import Smoosh.Smoosh
import Smoosh.Path

open Smoosh

/-
 * Stage 2 Expansion: Field Splitting
 -/

def is_ws (c : Char) : Bool :=
  List.elem c (toCharList " \n\t")

def collect_non_ifs (ifs : List Char) (ls : List Char) : (List Char) × (List Char) :=
  match ls with
  | [] => ([], [])
  | c :: cs =>
      if List.elem c ifs then
        ([], c :: cs)
      else
        let (f, remaining) := collect_non_ifs ifs cs
        (c :: f, remaining)

partial def split_expstring (ifs : List Char) (clst : List Char) : intermediate_fields :=
  match clst with
  | [] => []
  | c :: cs =>
      if List.elem c ifs then
        (if is_ws c then .WFS else .FS) :: split_expstring ifs cs
      else
        let (cc, cs1) := collect_non_ifs ifs cs
        (.Field (symbolic_string_of_char_list (c :: cc))) :: split_expstring ifs cs1

partial def split_word (ifs : List Char) (p : intermediate_fields × expanded_words) : intermediate_fields :=
  match p with
  | (f, []) => f
  | (f, .UsrF :: .UsrF :: wrds) =>
      split_word ifs (f, .UsrF :: wrds)
  | (f, .UsrF :: wrds) =>
      split_word ifs (f ++ [.FS], wrds)
  | (f, .ExpS s :: wrds) =>
      let new_fields := split_expstring ifs (toCharList s)
      split_word ifs (f ++ new_fields, wrds)
  | (f, .UsrS s :: wrds) =>
      split_word ifs (f ++ [.Field (symbolic_string_of_string s)], wrds)
  | (f, .At fs :: wrds) =>
      split_word ifs (f ++ (List.map .Field fs), wrds)
  | (f, .DQuo ss :: wrds) =>
      split_word ifs (f ++ [.QField ss], wrds)
  | (f, .EWSym sym :: wrds) =>
      split_word ifs (f ++ [.Field [.Sym sym]], wrds)

def concat_expanded (w : expanded_words) : Except String symbolic_string :=
  match w with
  | [] => .ok (symbolic_string_of_string "")
  | .UsrF :: ws => do
      let rest ← concat_expanded ws
      pure (symbolic_string_of_string " " ++ rest)
  | .ExpS s :: ws => do
      let rest ← concat_expanded ws
      pure (symbolic_string_of_string s ++ rest)
  | .DQuo ss :: ws => do
      -- quotes are not included
      let rest ← concat_expanded ws
      pure (ss ++ rest)
  | .At fs :: ws => do
      -- collapse the result of $@ expansion, too
      let rest ← concat_expanded ws
      pure (symbolic_string_of_fields fs ++ rest)
  | .EWSym sym :: ws => do
      let rest ← concat_expanded ws
      pure (.Sym sym :: rest)
  | .UsrS _ :: _ =>
      .error "broken invariant in concat_expanded: no UsrS should be found"


def collapse_quoted (w : expanded_words) : Except String expanded_words := do
  let is_at : expanded_word → Bool
    | .At _ => true
    | _     => false

  match breakBy is_at w with
  | (w', []) =>
      -- no At anywhere, just collapse it
      let ss ← concat_expanded w'
      pure [.DQuo ss]

  | (pre_w, .At fs :: post_w) =>
      -- attach pre_w to the first one, post_w to the last one
      pure (pre_w ++ intersperse .UsrF (List.map .DQuo fs) ++ post_w)

  | _ =>
      .error "broken invariant in collapse_quoted: couldn't find At anywhere, but got weird output"

def skip_field_splitting (w : expanded_words) : intermediate_fields :=
  match w with
  | [] => []
  -- properly handle null fields that might have been generated
  | .UsrF :: .UsrF :: ws =>
      skip_field_splitting (.UsrF :: ws)
  | .UsrF :: ws =>
      .FS :: skip_field_splitting ws
  | .UsrS s :: ws =>
      .Field (symbolic_string_of_string s) :: skip_field_splitting ws
  | .ExpS s :: ws =>
      .Field (symbolic_string_of_string s) :: skip_field_splitting ws
  | .DQuo s :: ws =>
      .QField s :: skip_field_splitting ws
  | .At fs :: ws =>
      intersperse .FS (List.map .QField fs) ++ skip_field_splitting ws
  | .EWSym sym :: ws =>
      .Field [.Sym sym] :: skip_field_splitting ws

def split_fields {α : Type u} [OS α] (s0 : os_state α) (exp_words : expanded_words) : Except String intermediate_fields :=
  let ifs := lookup_string_param s0 "IFS"
  match ifs with
  | .ok none =>
      .ok (split_word (toCharList " \n\t") ([], exp_words))
  | .ok (some fs) =>
      match try_concrete fs with
      | none =>
          -- unsoundly using default IFS
          .ok (split_word (toCharList " \n\t") ([], exp_words))
      | some "" =>
          -- If IFS is null, no field splitting shall be performed.
          .ok (skip_field_splitting exp_words)
      | some s =>
          .ok (split_word (toCharList s) ([], exp_words))
  | .error msg => .error msg

partial def combine_fields (f : intermediate_fields) : intermediate_fields :=
  match f with
  | [] => []
  | [.WFS] => [] -- Remove trailing field separators
  | .WFS :: .WFS :: rst =>
      combine_fields (.WFS :: rst) -- Combine adjacent whitespace separators
  | .WFS :: .FS :: rst =>
      combine_fields (.FS :: rst)
  | .FS :: .WFS :: rst =>
      combine_fields (.FS :: rst)
  | .Field s1 :: .Field s2 :: rst =>
      combine_fields (.Field (s1 ++ s2) :: rst)
  | .QField s1 :: .QField s2 :: rst =>
      combine_fields (.QField (s1 ++ s2) :: rst)
  | .QField s1 :: .Field s2 :: rst =>
      combine_fields (.Field (escape_patterns s1 ++ s2) :: rst)
  | .Field s1 :: .QField s2 :: rst =>
      combine_fields (.Field (s1 ++ escape_patterns s2) :: rst)
  | .WFS :: rst =>
      .FS :: combine_fields rst
  | x :: rst =>
      x :: combine_fields rst

def clean_fields (f : intermediate_fields) : intermediate_fields :=
  match f with
  | .WFS :: rst => clean_fields rst
  | _ => combine_fields f

def debug_tmp_field (tf : tmp_field) : String :=
  match tf with
  | .WFS => "WFS"
  | .FS => "FS"
  | .Field s => "Field(" ++ string_of_symbolic_string s ++ ")"
  | .QField s => "QField(" ++ string_of_symbolic_string s ++ ")"

def field_splitting {α : Type u} [OS α]
    (s0 : os_state α) (w : expanded_words) : Except String intermediate_fields := do
  let fs ← split_fields s0 w
  pure (clean_fields fs)

/-
 * Stage 3 Expansion: Pathname expansion
 -/

def insert_field_separators (fs : List String) : intermediate_fields :=
  match fs with
  | [] => []
  | [f] => [.Field (symbolic_string_of_string f)]
  | f :: fs' =>
      .Field (symbolic_string_of_string f) :: .FS :: insert_field_separators fs'

def needs_expansion (ss : symbolic_string) : Bool :=
  match ss with
  | [] => false
  | .C '[' :: [] => false  -- kludge for a bare [
  | .C '?' :: _ => true
  | .C '*' :: _ => true
  | .C '[' :: _ => true
  | _ :: ss' => needs_expansion ss'

def pathname_expansion {α : Type u} [OS α]
    (s0 : os_state α) (f : intermediate_fields) : intermediate_fields :=
  match f with
  | [] => []
  | .Field s :: rst =>
      let matchs :=
        if needs_expansion s then
          match try_concrete s with
          | some pat => match_path s0 pat
          | none => []  -- slightly inaccurate: not modeling symbolic pathname expansions
        else
          []
      let expansions :=
        if matchs.isEmpty then
          [.Field (unescape_pattern s)]
        else
          insert_field_separators matchs
      expansions ++ pathname_expansion s0 rst
  | x :: rst => x :: pathname_expansion s0 rst

/-
 * Stage 4 Expansion: Quote Removal
 -/

def remove_quotes (f : intermediate_fields) : intermediate_fields :=
  match f with
  | [] => []
  | .QField s :: rst => .Field s :: remove_quotes rst
  | x :: rst => x :: remove_quotes rst

def to_fields (f : intermediate_fields) : Except String fields :=
  match f with
  | [] => .ok []
  | .Field fs :: rst =>
      match to_fields rst with
      | .ok out      => .ok (fs :: out)
      | .error err   => .error err
  | .FS :: .FS :: rst =>
      -- keep the Lem behaviour: FS FS ⇒ insert empty field, then continue with (FS :: rst)
      match to_fields (.FS :: rst) with
      | .ok out    => .ok (symbolic_string_of_string "" :: out)
      | .error err => .error err
  | .FS :: rst =>
      to_fields rst
  | .WFS :: _ =>
      .error "broken invariant in to_fields: didn't expect WFS"
  | .QField _ :: _ =>
      .error "broken invariant in to_fields: didn't expect QField"

def finalize_fields (f : intermediate_fields) : Except String fields :=
  match f with
  | .FS :: rst => do
      let out ← finalize_fields rst
      pure (symbolic_string_of_string "" :: out)
  | _ =>
      to_fields f

def quote_removal (f : intermediate_fields) : Except String fields := do
  let no_quotes := combine_fields (remove_quotes f)
  finalize_fields no_quotes
