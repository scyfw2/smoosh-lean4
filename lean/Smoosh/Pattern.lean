import Smoosh.Smoosh

open Smoosh
namespace Smoosh
def charToString (c : Char) : String := String.singleton c
def charListToString (cs : List Char) : String := String.ofList cs

/-- Lem: match_result type -/
inductive match_result (α : Type u) where
  | noMatch  : match_result α
  | symbolic : match_result α
  | Match   : α → match_result α
deriving Repr, Inhabited

/-- Lem: bracket_char type -/
inductive bracket_char where
  | char      : Char → bracket_char
  | collating : String → bracket_char
  | equiv     : String → bracket_char
  | class_    : String → bracket_char
deriving Repr

/-- Lem: bracket_entry type -/
inductive  bracket_entry where
  | bc    : bracket_char →  bracket_entry
  | range : range_char → range_char →  bracket_entry
deriving Repr

/-- Lem: pattern_char type -/
inductive pattern_char where
  | lit     : Char → pattern_char
  | bracket : Bool → List  bracket_entry → pattern_char   -- matching? * entries
  | qmark   : pattern_char
  | star    : pattern_char
deriving Repr

/-- Lem: pattern type -/
abbrev pattern := List pattern_char

mutual
  def string_of_range_char (rc : range_char) : String :=
    match rc with
    | .rchar c      => charToString c
    | .rcollating s => string_of_bracket_char (.collating s)

  def string_of_bracket_char (bc : bracket_char) : String :=
    match bc with
    | .char c      => charToString c
    | .collating s => "[." ++ s ++ ".]"
    | .equiv s     => "[=" ++ s ++ "=]"
    | .class_ s    => "[:" ++ s ++ ":]"

  def string_of_bracket_entry (be : bracket_entry) : String :=
    match be with
    | .bc bc         => string_of_bracket_char bc
    | .range lo hi   => string_of_range_char lo ++ "-" ++ string_of_range_char hi

  def string_of_pattern_char (pc : pattern_char) : String :=
    match pc with
    | .lit '\\' => "\\\\"
    | .lit '?'  => "\\?"
    | .lit '*'  => "\\?"
    | .lit '['  => "\\["
    | .lit c    => charToString c
    | .bracket shouldMatch es =>
        "[" ++ (if shouldMatch then "" else "!") ++
          String.intercalate "" (List.map string_of_bracket_entry es) ++
        "]"
    | .qmark => "?"
    | .star  => "*"

  def string_of_pattern (p : pattern) : String :=
    String.intercalate "" (List.map string_of_pattern_char p)
end

def parse_bracket_terminator
    (pat : List Char) (term : Char)
    : Except String (List Char × List Char) :=
  match pat with
  | [] =>
      .error "expected bracket terminator, found end-of-pattern"
  | c :: ']' :: pat' =>
      if c = term then
        .ok (pat', [])
      else
        .error ("mismatched bracket terminator: got " ++
          charToString c ++ ", expected " ++ charToString term)
  | c :: pat' =>
      match parse_bracket_terminator pat' term with
      | .error err => .error err
      | .ok (pat'', cs) => .ok (pat'', c :: cs)

def parse_bracket_class
    (pat : List Char) (term : Char)
    : Except String (List Char × String) :=
  match parse_bracket_terminator pat term with
  | .error err => .error err
  | .ok (pat', cls) => .ok (pat', charListToString cls)

/-- POSIX bracket char parsing -/
def parse_bracket_char
    (pat : List Char)
    : Except String (List Char × bracket_char) :=
  match pat with
  | [] =>
      .error "expected bracket character, found end-of-pattern"
  | '[' :: '.' :: pat' =>
      match parse_bracket_class pat' '.' with
      | .error err => .error err
      | .ok (pat'', cls) => .ok (pat'', .collating cls)
  | '[' :: '=' :: pat' =>
      match parse_bracket_class pat' '=' with
      | .error err => .error err
      | .ok (pat'', cls) => .ok (pat'', .equiv cls)
  | '[' :: ':' :: pat' =>
      match parse_bracket_class pat' ':' with
      | .error err => .error err
      | .ok (pat'', cls) => .ok (pat'', .class_ cls)
  | c :: pat' =>
      .ok (pat', .char c)

def range_bc (bc : bracket_char) : Option range_char :=
  match bc with
  | .char c        => some (.rchar c)
  | .collating cls => some (.rcollating cls)
  | .equiv _       => none  -- TODO implement
  | .class_ _      => none  -- TODO implement

def parse_bracket_quoted_entries
    (pat : List Char)
    : Except String (List Char × List bracket_entry) :=
  match pat with
  | [] => .error "expected end quote"
  | '"' :: pat' => .ok (pat', [])
  | c :: pat' =>
      match parse_bracket_quoted_entries pat' with
      | .error err => .error err
      | .ok (pat'', es) => .ok (pat'', .bc (.char c) :: es)

partial def parse_bracket_entries
    (pat : List Char)
    : Except String (List Char × List bracket_entry) :=
  match pat with
  | [] => .error "expected bracket entries, found end-of-pattern"
  | ']' :: pat' => .ok (pat', [])
  | '-' :: ']' :: pat' => .ok (pat', [.bc (.char '-')])
  | '"' :: pat' =>
      match parse_bracket_quoted_entries pat' with
      | .error _err =>
          -- treat it as a normal quote
          match parse_bracket_entries pat' with
          | .error err => .error err
          | .ok (pat'', es) => .ok (pat'', .bc (.char '"') :: es)
      | .ok (pat'', es) =>
          match parse_bracket_entries pat'' with
          | .error err => .error err
          | .ok (pat''', es') => .ok (pat''', es ++ es')
  | _ =>
      match parse_bracket_char pat with
      | .error err => .error err
      | .ok (('-' :: ']' :: pat'), bc) =>
          -- '-' as final char is a literal
          .ok (pat', [.bc (.char '-'), .bc bc])
      | .ok (('-' :: pat'), bc) =>
          match parse_bracket_char pat' with
          | .error _ =>
              match parse_bracket_entries ('-' :: pat') with
              | .error err => .error err
              | .ok (pat'', es) => .ok (pat'', .bc bc :: es)
          | .ok (pat'', bc') =>
              match (range_bc bc, range_bc bc', parse_bracket_entries pat'') with
              | (some lo, some hi, .ok (pat''', es)) =>
                  .ok (pat''', .range lo hi :: es)
              | (none, _, _) =>
                  .error ("invalid range character: " ++ string_of_bracket_char bc)
              | (_, none, _) =>
                  .error ("invalid range character: " ++ string_of_bracket_char bc')
              | (_, _, .error err) => .error err
      | .ok (pat', bc) =>
          match parse_bracket_entries pat' with
          | .error err => .error err
          | .ok (pat'', es) => .ok (pat'', .bc bc :: es)

def bracket_initial_literal (c : Char) : Bool :=
  c = ']' || c = '-'

def parse_bracket
    (pat : List Char)
    : Except String (List Char × pattern_char) :=
  match pat with
  | [] => .error "unterminated bracket, found end-of-pattern"
  | c :: pat' =>
      let (matching, pat'') :=
        if c = '!' then (false, pat') else (true, pat)
      match pat'' with
      | [] => .error "unterminated bracket, found end-of-pattern"
      | ']' :: [] => .error "empty bracket, treating as literal characters"
      | c0 :: pat''' =>
          let (realPat, frontEs) :=
            if bracket_initial_literal c0 then (pat''', [.bc (.char c0)]) else (pat'', [])
          match parse_bracket_entries realPat with
          | .error err => .error err
          | .ok (restPat, es) => .ok (restPat, .bracket matching (frontEs ++ es))

mutual
  partial def parse_quoted_pattern
      (pat : List Char)
      : Except String (List Char × pattern) :=
    let recur (pat' : List Char) (pcs1 : pattern) :=
      match parse_quoted_pattern pat' with
      | .error err => .error err
      | .ok (pat'', pcs2) => .ok (pat'', pcs1 ++ pcs2)
    match pat with
    | [] => .error "unterminated quote"
    | '"' :: pat' => .ok (pat', [])
    | '\\' :: c :: pat' => recur pat' [.lit c]
    | c :: pat' => recur pat' [.lit c]

  partial def parse_pattern_char
      (pat : List Char)
      : Except String (List Char × pattern) :=
    match pat with
    | [] => .error "expected pattern char, got end-of-pattern"
    | '*' :: pat' => .ok (pat', [.star])
    | '?' :: pat' => .ok (pat', [.qmark])
    | '[' :: pat' =>
        match parse_bracket pat' with
        | .error _ => .ok (pat', [.lit '['])
        | .ok (pat'', pc) => .ok (pat'', [pc])
    | '"' :: pat' => parse_quoted_pattern pat'
    | '\\' :: [] => .error "unescaped backslash at end-of-pattern"
    | '\\' :: c :: pat' => .ok (pat', [.lit c])
    | c :: pat' => .ok (pat', [.lit c])
end

partial def parse_pattern_loop
    (pat : List Char)
    : Except String (List Char × pattern) :=
  match pat with
  | [] => .ok ([], [])
  | _ =>
      match parse_pattern_char pat with
      | .error err => .error err
      | .ok (pat', pcs1) =>
          match parse_pattern_loop pat' with
          | .error err => .error err
          | .ok (pat'', pcs2) => .ok (pat'', pcs1 ++ pcs2)

def parse_pattern (pat : List Char) : Except String pattern :=
  match parse_pattern_loop pat with
  | .error err => .error err
  | .ok ([], ptn) => .ok ptn
  | .ok (pat', _) =>
      .error ("unexpected unparsed pattern in '" ++ charListToString pat' ++ "'")

def match_entry (lc : locale) (c : Char) (be : bracket_entry) : Bool :=
  match be with
  | .bc (.char c')       => c' = c
  | .bc (.collating cls) => lc.collates c cls
  | .bc (.equiv cls)     => lc.equiv c cls
  | .bc (.class_ cls)    => lc.charclass c cls
  | .range lo hi         => lc.range c lo hi

-- Does an EXACT pattern match.
partial def match_exact_pattern
    (lc : locale) (pat : pattern) (s : symbolic_string)
    : match_result symbolic_string :=
  match (pat, s) with
  -- empty pattern
  | ([], []) => .Match []
  | ([], _)  => .noMatch

  -- question-mark
  | (.qmark :: _, []) => .noMatch
  | (.qmark :: pat', _ :: s') => match_exact_pattern lc pat' s'

  -- star
  | (.star :: pat', []) => match_exact_pattern lc pat' []
  | (.star :: pat', c :: s') =>
      match match_exact_pattern lc pat' (c :: s') with
      | .noMatch   => match_exact_pattern lc (.star :: pat') s'
      | .symbolic  => .symbolic
      | .Match s'' => .Match s''

  -- bracket
  | (.bracket _ _ :: _, []) => .noMatch
  | (.bracket _ _ :: _, .Sym _ :: _) => .symbolic
  | (.bracket shouldMatch cs :: pat', .C c :: s') =>
      if shouldMatch = (cs.any (match_entry lc c)) then
        match_exact_pattern lc pat' s'
      else
        .noMatch

  -- plain characters
  | (_ :: _, []) => .noMatch
  | (.lit c1 :: pat', .C c2 :: s') =>
      if c1 = c2 then match_exact_pattern lc pat' s' else .noMatch

  -- symbolic catch-all
  | (_, .Sym _ :: _) => .symbolic

def match_exact
    (lc : locale) (ss_pat : symbolic_string) (s : symbolic_string)
    : match_result symbolic_string :=
  match try_concrete ss_pat with
  | none => .symbolic
  | some s_pat =>
      match parse_pattern (toCharList s_pat) with
      | .error _err => .noMatch
      | .ok pat => match_exact_pattern lc pat s

def try_match_substring_loop
    (lc : locale) (side : substring_side) (sizes : List Nat)
    (pat : pattern) (str : symbolic_string)
    : match_result symbolic_string :=
  match sizes with
  | [] => .noMatch
  | size :: sizes' =>
      let (first, rest) := str.splitAt size
      let (substr, keep) :=
        match side with
        | .Prefix => (first, rest)
        | .Suffix => (rest, first)
      match match_exact_pattern lc pat substr with
      | .noMatch  => try_match_substring_loop lc side sizes' pat str
      | .symbolic => .symbolic
      | .Match _ => .Match keep

def try_match_substring
    (lc : locale) (side : substring_side) (mode : substring_mode)
    (pat : String) (str : symbolic_string)
    : symbolic_string :=
  match parse_pattern (toCharList pat) with
  | .error _err => str
  | .ok ptn =>
      let sizes := List.range (List.length str + 1)
      let ordered_sizes :=
        match (mode, side) with
        | (.Shortest, .Prefix) => sizes
        | (.Longest,  .Suffix) => sizes
        | (.Longest,  .Prefix) => List.reverse sizes
        | (.Shortest, .Suffix) => List.reverse sizes
      match try_match_substring_loop lc side ordered_sizes ptn str with
      | .noMatch => str
      | .symbolic =>
          [.Sym (.SymPat side mode (symbolic_string_of_string pat) str)]
      | .Match str' => str'

end Smoosh
