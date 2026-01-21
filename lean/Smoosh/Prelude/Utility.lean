import Smoosh.Compat.PervasivesExtra
import Smoosh.BuildInfo
import Smoosh.Platform.SignalPlatform
import Smoosh.Num

universe u

namespace Smoosh

variable {α β : Type u}

/-- Lem: toCharList -/
def toCharList (s : String) : List Char :=
  s.toList

/-- Lem: toString -/
def charsToString (cs : List Char) : String :=
  String.ofList cs

/-- Lem: uppercase_char -/
def uppercase_char (c : Char) : Char :=
  c.toUpper

/-- Lem: alphabetic -/
def alphabetic : List Char :=
  toCharList "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"

/-- Lem: alphanumerics -/
def alphanumerics : List Char :=
  toCharList "0123456789" ++ alphabetic

/-- Lem: is_alpha -/
def is_alpha (c : Char) : Bool :=
  alphabetic.contains c

/-- Lem: is_alphanumeric -/
def is_alphanumeric (c : Char) : Bool :=
  alphanumerics.contains c

/-- Lem: is_variable_initial_char -/
def is_variable_initial_char (c : Char) : Bool :=
  is_alpha c || c = '_'

/-- Lem: is_variable_char -/
def is_variable_char (c : Char) : Bool :=
  is_alphanumeric c || c = '_'

/-- Lem: uppercase -/
def uppercase (s : String) : String :=
  charsToString ((toCharList s).map uppercase_char)

/-- Lem: parens -/
def parens (s : String) : String :=
  "( " ++ s ++ " )"

/-- Lem: tails -/
def tails : List α → List (List α)
  | []      => [[]]
  | x :: xs => (x :: xs) :: tails xs

/-- Lem: compare_by_first -/
def compare_by_first [Ord α] : (α × β) → (α × β) → Ordering
  | (a, _), (a', _) => compare a a'

/-- Lem: insertBy -/
def insertBy (lte : α → α → Bool) (x : α) : List α → List α
  | []      => [x]
  | y :: ys => if lte x y then x :: y :: ys else y :: insertBy lte x ys

/-- Lem: sortBy -/
def sortBy (lte : α → α → Bool) (xs : List α) : List α :=
  xs.foldr (fun x acc => insertBy lte x acc) []

/-- A Bool-valued ≤ induced from Ord.compare -/
def ordLe [Ord α] (a b : α) : Bool :=
  match compare a b with
  | Ordering.gt => false
  | _           => true

/-- Lem: sort -/
def sort [Ord α] (xs : List α) : List α :=
  sortBy ordLe xs

/-- Lem: collect_either (either a b = Sum a b) -/
def collect_either : List (Sum α β) → (List α × List β)
  | [] => ([], [])
  | Sum.inl a :: xs =>
      let (ls, rs) := collect_either xs
      (a :: ls, rs)
  | Sum.inr b :: xs =>
      let (ls, rs) := collect_either xs
      (ls, b :: rs)

/-- Bool prefix check (Lem: isPrefixOf) -/
def isPrefixOf [DecidableEq α] : List α → List α → Bool
  | [],      _       => true
  | _ :: _,  []      => false
  | a :: as, b :: bs => if a = b then isPrefixOf as bs else false

/-- Lem: isInfixOf -/
def isInfixOf [DecidableEq α] (needle haystack : List α) : Bool :=
  (tails haystack).any (fun t => isPrefixOf needle t)

/-- Lem: replace (replace first occurrence) -/
def replace [DecidableEq α] (l_old l_new l_orig : List α) : List α :=
  if isPrefixOf l_old l_orig then
    l_new ++ l_orig.drop l_old.length
  else
    match l_orig with
    | []      => []
    | x :: xs => x :: replace l_old l_new xs

/-- Lem: replace_string -/
def replace_string (s_old s_new s_orig : String) : String :=
  charsToString (replace (toCharList s_old) (toCharList s_new) (toCharList s_orig))

/-- Lem: ltrim_newlines_cl -/
def ltrim_newlines_cl : List Char → List Char
  | []        => []
  | '\n' :: t => ltrim_newlines_cl t
  | xs        => xs

/-- Lem: intersperse -/
def intersperse (sep : α) : List α → List α
  | []        => []
  | [x]       => [x]
  | x :: xs   => x :: sep :: intersperse sep xs


def stringLength (s : String) : Nat := s.length

/-- Lem: trimr_one_newline -/
def trimr_one_newline (s : String) : String :=
  let cl := toCharList s
  match cl.reverse with
  | [] => ""
  | '\n' :: cl' => charsToString cl'.reverse
  | _ => s

/-- Lem: trimr_newlines -/
def trimr_newlines (s : String) : String :=
  let cl := toCharList s
  charsToString ((ltrim_newlines_cl cl.reverse).reverse)

/-- Lem: pad_left_with
padding = max (len - stringLength s) 0 (Lem)
The substraction for Nat in Lean stops at 0.
-/
def pad_left_with (c : Char) (s : String) (len : Nat) : String :=
  let padding := len - stringLength s
  charsToString (List.replicate padding c) ++ s

/-- Lem: pad_right_with -/
def pad_right_with (c : Char) (s : String) (len : Nat) : String :=
  let padding := len - stringLength s
  s ++ charsToString (List.replicate padding c)

/-- Lem: pad_left -/
def pad_left : String → Nat → String :=
  pad_left_with ' '

/-- Lem: pad_right -/
def pad_right : String → Nat → String :=
  pad_right_with ' '

/-- helper: max via Ord.compare -/
def maxOrd [Ord α] (a b : α) : α :=
  match compare a b with
  | Ordering.lt => b
  | _           => a

/-- Lem: maximum -/
def maximum [Ord α] [Inhabited α] : List α → α
  | []      => panic! "maximum got empty list"
  | [x]     => x
  | x :: xs => maxOrd x (maximum xs)

/-- Lem: break (predicate-matching element goes to the right part) -/
def breakBy (p : α → Bool) : List α → (List α × List α)
  | [] => ([], [])
  | x :: xs =>
      if p x then
        ([], x :: xs)
      else
        let (xs', xs'') := breakBy p xs
        (x :: xs', xs'')

/-- Lem: spaced -/
def spaced (s1 s2 : String) : String :=
  let sep := if s1 ≠ "" && s2 ≠ "" then " " else ""
  s1 ++ sep ++ s2

/-- Lem: spaced_many -/
def spaced_many : List String → String
  | []      => ""
  | [s]     => s
  | s :: ss => spaced s (spaced_many ss)

/-- Lem: break_on_esc -/
def break_on_esc (escapable : Bool) (sep : Char) : List Char → (List Char × List Char)
  | [] => ([], [])
  | '\\' :: c :: cs =>
      if escapable then
        let (cs', cs'') := break_on_esc escapable sep cs
        ('\\' :: c :: cs', cs'')
      else
        -- escapable=false falls through to normal handling of '\'
        if sep = '\\' then ([], c :: cs)
        else
          let (cs', cs'') := break_on_esc escapable sep (c :: cs)
          ('\\' :: cs', cs'')
  | c :: cs =>
      if sep = c then
        ([], cs)
      else
        let (cs', cs'') := break_on_esc escapable sep cs
        (c :: cs', cs'')

/-- Lem: split_on -/
def split_on (escapable : Bool) (sep : Char) (cs : List Char) : List (List Char) :=
  let rec go (cs : List Char) (curRev : List Char) (accRev : List (List Char)) : List (List Char) :=
    match cs with
    | [] =>
        -- Lem behavior: [] -> []; but trailing sep should yield final empty segment.
        if accRev.isEmpty && curRev.isEmpty then
          []
        else
          (curRev.reverse :: accRev).reverse
    | '\\' :: rest =>
        if escapable then
          match rest with
          | c :: rest' =>
              -- keep both '\' and c in the output (same order)
              go rest' (c :: '\\' :: curRev) accRev
          | [] =>
              -- lone '\' at end: treat as normal char
              go [] ('\\' :: curRev) accRev
        else
          -- not escapable: '\' is just a normal char
          go rest ('\\' :: curRev) accRev
    | c :: rest =>
        if c = sep then
          -- split: drop sep, commit current segment
          go rest [] (curRev.reverse :: accRev)
        else
          go rest (c :: curRev) accRev
  go cs [] []

/-- Lem: split_string_on -/
def split_string_on (escapable : Bool) (sep : Char) (s : String) : List String :=
  (split_on escapable sep (toCharList s)).map charsToString

/-- Lem: adjust_nth -/
def adjust_nth (l : List α) (n : Nat) (f : α → (α × β)) : Option (List α × β) :=
  match l, n with
  | [], _ => none
  | v :: l', 0 =>
      let (v', res) := f v
      some (v' :: l', res)
  | v :: l', Nat.succ n' =>
      match adjust_nth l' n' f with
      | none => none
      | some (l'', res) => some (v :: l'', res)

end Smoosh
