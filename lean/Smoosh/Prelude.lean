import Smoosh.Compat.PervasivesExtra
import Smoosh.BuildInfo
import Smoosh.Platform.SignalPlatform
import Smoosh.Num

universe u

namespace Smoosh

variable {α β : Type u}

/-
(**********************************************************************)
(* UTILITY FUNCTIONS **************************************************)
(**********************************************************************)
-/

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

/-
(**********************************************************************)
(* LOCALES ************************************************************)
(**********************************************************************)
-/

/-- Lem: ord -/
def ord (c : Char) : Nat := c.toNat

/-- Lem: between -/
def between (lo c hi : Nat) : Bool :=
  (lo ≤ c) && (c ≤ hi)

/-===============================================================
  Locale / char class
===============================================================-/

inductive RangeChar where
  | rchar      (c : Char)
  | rcollating (s : String)
  deriving DecidableEq, Repr

structure Locale where
  name      : String
  collates  : Char → String → Bool
  equiv     : Char → String → Bool
  charclass : Char → String → Bool
  range     : Char → RangeChar → RangeChar → Bool

/-- Lem: ambient_charclass (non-recursive in Lean) -/
def ambient_charclass (c : Char) (cls : String) : Bool :=
  let isAlpha : Bool :=
    between (ord 'A') (ord c) (ord 'Z') || between (ord 'a') (ord c) (ord 'z')
  let isDigit : Bool :=
    (toCharList "0123456789").contains c
  let isUpper : Bool :=
    between (ord 'A') (ord c) (ord 'Z')
  let isLower : Bool :=
    between (ord 'a') (ord c) (ord 'z')
  let isBlank : Bool :=
    (toCharList " \t").contains c
  let isCntrl : Bool :=
    (ord c < ord ' ') || (ord c = 127)   -- del
  let isPunct : Bool :=
    (toCharList "!\"#$%&'()*+,-./:;<=>?@[\\]^_{}~|").contains c
      || ord c = 200  -- grave accent (as in Lem comment)
  let isSpace : Bool :=
    (toCharList " \t\n\r").contains c || ord c = 11 || ord c = 14 -- VT / FF
  let isXDigit : Bool :=
    (toCharList "0123456789ABCDEFabcdef").contains c
  match cls with
  | "alnum"  => isAlpha || isDigit
  | "alpha"  => isUpper || isLower
  | "blank"  => isBlank
  | "cntrl"  => isCntrl
  | "digit"  => isDigit
  | "graph"  => (isAlpha || isDigit) || isPunct
  | "lower"  => isLower
  | "print"  => ((isAlpha || isDigit) || isPunct) || c = ' '
  | "punct"  => isPunct
  | "space"  => isSpace
  | "upper"  => isUpper
  | "xdigit" => isXDigit
  | _        => false

/-- Lem: lc_ambient -/
def lc_ambient : Locale :=
  let collates : Char → String → Bool :=
    fun c cls => (toCharList cls).contains c      -- stub
  let equiv : Char → String → Bool :=
    fun c cls => (toCharList cls).contains c      -- stub

  let rchar : RangeChar → Option Char
    | .rchar c       => some c
    | .rcollating s  =>
        match toCharList s with
        | [c] => some c
        | _   => none

  let range : Char → RangeChar → RangeChar → Bool :=
    fun c rlo rhi =>
      match rchar rlo, rchar rhi with
      | some lo, some hi => between (ord lo) (ord c) (ord hi)
      | _, _             => false

  { name := "ambient"
  , collates := collates
  , equiv := equiv
  , charclass := ambient_charclass
  , range := range
  }

/-===============================================================
  File permissions
===============================================================-/

/-- Lem: type file_perm = Read | Write | Execute -/
inductive FilePerm where
  | Read | Write | Execute
  deriving DecidableEq, Repr

/-- A tiny “set” of permissions: just three booleans. -/
structure PermSet where
  r : Bool := false
  w : Bool := false
  x : Bool := false
  deriving Repr, DecidableEq

namespace PermSet

def empty : PermSet := {}

def singleton : FilePerm → PermSet
  | .Read    => { r := true }
  | .Write   => { w := true }
  | .Execute => { x := true }

def mem (p : FilePerm) (s : PermSet) : Bool :=
  match p with
  | .Read    => s.r
  | .Write   => s.w
  | .Execute => s.x

def union (a b : PermSet) : PermSet :=
  { r := a.r || b.r, w := a.w || b.w, x := a.x || b.x }

def diff (a b : PermSet) : PermSet :=
  { r := a.r && (!b.r), w := a.w && (!b.w), x := a.x && (!b.x) }

def fromList (ps : List FilePerm) : PermSet :=
  ps.foldl (fun acc p => union acc (singleton p)) empty

end PermSet

-- Compatibility layer: mimic Lem’s `Set.*` calls (only what we need).
namespace Set
abbrev Set := PermSet
def empty : Set := PermSet.empty
def singleton (p : FilePerm) : Set := PermSet.singleton p
def fromList (ps : List FilePerm) : Set := PermSet.fromList ps
def difference (a b : Set) : Set := PermSet.diff a b
end Set

/-- Lem: type perms = <| ... user: set file_perm; ... |>
    We keep the same shape. -/
structure Perms where
  setuid : Bool := false
  setgid : Bool := false
  sticky : Bool := false
  user   : Set.Set := Set.empty
  group  : Set.Set := Set.empty
  other  : Set.Set := Set.empty
  deriving Repr, DecidableEq

def permsAllClear : Perms := {}

def allFilePerms : Set.Set :=
  PermSet.fromList [FilePerm.Read, FilePerm.Write, FilePerm.Execute]

def defaultUmask : Perms :=
  { setuid := false, setgid := false, sticky := false
  , user  := Set.empty
  , group := Set.singleton FilePerm.Write
  , other := Set.singleton FilePerm.Write
  }

def invertFilePerms (s : Set.Set) : Set.Set :=
  Set.difference allFilePerms s

def invertPerms (p : Perms) : Perms :=
  { setuid := !p.setuid
  , setgid := !p.setgid
  , sticky := !p.sticky
  , user   := invertFilePerms p.user
  , group  := invertFilePerms p.group
  , other  := invertFilePerms p.other
  }

/-
(**********************************************************************)
(* Basic parsing and rendering of perms *******************************)
(**********************************************************************)
-/

/-- Lem: has_bit n k -/
def has_bit (n k : Nat) : Bool :=
  Nat.testBit n k

/-- Lem: stringFromNat -/
def stringFromNat (n : Nat) : String :=
  s!"{n}"

-- Extend compatibility layer: Set.member / Set.union
namespace Set
def member (p : FilePerm) (s : Set) : Bool :=
  PermSet.mem p s

def union (a b : Set) : Set :=
  PermSet.union a b
end Set

/-- Lem: nat_of_file_perms : set file_perm -> nat
    Execute=1, Write=2, Read=4 (same as Lem) -/
def nat_of_file_perms (fperms : Set.Set) : Nat :=
  let bit0 := if Set.member FilePerm.Execute fperms then 1 else 0
  let bit1 := if Set.member FilePerm.Write   fperms then 2 else 0
  let bit2 := if Set.member FilePerm.Read    fperms then 4 else 0
  bit0 + bit1 + bit2

/-- Lem: file_perms_of_nat : nat -> set file_perm
    bit0->Execute, bit1->Write, bit2->Read (same as Lem) -/
def file_perms_of_nat (n : Nat) : Set.Set :=
  let r := if has_bit n 0 then Set.singleton FilePerm.Execute else Set.empty
  let w := if has_bit n 1 then Set.singleton FilePerm.Write   else Set.empty
  let x := if has_bit n 2 then Set.singleton FilePerm.Read    else Set.empty
  Set.union r (Set.union w x)

/-- Lem: perms_of_nat : nat -> perms -/
def perms_of_nat (n : Nat) : Perms :=
  { other  := file_perms_of_nat n
  , group  := file_perms_of_nat (n / 8)
  , user   := file_perms_of_nat (n / 64)
  , sticky := has_bit n 9
  , setgid := has_bit n 10
  , setuid := has_bit n 11
  }

/-- Lem: nat_of_perms : perms -> nat -/
def nat_of_perms (p : Perms) : Nat :=
  let bit0 := if p.sticky then 1 else 0
  let bit1 := if p.setgid then 2 else 0
  let bit2 := if p.setuid then 4 else 0
  let first  := bit0 + bit1 + bit2
  let second := nat_of_file_perms p.user
  let third  := nat_of_file_perms p.group
  let fourth := nat_of_file_perms p.other
  (Nat.pow 2 9) * first + (Nat.pow 2 6) * second + (Nat.pow 2 3) * third + fourth

/-- Lem: octal_string_of_perms : perms -> string -/
def octal_string_of_perms (p : Perms) : String :=
  let bit0 := if p.sticky then 1 else 0
  let bit1 := if p.setgid then 2 else 0
  let bit2 := if p.setuid then 4 else 0
  let first  := stringFromNat (bit0 + bit1 + bit2)
  let second := stringFromNat (nat_of_file_perms p.user)
  let third  := stringFromNat (nat_of_file_perms p.group)
  let fourth := stringFromNat (nat_of_file_perms p.other)
  first ++ second ++ third ++ fourth

/-- Lem: string_of_file_perms : set file_perm -> string -/
def string_of_file_perms (fperms : Set.Set) : String :=
  let r := if Set.member FilePerm.Read    fperms then "r" else ""
  let w := if Set.member FilePerm.Write   fperms then "w" else ""
  let x := if Set.member FilePerm.Execute fperms then "x" else ""
  r ++ w ++ x

/-- Lem: string_of_perms : perms -> string -/
def string_of_perms (p : Perms) : String :=
  let u := string_of_file_perms p.user
  let g := string_of_file_perms p.group
  let o := string_of_file_perms p.other
  "u=" ++ u ++ "," ++
  "g=" ++ g ++ "," ++
  "o=" ++ o




end Smoosh
