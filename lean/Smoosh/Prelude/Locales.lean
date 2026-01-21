import Smoosh.Compat.PervasivesExtra
import Smoosh.BuildInfo
import Smoosh.Platform.SignalPlatform
import Smoosh.Num
import Smoosh.Prelude.Utility

namespace Smoosh

/-- Lem: ord -/
def ord (c : Char) : Nat := c.toNat

/-- Lem: between -/
def between (lo c hi : Nat) : Bool :=
  (lo ≤ c) && (c ≤ hi)

/-- Lem: range_char type -/
inductive range_char where
  | rchar      (c : Char)
  | rcollating (s : String)
  deriving DecidableEq, Repr

/-- Lem: locale type -/
structure locale where
  name      : String
  collates  : Char → String → Bool
  equiv     : Char → String → Bool
  charclass : Char → String → Bool
  range     : Char → range_char → range_char → Bool

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
def lc_ambient : locale :=
  let collates : Char → String → Bool :=
    fun c cls => (toCharList cls).contains c      -- stub
  let equiv : Char → String → Bool :=
    fun c cls => (toCharList cls).contains c      -- stub

  let rchar : range_char → Option Char
    | .rchar c       => some c
    | .rcollating s  =>
        match toCharList s with
        | [c] => some c
        | _   => none

  let range : Char → range_char → range_char → Bool :=
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

end Smoosh
