import Smoosh.Compat.PervasivesExtra
import Smoosh.BuildInfo
import Smoosh.Platform.SignalPlatform
import Smoosh.Num
import Smoosh.Prelude.FilePerm
import Smoosh.Prelude.Locales
import Smoosh.Prelude.Utility

namespace Smoosh
open Smoosh

/-- Lem: has_bit n k -/
def has_bit (n k : Nat) : Bool :=
  Nat.testBit n k

/-- Lem: stringFromNat -/
def stringFromNat (n : Nat) : String :=
  s!"{n}"

/-- Lem: nat_of_file_perms : set file_perm -> nat -/
def nat_of_file_perms (fperms : Set.Set file_perm) : Nat :=
  let bit0 := if Set.Set.member .Execute fperms then 1 else 0
  let bit1 := if Set.Set.member .Write   fperms then 2 else 0
  let bit2 := if Set.Set.member .Read    fperms then 4 else 0
  bit0 + bit1 + bit2

/-- Lem: file_perms_of_nat : nat -> set file_perm -/
def file_perms_of_nat (n : Nat) : Set.Set file_perm :=
  let r := if has_bit n 0 then .singleton .Execute else .empty
  let w := if has_bit n 1 then .singleton .Write   else .empty
  let x := if has_bit n 2 then .singleton .Read    else .empty
  .union r (.union w x)

/-- Lem: perms_of_nat : nat -> perms -/
def perms_of_nat (n : Nat) : perms :=
  { other  := file_perms_of_nat n
  , group  := file_perms_of_nat (n / 8)
  , user   := file_perms_of_nat (n / 64)
  , sticky := has_bit n 9
  , setgid := has_bit n 10
  , setuid := has_bit n 11
  }

/-- Lem: nat_of_perms : perms -> nat -/
def nat_of_perms (p : perms) : Nat :=
  let bit0 := if p.sticky then 1 else 0
  let bit1 := if p.setgid then 2 else 0
  let bit2 := if p.setuid then 4 else 0
  let first  := bit0 + bit1 + bit2
  let second := nat_of_file_perms p.user
  let third  := nat_of_file_perms p.group
  let fourth := nat_of_file_perms p.other
  (Nat.pow 2 9) * first + (Nat.pow 2 6) * second + (Nat.pow 2 3) * third + fourth

/-- Lem: octal_string_of_perms : perms -> string -/
def octal_string_of_perms (p : perms) : String :=
  let bit0 := if p.sticky then 1 else 0
  let bit1 := if p.setgid then 2 else 0
  let bit2 := if p.setuid then 4 else 0
  let first  := stringFromNat (bit0 + bit1 + bit2)
  let second := stringFromNat (nat_of_file_perms p.user)
  let third  := stringFromNat (nat_of_file_perms p.group)
  let fourth := stringFromNat (nat_of_file_perms p.other)
  first ++ second ++ third ++ fourth

/-- Lem: string_of_file_perms : set file_perm -> string -/
def string_of_file_perms (fperms : Set.Set file_perm) : String :=
  let r := if Set.Set.member .Read    fperms then "r" else ""
  let w := if Set.Set.member .Write   fperms then "w" else ""
  let x := if Set.Set.member .Execute fperms then "x" else ""
  r ++ w ++ x

/-- Lem: string_of_perms : perms -> string -/
def string_of_perms (p : perms) : String :=
  let u := string_of_file_perms p.user
  let g := string_of_file_perms p.group
  let o := string_of_file_perms p.other
  "u=" ++ u ++ "," ++
  "g=" ++ g ++ "," ++
  "o=" ++ o

end Smoosh
