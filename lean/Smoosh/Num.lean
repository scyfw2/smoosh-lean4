namespace Smoosh.Num
/-
  --------------------------------
  Nat class
  --------------------------------
-/
class NatConv (α : Type u) where
  ofNat : Nat → α
  toNat : α → Nat

instance : NatConv Int where
  ofNat := Int.ofNat
  toNat := fun i => Int.toNat i

instance : NatConv Int32 where
  ofNat n := Int32.ofInt (Int.ofNat n)
  toNat x := Int.toNat x.toInt

instance : NatConv Int64 where
  ofNat n := Int64.ofInt (Int.ofNat n)
  toNat x := Int.toNat x.toInt

-- val has_bit : nat -> nat -> bool
def hasBit (n bit : Nat) : Bool :=
  ((n / (2 ^ bit)) % 2) == 1

/-
  --------------------------------
  Read class
  --------------------------------
-/
def elemChar (c : Char) (s : String) : Bool :=
  s.toList.contains c

def isWhitespace (c : Char) : Bool := elemChar c " \n\t"
def isDigit (c : Char) : Bool := elemChar c "1234567890"
def isOctalDigit (c : Char) : Bool := elemChar c "01234567"
def isNumConstChar (c : Char) : Bool := elemChar c "1234567890xabcdefABCDEF"

-- val is_numeric : list char -> bool
def isNumeric (cs : List Char) : Bool :=
  cs.foldr (fun c ok => isNumConstChar c && ok) true

-- val hexalpha_to_num : char -> either string nat
def hexalphaToNum (c : Char) : Except String Nat :=
  match c with
  | '0' => .ok 0
  | '1' => .ok 1
  | '2' => .ok 2
  | '3' => .ok 3
  | '4' => .ok 4
  | '5' => .ok 5
  | '6' => .ok 6
  | '7' => .ok 7
  | '8' => .ok 8
  | '9' => .ok 9
  | 'a' | 'A' => .ok 10
  | 'b' | 'B' => .ok 11
  | 'c' | 'C' => .ok 12
  | 'd' | 'D' => .ok 13
  | 'e' | 'E' => .ok 14
  | 'f' | 'F' => .ok 15
  | _ => .error s!"bad digit '{c}'"

/-
  * Read can fail with an error message by using Left.
  * Do not use any methods that may throw errors.
-/
class Read (α : Type u) where
  read  : List Char → Except String α
  write : α → String

-- val trim : list char -> list char
def trim (cs : List Char) : List Char :=
  let l := cs.dropWhile isWhitespace
  let r := (l.reverse.dropWhile isWhitespace).reverse
  r

-- let rec readConstant dec hex oct chars =
def readConstant
    (dec hex oct : List Char → Except String Int)
    (chars : List Char) : Except String Int :=
  let cs := trim chars
  let (neg, cs') :=
    match cs with
    | '-' :: rest => (true,  rest)
    | '+' :: rest => (false, rest)
    | _           => (false, cs)
  let res :=
    match cs' with
    | ['0']            => dec cs'
    | '0'::'x'::rest   => hex rest
    | '0'::rest        => oct rest
    | _                => dec cs'
  match res with
  | .error e => .error e
  | .ok n    => if neg then .ok (-n) else .ok n

def readConstant64
    (dec hex oct : List Char → Except String Int64)
    (chars : List Char) : Except String Int64 :=
  let cs := trim chars
  let (neg, cs') :=
    match cs with
    | '-' :: rest => (true,  rest)
    | '+' :: rest => (false, rest)
    | _           => (false, cs)
  let res :=
    match cs' with
    | ['0']          => dec cs'
    | '0'::'x'::rest => hex rest
    | '0'::rest      => oct rest
    | _              => dec cs'
  match res with
  | .error e => .error e
  | .ok n    => if neg then .ok (-n) else .ok n

def readConstant32
    (dec hex oct : List Char → Except String Int32)
    (chars : List Char) : Except String Int32 :=
  let cs := trim chars
  let (neg, cs') :=
    match cs with
    | '-' :: rest => (true,  rest)
    | '+' :: rest => (false, rest)
    | _           => (false, cs)
  let res :=
    match cs' with
    | ['0']          => dec cs'
    | '0'::'x'::rest => hex rest
    | '0'::rest      => oct rest
    | _              => dec cs'
  match res with
  | .error e => .error e
  | .ok n    => if neg then .ok (-n) else .ok n

def int64Max : Int64 := (NatConv.ofNat 2) ^ 63 - (NatConv.ofNat 1)

def int64Min : Int64 := -((NatConv.ofNat 2) ^ 63)

def int32Max : Int32 := (NatConv.ofNat 2) ^ 31 - (NatConv.ofNat 1)

def int32Min : Int32 := -((NatConv.ofNat 2) ^ 31)

/-
  --------------------------------
  unbounded_unsigned (two's complement) for Int
  --------------------------------
-/
-- val unbounded_unsigned : nat (* bits *) -> integer -> integer
def unboundedUnsigned (bits : Nat) (unboundedN : Int) : Int :=
  let signedBits := bits - 1
  let upper : Int := (2 : Int) ^ signedBits - 1
  let lower : Int := -((2 : Int) ^ signedBits)
  let n :=
    if unboundedN < lower then lower
    else if unboundedN > upper then upper
    else unboundedN
  if n < 0 then (2 : Int) ^ bits + n else n

-- val unbounded_unsigned64 : integer -> integer
def unboundedUnsigned64 (n : Int) : Int :=
  unboundedUnsigned 64 n

def splitWhile {α} (p : α → Bool) : List α → List α × List α
  | []      => ([], [])
  | x :: xs =>
    if p x then
      let (a, b) := splitWhile p xs
      (x :: a, b)
    else
      ([], x :: xs)

/-
  --------------------------------
  Integer parsing (base 2/8/10/16) for Int
  --------------------------------
-/
-- val readInteger_loop : nat -> integer -> (list char) -> either string integer
def readIntegerLoop (base : Nat) (acc : Int) : List Char → Except String Int
  | []      => .ok acc
  | c :: cs =>
    match hexalphaToNum c with
    | .error msg => .error msg
    | .ok num =>
      if num > base - 1 then
        .error s!"{c} is not a valid base {base} digit"
      else
        readIntegerLoop base ((Int.ofNat base) * acc + (Int.ofNat num)) cs

-- val readUnsignedInteger : nat -> list char -> either string integer
def readUnsignedInteger (base : Nat) (chars : List Char) : Except String Int :=
  match chars with
  | [] => .error "empty string is not numeric"
  | _  => readIntegerLoop base 0 chars

-- val readSignedInteger : nat -> list char -> either string integer
def readSignedInteger (base : Nat) (chars : List Char) : Except String Int :=
  let chars := trim chars
  match chars with
  | '+' :: cs => readUnsignedInteger base cs
  | '-' :: cs =>
    match readUnsignedInteger base cs with
    | .error e => .error e
    | .ok n    => .ok (-n)
  | _ => readUnsignedInteger base chars

/-
Lem/OCaml:
  Sys.int_size = 31 (32-bit) or 63 (64-bit)
Lean has no Sys.int_size in OCaml, but we can estimate by USize.size:
  USize.size = 32 or 64
-/
-- def system_int_size : Nat :=
--   USize.size - 1

/-
Lem:
  highestNat = 2^(s-2) - 1 + 2^(s-2)
In Lean, Nat won't overflow, but we can keep the similar structure.
-/
-- def highestNat : Nat :=
--   let k := system_int_size - 2
--   (2 ^ k - 1) + (2 ^ k)

-- val readNat : (list char) -> either string nat
def readNat (cs : List Char) : Except String Nat :=
  let cs := trim cs
  if isNumeric cs then
    match readUnsignedInteger 10 cs with
    | .error e => .error e
    | .ok n    => .ok (Int.toNat n)
  else
    .error s!"{String.ofList cs} is non-numeric"

-- val parse_nat : list char -> either string (nat * list char)
def parseNat (cs : List Char) : Except String (Nat × List Char) :=
  let (ds, rest) := splitWhile isDigit cs
  if ds.isEmpty then
    .error "no digits"
  else
    match readNat ds with
    | .error e => .error e
    | .ok n    => .ok (n, rest)

/- Lem: readInt64_loop : nat -> int64 -> list char -> either string int64 -/
def readInt64_loop (base : Nat) (acc : Int64) (chars : List Char) : Except String Int64 :=
  match chars with
  | [] => .ok acc
  | c :: cs =>
    match hexalphaToNum c with
    | .error msg => .error msg
    | .ok num =>
      if (num > base - 1) then
        .error (String.ofList [c] ++ " is not a valid base " ++ toString base ++ " digit")
      else
        let acc1 : Int64 :=
          (NatConv.ofNat base) * acc + (NatConv.ofNat num)
        if acc1 < (NatConv.ofNat (α := Int64) 0) then
          .ok int64Max
        else
          readInt64_loop base acc1 cs

/- Lem: readInt64 : nat -> list char -> either string int64 -/
def readInt64 (base : Nat) (chars : List Char) : Except String Int64 :=
  match chars with
  | [] => .error "empty string is not numeric"
  | _  => readInt64_loop base (NatConv.ofNat (α := Int64) 0) chars

/- Lem: readInt32_loop : nat -> int32 -> list char -> either string int32 -/
def readInt32_loop (base : Nat) (acc : Int32) (chars : List Char) : Except String Int32 :=
  match chars with
  | [] => .ok acc
  | c :: cs =>
    match hexalphaToNum c with
    | .error msg => .error msg
    | .ok num =>
      if (num > base - 1) then
        .error (String.ofList [c] ++ " is not a valid base " ++ toString base ++ " digit")
      else
        let acc1 : Int32 :=
          (NatConv.ofNat (α := Int32) base) * acc + (NatConv.ofNat (α := Int32) num)
        if acc1 < (NatConv.ofNat (α := Int32) 0) then
          .ok int32Max
        else
          readInt32_loop base acc1 cs

/- Lem: readInt32 : nat -> list char -> either string int32 -/
def readInt32 (base : Nat) (chars : List Char) : Except String Int32 :=
  match chars with
  | [] => .error "empty string is not numeric"
  | _  => readInt32_loop base (NatConv.ofNat (α := Int32) 0) chars

/-
  --------------------------------
  Writing (base 2/8/10/16) for Int
  --------------------------------
-/
private def validBaseNat (b : Nat) : Bool :=
  (b == 2) || (b == 8) || (b == 10) || (b == 16)

-- Lem: digits = toCharList "0123456789abcdef"
private def digits : List Char := "0123456789abcdef".toList

-- Lem: index digits n : maybe char
private def listGet? {α : Type u} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet? xs n

-- val conv_digit : nat -> string
def conv_digit (n : Nat) : String :=
  match listGet? digits n with
  | none   => panic! "invalid digit---can only go up to hexadecimal"
  | some c => String.ofList [c]

-- val write_helper : forall 'a. Eq 'a, Nat 'a, NumIntegerDivision 'a, NumRemainder 'a => 'a -> string -> 'a -> string
partial def write_helper (α : Type u)
    [DecidableEq α] [NatConv α] [HDiv α α α] [HMod α α α]
    (base : α) (str : String) (n : α) : String :=
  let b := NatConv.toNat base
  if !(validBaseNat b) then
    panic! "can only work with binary, octal, decimal, and hexadecimal"
  else
    if n = NatConv.ofNat 0 then
      str
    else
      let next_digit : α := n % base
      write_helper α base (conv_digit (NatConv.toNat next_digit) ++ str) (n / base)

-- val unbounded_write_base : forall 'a. Eq 'a, Ord 'a, Nat 'a, NumNegate 'a, NumIntegerDivision 'a, NumRemainder 'a => 'a (* base *) -> 'a (* num *) -> string
def unbounded_write_base (α : Type u)
    [DecidableEq α] [LT α] [DecidableRel (fun a b : α => a < b)]
    [NatConv α] [Neg α] [HDiv α α α] [HMod α α α]
    (base : α) (n : α) : String :=
  if n < NatConv.ofNat 0 then
    "-" ++ write_helper α base "" (-n)
  else if n = NatConv.ofNat 0 then
    "0"
  else
    write_helper α base "" n

abbrev unbounded_write := unbounded_write_base

-- val unbounded_write_decimal : forall 'a. Eq 'a, Ord 'a, Nat 'a, NumNegate 'a, NumIntegerDivision 'a, NumRemainder 'a => 'a -> string
def unbounded_write_decimal (α : Type u)
    [DecidableEq α] [LT α] [DecidableRel (fun a b : α => a < b)]
    [NatConv α] [Neg α] [HDiv α α α] [HMod α α α]
    (n : α) : String :=
  unbounded_write α (NatConv.ofNat 10) n

-- val unbounded_write_octal : forall 'a. Eq 'a, Ord 'a, Nat 'a, NumNegate 'a, NumIntegerDivision 'a, NumRemainder 'a => 'a -> string
def unbounded_write_octal (α : Type u)
    [DecidableEq α]  [LT α] [DecidableRel (fun a b : α => a < b)]
    [NatConv α] [Neg α] [HDiv α α α] [HMod α α α]
    (n : α) : String :=
  unbounded_write α (NatConv.ofNat 8) n

-- val unbounded_write_hex : forall 'a. Eq 'a, Ord 'a, Nat 'a, NumNegate 'a, NumIntegerDivision 'a, NumRemainder 'a => 'a -> string
def unbounded_write_hex (α : Type u)
    [DecidableEq α] [LT α] [DecidableRel (fun a b : α => a < b)]
    [NatConv α] [Neg α] [HDiv α α α] [HMod α α α]
    (n : α) : String :=
  unbounded_write α (NatConv.ofNat 16) n


def write32 (x : Int32) : String := toString x.toInt
def write64 (x : Int64) : String := toString x.toInt

-- val unbounded_read : list char -> either string integer
def unbounded_read (cs : List Char) : Except String Int :=
  readConstant (readUnsignedInteger 10) (readUnsignedInteger 16) (readUnsignedInteger 8) cs

instance : Read Int where
  read  := unbounded_read
  write := fun (n : Int) => unbounded_write_decimal Int n

instance : Read Int64 where
  read  := fun cs => readConstant64 (readInt64 10) (readInt64 16) (readInt64 8) cs
  write := write64

instance : Read Int32 where
  read  := fun cs => readConstant32 (readInt32 10) (readInt32 16) (readInt32 8) cs
  write := write32

end Smoosh.Num
