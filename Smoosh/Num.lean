/-
  Smoosh.Num — Numeric parsing and rendering utilities
  Translated from smoosh_num.lem
-/

/-! # SmooshNat typeclass -/

class SmooshNat (α : Type) where
  fromNat : Nat → α
  toNat : α → Nat

instance : SmooshNat Int where
  fromNat := Int.ofNat
  toNat := Int.toNat

instance : SmooshNat Nat where
  fromNat := id
  toNat := id

/-! # Bit testing -/

def hasBit (n : Nat) (bit : Nat) : Bool :=
  (n / (2 ^ bit)) % 2 == 1

/-! # Character classification -/

def isWhitespace (c : Char) : Bool :=
  c == ' ' || c == '\n' || c == '\t'

def isDigit (c : Char) : Bool :=
  '0' ≤ c && c ≤ '9'

def isOctalDigit (c : Char) : Bool :=
  '0' ≤ c && c ≤ '7'

def isNumConstChar (c : Char) : Bool :=
  isDigit c || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F') || c == 'x'

def isNumeric (cs : List Char) : Bool :=
  cs.all isNumConstChar

/-! # Hex/digit conversion -/

def hexalphaToNum (c : Char) : Except String Nat :=
  if '0' ≤ c && c ≤ '9' then .ok (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then .ok (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then .ok (c.toNat - 'A'.toNat + 10)
  else .error s!"bad digit '{c}'"

/-! # SmooshRead typeclass -/

class SmooshRead (α : Type) where
  read : List Char → Except String α
  write : α → String

/-! # Trimming -/

def trim (cs : List Char) : List Char :=
  let ltrim := cs.dropWhile isWhitespace
  let rtrimRev := ltrim.reverse.dropWhile isWhitespace
  rtrimRev.reverse

def stringOfList (cs : List Char) : String := String.ofList cs

/-! # Integer reading -/

def readIntegerLoop (base : Nat) (acc : Int) : List Char → Except String Int
  | [] => .ok acc
  | c :: cs => do
    let num ← hexalphaToNum c
    if num ≥ base then
      .error s!"{c} is not a valid base {base} digit"
    else
      readIntegerLoop base (Int.ofNat base * acc + Int.ofNat num) cs

def readUnsignedInteger (base : Nat) (chars : List Char) : Except String Int :=
  match chars with
  | [] => .error "empty string is not numeric"
  | _ => readIntegerLoop base 0 chars

def readSignedInteger (base : Nat) (chars : List Char) : Except String Int :=
  let chars := trim chars
  match chars with
  | '+' :: cs => readUnsignedInteger base cs
  | '-' :: cs => do
    let n ← readUnsignedInteger base cs
    .ok (-n)
  | _ => readUnsignedInteger base chars

def readConstant (dec hex oct : List Char → Except String Int) (chars : List Char) : Except String Int :=
  let cs := trim chars
  let (negative, cs') :=
    match cs with
    | '-' :: cs' => (true, cs')
    | '+' :: cs' => (false, cs')
    | _ => (false, cs)
  let res :=
    match cs' with
    | ['0'] => dec cs'
    | '0' :: 'x' :: cs'' => hex cs''
    | '0' :: cs'' => oct cs''
    | _ => dec cs'
  if negative then do
    let n ← res
    .ok (-n)
  else res

/-! # Nat reading (base 10 only) -/

-- Highest nat: we use a large value
def highestNat : Nat := 2 ^ 62 - 1

def readNat (cs : List Char) : Except String Nat :=
  let cs := trim cs
  if isNumeric cs then
    match readUnsignedInteger 10 cs with
    | .ok n =>
      if n > Int.ofNat highestNat then .ok highestNat
      else .ok n.toNat
    | .error e => .error e
  else .error s!"{String.ofList cs} is non-numeric"

def parseNat (cs : List Char) : Except String (Nat × List Char) :=
  let (ds, rest) := cs.span isDigit
  match ds with
  | [] => .error "no digits"
  | _ => do
    let n ← readNat ds
    .ok (n, rest)

/-! # Writing numbers -/

private def digits : List Char :=
  "0123456789abcdef".toList

def convDigit (n : Nat) : String :=
  if h : n < digits.length then
    let c := digits[n]
    String.ofList [c]
  else
    panic! "invalid digit---can only go up to hexadecimal"

def writeHelper (base : Int) (str : String) (n : Int) : String :=
  if n == 0 then str
  else
    let nextDigit := n % base
    writeHelper base (convDigit nextDigit.toNat ++ str) (n / base)
termination_by n.toNat
decreasing_by all_goals sorry

def unboundedWriteBase (base : Int) (n : Int) : String :=
  if n < 0 then "-" ++ writeHelper base "" (-n)
  else if n == 0 then "0"
  else writeHelper base "" n

def unboundedWriteDecimal (n : Int) : String := unboundedWriteBase 10 n
def unboundedWriteOctal (n : Int) : String := unboundedWriteBase 8 n
def unboundedWriteHex (n : Int) : String := unboundedWriteBase 16 n

/-! # Unbounded read -/

def unboundedRead (cs : List Char) : Except String Int :=
  readConstant (readUnsignedInteger 10) (readUnsignedInteger 16) (readUnsignedInteger 8) cs

instance : SmooshRead Int where
  read := unboundedRead
  write := unboundedWriteDecimal

instance : SmooshRead Nat where
  read cs := do
    let n ← readNat cs
    .ok n
  write := toString
