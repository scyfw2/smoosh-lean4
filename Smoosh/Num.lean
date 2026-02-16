/-!
  # Smoosh.Num — Numeric parsing and rendering utilities
  Translated from `smoosh_num.lem`.

  Provides character classification, integer reading/writing in multiple bases,
  and the `SmooshNat`/`SmooshRead` typeclasses for numeric type abstraction.
  Lean uses unbounded integers, so `readInt32`/`readInt64`/`write32`/`write64` are not translated.
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

/-- Ref: smoosh_num.lem:has_bit — Test whether bit `bit` is set in `n`. -/
def hasBit (n : Nat) (bit : Nat) : Bool :=
  (n / (2 ^ bit)) % 2 == 1

/-! # Character classification -/

/-- Ref: smoosh_num.lem:is_whitespace — Whitespace check (space, newline, tab). -/
def isWhitespace (c : Char) : Bool :=
  c == ' ' || c == '\n' || c == '\t'

/-- Ref: smoosh_num.lem:is_digit — Decimal digit check. -/
def isDigit (c : Char) : Bool :=
  '0' ≤ c && c ≤ '9'

/-- Ref: smoosh_num.lem:is_octal_digit -/
def isOctalDigit (c : Char) : Bool :=
  '0' ≤ c && c ≤ '7'

/-- Ref: smoosh_num.lem:is_num_const_char — Digit or hex letter or 'x'. -/
def isNumConstChar (c : Char) : Bool :=
  isDigit c || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F') || c == 'x'

/-- Ref: smoosh_num.lem:is_numeric — All chars are numeric constant chars. -/
def isNumeric (cs : List Char) : Bool :=
  cs.all isNumConstChar

/-! # Hex/digit conversion -/

/-- Ref: smoosh_num.lem:hexalpha_to_num — Convert hex digit char to numeric value. -/
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

/-- Ref: smoosh_num.lem:trim — Strip leading/trailing whitespace from char list. -/
def trim (cs : List Char) : List Char :=
  let ltrim := cs.dropWhile isWhitespace
  let rtrimRev := ltrim.reverse.dropWhile isWhitespace
  rtrimRev.reverse

def stringOfList (cs : List Char) : String := String.ofList cs

/-! # Integer reading -/

/-- Ref: smoosh_num.lem:readInteger_loop — Read digits in given base, accumulating value. -/
def readIntegerLoop (base : Nat) (acc : Int) : List Char → Except String Int
  | [] => .ok acc
  | c :: cs => do
    let num ← hexalphaToNum c
    if num ≥ base then
      .error s!"{c} is not a valid base {base} digit"
    else
      readIntegerLoop base (Int.ofNat base * acc + Int.ofNat num) cs

/-- Ref: smoosh_num.lem:readUnsignedInteger — Read unsigned integer in given base. -/
def readUnsignedInteger (base : Nat) (chars : List Char) : Except String Int :=
  match chars with
  | [] => .error "empty string is not numeric"
  | _ => readIntegerLoop base 0 chars

/-- Ref: smoosh_num.lem:readSignedInteger — Read integer with optional + or - sign. -/
def readSignedInteger (base : Nat) (chars : List Char) : Except String Int :=
  let chars := trim chars
  match chars with
  | '+' :: cs => readUnsignedInteger base cs
  | '-' :: cs => do
    let n ← readUnsignedInteger base cs
    .ok (-n)
  | _ => readUnsignedInteger base chars

/-- Ref: smoosh_num.lem:readConstant — Read integer constant with 0x/0 prefix detection. -/
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

/-- Ref: smoosh_num.lem:highestNat — Upper bound for Nat reading (2^62 - 1). -/
def highestNat : Nat := 2 ^ 62 - 1

/-- Ref: smoosh_num.lem:readNat — Read a base-10 natural number, clamped to `highestNat`. -/
def readNat (cs : List Char) : Except String Nat :=
  let cs := trim cs
  if isNumeric cs then
    match readUnsignedInteger 10 cs with
    | .ok n =>
      if n > Int.ofNat highestNat then .ok highestNat
      else .ok n.toNat
    | .error e => .error e
  else .error s!"{String.ofList cs} is non-numeric"

/-- Ref: smoosh_num.lem:parse_nat — Read leading digits, return (value, remaining chars). -/
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

/-- Ref: smoosh_num.lem:conv_digit — Convert a digit value (0–15) to its character. -/
def convDigit (n : Nat) : String :=
  if h : n < digits.length then
    let c := digits[n]
    String.ofList [c]
  else
    panic! "invalid digit---can only go up to hexadecimal"

/-- Ref: smoosh_num.lem:write_helper — Recursive base-conversion helper.
    TODO: `decreasing_by sorry` — termination proof not provided. -/
def writeHelper (base : Int) (str : String) (n : Int) : String :=
  if n == 0 then str
  else
    let nextDigit := n % base
    writeHelper base (convDigit nextDigit.toNat ++ str) (n / base)
termination_by n.toNat
decreasing_by all_goals sorry

/-- Ref: smoosh_num.lem:unbounded_write_base — Write integer in given base (unbounded). -/
def unboundedWriteBase (base : Int) (n : Int) : String :=
  if n < 0 then "-" ++ writeHelper base "" (-n)
  else if n == 0 then "0"
  else writeHelper base "" n

/-- Ref: smoosh_num.lem:unbounded_write_decimal -/
def unboundedWriteDecimal (n : Int) : String := unboundedWriteBase 10 n
/-- Ref: smoosh_num.lem:unbounded_write_octal -/
def unboundedWriteOctal (n : Int) : String := unboundedWriteBase 8 n
/-- Ref: smoosh_num.lem:unbounded_write_hex -/
def unboundedWriteHex (n : Int) : String := unboundedWriteBase 16 n

/-! # Unbounded read -/

/-- Ref: smoosh_num.lem:unbounded_read — Read integer with 0x/0 prefix detection (unbounded). -/
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
