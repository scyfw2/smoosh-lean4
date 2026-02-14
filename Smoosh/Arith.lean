/-
  Smoosh.Arith — Arithmetic expression lexer, parser, and evaluator
  Translated from arith.lem (657 lines)
-/
import Smoosh.Num
import Smoosh.Prelude

/-! # Arithmetic tokens -/

inductive ArithToken where
  | tNum (n : Int)
  | tVar (s : String)
  | tPlus | tMinus | tTimes | tDiv | tMod
  | tLShift | tRShift
  | tLt | tLte | tGt | tGte | tEq | tNEq
  | tBitAnd | tBitOr | tBitXOr
  | tBoolAnd | tBoolOr
  | tBitNot | tBoolNot
  | tPreIncr | tPreDecr
  | tColon | tQuestion
  | tVarEq | tVarPlusEq | tVarMinusEq
  | tVarTimesEq | tVarDivEq | tVarModEq
  | tVarLShiftEq | tVarRShiftEq
  | tVarBitAndEq | tVarBitOrEq | tVarBitXOrEq
  | tLParen | tRParen
  deriving Repr, BEq

/-! # Binary operators -/

inductive BinaryOperator where
  | plus | minus | times | div | mod
  | lshift | rshift
  | lt | lte | gt | gte | eq | neq
  | bitAnd | bitOr | bitXOr
  | boolAnd | boolOr
  deriving Repr, BEq

/-! # Arithmetic expressions -/

inductive ArithExp where
  | num (n : Int)
  | var (s : String)
  | binOp (op : BinaryOperator) (l r : ArithExp)
  | unaryPlus (e : ArithExp)
  | unaryMinus (e : ArithExp)
  | bitNot (e : ArithExp)
  | boolNot (e : ArithExp)
  | preIncr (s : String)
  | preDecr (s : String)
  | postIncr (s : String)
  | postDecr (s : String)
  | conditional (cond t f : ArithExp)
  | assignVar (s : String) (op : Option BinaryOperator) (e : ArithExp)
  deriving Repr, BEq

/-! # Lexer -/

def isArithDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'
def isArithAlpha (c : Char) : Bool := isVariableInitialChar c

def span' (f : Char → Bool) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    if f c then
      let (s, rst) := span' f cs
      (c :: s, rst)
    else ([], c :: cs)

partial def lexer (str : List Char) : Except String (List ArithToken) :=
  match str with
  | [] => .ok []
  | '^' :: '=' :: cs => (.tVarBitXOrEq :: ·) <$> lexer cs
  | '|' :: '=' :: cs => (.tVarBitOrEq :: ·) <$> lexer cs
  | '&' :: '=' :: cs => (.tVarBitAndEq :: ·) <$> lexer cs
  | '>' :: '>' :: '=' :: cs => (.tVarRShiftEq :: ·) <$> lexer cs
  | '<' :: '<' :: '=' :: cs => (.tVarLShiftEq :: ·) <$> lexer cs
  | '/' :: '=' :: cs => (.tVarDivEq :: ·) <$> lexer cs
  | '%' :: '=' :: cs => (.tVarModEq :: ·) <$> lexer cs
  | '-' :: '=' :: cs => (.tVarMinusEq :: ·) <$> lexer cs
  | '+' :: '=' :: cs => (.tVarPlusEq :: ·) <$> lexer cs
  | '*' :: '=' :: cs => (.tVarTimesEq :: ·) <$> lexer cs
  | '>' :: '>' :: cs => (.tRShift :: ·) <$> lexer cs
  | '<' :: '<' :: cs => (.tLShift :: ·) <$> lexer cs
  | '|' :: '|' :: cs => (.tBoolOr :: ·) <$> lexer cs
  | '&' :: '&' :: cs => (.tBoolAnd :: ·) <$> lexer cs
  | '=' :: '=' :: cs => (.tEq :: ·) <$> lexer cs
  | '!' :: '=' :: cs => (.tNEq :: ·) <$> lexer cs
  | '>' :: '=' :: cs => (.tGte :: ·) <$> lexer cs
  | '<' :: '=' :: cs => (.tLte :: ·) <$> lexer cs
  | '+' :: '+' :: cs => (.tPreIncr :: ·) <$> lexer cs
  | '-' :: '-' :: cs => (.tPreDecr :: ·) <$> lexer cs
  | '=' :: cs => (.tVarEq :: ·) <$> lexer cs
  | ':' :: cs => (.tColon :: ·) <$> lexer cs
  | '?' :: cs => (.tQuestion :: ·) <$> lexer cs
  | '^' :: cs => (.tBitXOr :: ·) <$> lexer cs
  | '|' :: cs => (.tBitOr :: ·) <$> lexer cs
  | '&' :: cs => (.tBitAnd :: ·) <$> lexer cs
  | '>' :: cs => (.tGt :: ·) <$> lexer cs
  | '<' :: cs => (.tLt :: ·) <$> lexer cs
  | '~' :: cs => (.tBitNot :: ·) <$> lexer cs
  | '!' :: cs => (.tBoolNot :: ·) <$> lexer cs
  | '*' :: cs => (.tTimes :: ·) <$> lexer cs
  | '/' :: cs => (.tDiv :: ·) <$> lexer cs
  | '%' :: cs => (.tMod :: ·) <$> lexer cs
  | '-' :: cs => (.tMinus :: ·) <$> lexer cs
  | '+' :: cs => (.tPlus :: ·) <$> lexer cs
  | '(' :: cs => (.tLParen :: ·) <$> lexer cs
  | ')' :: cs => (.tRParen :: ·) <$> lexer cs
  | c :: cs =>
    if isArithDigit c then
      let (digits, rst) := span' isNumConstChar cs
      match unboundedRead (c :: digits) with
      | .ok n => (.tNum n :: ·) <$> lexer rst
      | .error e => .error e
    else if isVariableInitialChar c then
      let (varChars, rst) := span' isVariableChar cs
      (.tVar (String.ofList (c :: varChars)) :: ·) <$> lexer rst
    else if isWhitespace c then
      lexer cs
    else
      .error s!"{String.ofList [c]} is an unrecognized character"

/-! # Parser (recursive descent) -/

mutual
partial def parseAssignment (tkns : List ArithToken) : Except String (ArithExp × List ArithToken) :=
  match tkns with
  | .tVar s :: .tVarEq :: rst => collectAssignment (.assignVar s none) rst
  | .tVar s :: .tVarPlusEq :: rst => collectAssignment (.assignVar s (some .plus)) rst
  | .tVar s :: .tVarMinusEq :: rst => collectAssignment (.assignVar s (some .minus)) rst
  | .tVar s :: .tVarTimesEq :: rst => collectAssignment (.assignVar s (some .times)) rst
  | .tVar s :: .tVarDivEq :: rst => collectAssignment (.assignVar s (some .div)) rst
  | .tVar s :: .tVarModEq :: rst => collectAssignment (.assignVar s (some .mod)) rst
  | .tVar s :: .tVarLShiftEq :: rst => collectAssignment (.assignVar s (some .lshift)) rst
  | .tVar s :: .tVarRShiftEq :: rst => collectAssignment (.assignVar s (some .rshift)) rst
  | .tVar s :: .tVarBitAndEq :: rst => collectAssignment (.assignVar s (some .bitAnd)) rst
  | .tVar s :: .tVarBitOrEq :: rst => collectAssignment (.assignVar s (some .bitOr)) rst
  | .tVar s :: .tVarBitXOrEq :: rst => collectAssignment (.assignVar s (some .bitXOr)) rst
  | _ => parseConditional tkns

partial def collectAssignment (mk : ArithExp → ArithExp) (tkns : List ArithToken) : Except String (ArithExp × List ArithToken) := do
  let (term, rst) ← parseAssignment tkns
  .ok (mk term, rst)

partial def parseConditional (tkns : List ArithToken) : Except String (ArithExp × List ArithToken) := do
  let (term, rst) ← parseBoolOr tkns
  firstConditionalTerm term rst

partial def firstConditionalTerm (boolean : ArithExp) (tkns : List ArithToken) : Except String (ArithExp × List ArithToken) :=
  match tkns with
  | .tQuestion :: rst1 => do
    let (lhs, rst2) ← parseConditional rst1
    secondConditionalTerm boolean lhs rst2
  | _ => .ok (boolean, tkns)

partial def secondConditionalTerm (cond lhs : ArithExp) (tkns : List ArithToken) : Except String (ArithExp × List ArithToken) :=
  match tkns with
  | .tColon :: rst => do
    let (rhs, rst2) ← parseConditional rst
    .ok (.conditional cond lhs rhs, rst2)
  | _ => .error "expected ':' in conditional"

partial def parseBoolOr (tkns : List ArithToken) : Except String (ArithExp × List ArithToken) := do
  let (term, rst) ← parseBoolAnd tkns
  boolOrTerm term rst

partial def boolOrTerm (lhs : ArithExp) (tkns : List ArithToken) : Except String (ArithExp × List ArithToken) :=
  match tkns with
  | .tBoolOr :: rst => do
    let (rhs, rst2) ← parseBoolAnd rst
    boolOrTerm (.binOp .boolOr lhs rhs) rst2
  | _ => .ok (lhs, tkns)

partial def parseBoolAnd (tkns : List ArithToken) : Except String (ArithExp × List ArithToken) := do
  let (term, rst) ← parseBitOr tkns
  boolAndTerm term rst

partial def boolAndTerm (lhs : ArithExp) (tkns : List ArithToken) : Except String (ArithExp × List ArithToken) :=
  match tkns with
  | .tBoolAnd :: rst => do
    let (rhs, rst2) ← parseBitOr rst
    boolAndTerm (.binOp .boolAnd lhs rhs) rst2
  | _ => .ok (lhs, tkns)

partial def parseBitOr (tkns : List ArithToken) : Except String (ArithExp × List ArithToken) := do
  let (term, rst) ← parseBitXOr tkns
  bitOrTerm term rst

partial def bitOrTerm (lhs : ArithExp) (tkns : List ArithToken) : Except String (ArithExp × List ArithToken) :=
  match tkns with
  | .tBitOr :: rst => do
    let (rhs, rst2) ← parseBitXOr rst
    bitOrTerm (.binOp .bitOr lhs rhs) rst2
  | _ => .ok (lhs, tkns)

partial def parseBitXOr (tkns : List ArithToken) : Except String (ArithExp × List ArithToken) := do
  let (term, rst) ← parseBitAnd tkns
  bitXOrTerm term rst

partial def bitXOrTerm (lhs : ArithExp) (tkns : List ArithToken) : Except String (ArithExp × List ArithToken) :=
  match tkns with
  | .tBitXOr :: rst => do
    let (rhs, rst2) ← parseBitAnd rst
    bitXOrTerm (.binOp .bitXOr lhs rhs) rst2
  | _ => .ok (lhs, tkns)

partial def parseBitAnd (tkns : List ArithToken) : Except String (ArithExp × List ArithToken) := do
  let (term, rst) ← parseEquality tkns
  bitAndTerm term rst

partial def bitAndTerm (lhs : ArithExp) (tkns : List ArithToken) : Except String (ArithExp × List ArithToken) :=
  match tkns with
  | .tBitAnd :: rst => do
    let (rhs, rst2) ← parseEquality rst
    bitAndTerm (.binOp .bitAnd lhs rhs) rst2
  | _ => .ok (lhs, tkns)

partial def parseEquality (tkns : List ArithToken) : Except String (ArithExp × List ArithToken) := do
  let (term, rst) ← parseRelational tkns
  equalityTerm term rst

partial def equalityTerm (lhs : ArithExp) (tkns : List ArithToken) : Except String (ArithExp × List ArithToken) :=
  match tkns with
  | .tEq :: rst => do
    let (rhs, rst2) ← parseRelational rst
    equalityTerm (.binOp .eq lhs rhs) rst2
  | .tNEq :: rst => do
    let (rhs, rst2) ← parseRelational rst
    equalityTerm (.binOp .neq lhs rhs) rst2
  | _ => .ok (lhs, tkns)

partial def parseRelational (tkns : List ArithToken) : Except String (ArithExp × List ArithToken) := do
  let (term, rst) ← parseBitShift tkns
  relationalTerm term rst

partial def relationalTerm (lhs : ArithExp) (tkns : List ArithToken) : Except String (ArithExp × List ArithToken) :=
  match tkns with
  | .tLt :: rst => do
    let (rhs, rst2) ← parseBitShift rst; relationalTerm (.binOp .lt lhs rhs) rst2
  | .tLte :: rst => do
    let (rhs, rst2) ← parseBitShift rst; relationalTerm (.binOp .lte lhs rhs) rst2
  | .tGt :: rst => do
    let (rhs, rst2) ← parseBitShift rst; relationalTerm (.binOp .gt lhs rhs) rst2
  | .tGte :: rst => do
    let (rhs, rst2) ← parseBitShift rst; relationalTerm (.binOp .gte lhs rhs) rst2
  | _ => .ok (lhs, tkns)

partial def parseBitShift (tkns : List ArithToken) : Except String (ArithExp × List ArithToken) := do
  let (term, rst) ← parseAdditive tkns
  shiftTerm term rst

partial def shiftTerm (lhs : ArithExp) (tkns : List ArithToken) : Except String (ArithExp × List ArithToken) :=
  match tkns with
  | .tLShift :: rst => do
    let (rhs, rst2) ← parseAdditive rst; shiftTerm (.binOp .lshift lhs rhs) rst2
  | .tRShift :: rst => do
    let (rhs, rst2) ← parseAdditive rst; shiftTerm (.binOp .rshift lhs rhs) rst2
  | _ => .ok (lhs, tkns)

partial def parseAdditive (tkns : List ArithToken) : Except String (ArithExp × List ArithToken) := do
  let (term, rst) ← parseMultiplicative tkns
  additiveTerm term rst

partial def additiveTerm (lhs : ArithExp) (tkns : List ArithToken) : Except String (ArithExp × List ArithToken) :=
  match tkns with
  | .tPlus :: rst => do
    let (rhs, rst2) ← parseMultiplicative rst; additiveTerm (.binOp .plus lhs rhs) rst2
  | .tMinus :: rst => do
    let (rhs, rst2) ← parseMultiplicative rst; additiveTerm (.binOp .minus lhs rhs) rst2
  | _ => .ok (lhs, tkns)

partial def parseMultiplicative (tkns : List ArithToken) : Except String (ArithExp × List ArithToken) := do
  let (term, rst) ← parseUnary tkns
  multiplicativeTerm term rst

partial def multiplicativeTerm (lhs : ArithExp) (tkns : List ArithToken) : Except String (ArithExp × List ArithToken) :=
  match tkns with
  | .tTimes :: rst => do
    let (rhs, rst2) ← parseUnary rst; multiplicativeTerm (.binOp .times lhs rhs) rst2
  | .tDiv :: rst => do
    let (rhs, rst2) ← parseUnary rst; multiplicativeTerm (.binOp .div lhs rhs) rst2
  | .tMod :: rst => do
    let (rhs, rst2) ← parseUnary rst; multiplicativeTerm (.binOp .mod lhs rhs) rst2
  | _ => .ok (lhs, tkns)

partial def parseUnary (tkns : List ArithToken) : Except String (ArithExp × List ArithToken) :=
  match tkns with
  | .tPlus :: rst => do
    let (e, rst2) ← parseUnary rst; .ok (.unaryPlus e, rst2)
  | .tMinus :: rst => do
    let (e, rst2) ← parseUnary rst; .ok (.unaryMinus e, rst2)
  | .tBitNot :: rst => do
    let (e, rst2) ← parseUnary rst; .ok (.bitNot e, rst2)
  | .tBoolNot :: rst => do
    let (e, rst2) ← parseUnary rst; .ok (.boolNot e, rst2)
  | .tPreIncr :: .tVar s :: rst => .ok (.preIncr s, rst)
  | .tPreDecr :: .tVar s :: rst => .ok (.preDecr s, rst)
  | _ => parsePostfix tkns

partial def parsePostfix (tkns : List ArithToken) : Except String (ArithExp × List ArithToken) :=
  match tkns with
  | .tVar s :: .tPreIncr :: rst => .ok (.postIncr s, rst)
  | .tVar s :: .tPreDecr :: rst => .ok (.postDecr s, rst)
  | _ => parsePrimary tkns

partial def parsePrimary (tkns : List ArithToken) : Except String (ArithExp × List ArithToken) :=
  match tkns with
  | .tNum n :: rst => .ok (.num n, rst)
  | .tVar s :: rst => .ok (.var s, rst)
  | .tLParen :: rst => do
    let (e, rst2) ← parseAssignment rst
    match rst2 with
    | .tRParen :: rst3 => .ok (e, rst3)
    | _ => .error "expected ')'"
  | _ => .error "unexpected token in arithmetic expression"
end

def parseArith (s : String) : Except String ArithExp := do
  let tkns ← lexer s.toList
  let (e, rest) ← parseAssignment tkns
  if rest.isEmpty then .ok e
  else .error s!"unexpected tokens after arithmetic expression"

/-! # Evaluator -/

-- The evaluator needs variable lookup/assignment from the shell state.
-- We parameterize it as functions.

def evalBinOp (op : BinaryOperator) (l r : Int) : Except String Int :=
  match op with
  | .plus => .ok (l + r)
  | .minus => .ok (l - r)
  | .times => .ok (l * r)
  | .div => if r == 0 then .error "division by zero" else .ok (l / r)
  | .mod => if r == 0 then .error "division by zero" else .ok (l % r)
  | .lshift => .ok (l * (2 ^ r.toNat))
  | .rshift => .ok (l / (2 ^ r.toNat))
  | .lt => .ok (if l < r then 1 else 0)
  | .lte => .ok (if l ≤ r then 1 else 0)
  | .gt => .ok (if l > r then 1 else 0)
  | .gte => .ok (if l ≥ r then 1 else 0)
  | .eq => .ok (if l == r then 1 else 0)
  | .neq => .ok (if l != r then 1 else 0)
  | .bitAnd => .ok (Int.ofNat (Nat.land l.toNat r.toNat))
  | .bitOr => .ok (Int.ofNat (Nat.lor l.toNat r.toNat))
  | .bitXOr => .ok (Int.ofNat (Nat.xor l.toNat r.toNat))
  | .boolAnd => .ok (if l != 0 && r != 0 then 1 else 0)
  | .boolOr => .ok (if l != 0 || r != 0 then 1 else 0)

partial def evalArith (getVar : String → Int) (setVar : String → Int → Unit)
    (e : ArithExp) : Except String Int :=
  match e with
  | .num n => .ok n
  | .var s => .ok (getVar s)
  | .binOp op l r => do
    let lv ← evalArith getVar setVar l
    let rv ← evalArith getVar setVar r
    evalBinOp op lv rv
  | .unaryPlus e' => evalArith getVar setVar e'
  | .unaryMinus e' => do
    let v ← evalArith getVar setVar e'
    .ok (-v)
  | .bitNot e' => do
    let v ← evalArith getVar setVar e'
    .ok (-(v + 1))
  | .boolNot e' => do
    let v ← evalArith getVar setVar e'
    .ok (if v == 0 then 1 else 0)
  | .preIncr s =>
    let v := getVar s + 1
    let _ := setVar s v
    .ok v
  | .preDecr s =>
    let v := getVar s - 1
    let _ := setVar s v
    .ok v
  | .postIncr s =>
    let v := getVar s
    let _ := setVar s (v + 1)
    .ok v
  | .postDecr s =>
    let v := getVar s
    let _ := setVar s (v - 1)
    .ok v
  | .conditional cond t f => do
    let cv ← evalArith getVar setVar cond
    if cv != 0 then evalArith getVar setVar t
    else evalArith getVar setVar f
  | .assignVar s mop rhs => do
    let rv ← evalArith getVar setVar rhs
    let v := match mop with
      | none => rv
      | some op =>
        let lv := getVar s
        match evalBinOp op lv rv with
        | .ok r => r
        | .error _ => rv  -- fallback
    let _ := setVar s v
    .ok v
