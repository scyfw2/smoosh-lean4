import Smoosh.Num
import Smoosh.Smoosh

universe u

namespace Smoosh.Num

variable
{α β : Type u}

/-- Lem: arith_token type -/
inductive arith_token (α : Type u) : Type u where
  | TNum : α → arith_token α
  | TVar : String → arith_token α
  | TPlus | TMinus
  | TTimes | TDiv | TMod
  | TBitNot | TBoolNot      -- '!' ?
  | TLShift | TRShift
  | TLt | TLte
  | TGt | TGte
  | TEq | TNEq
  | TBitAnd | TBitOr | TBitXOr
  | TBoolAnd | TBoolOr
  | TQuestion | TColon      -- For 1 ? 17 : 18
  | TVarEq
  | TVarPlusEq | TVarMinusEq
  | TVarTimesEq | TVarDivEq | TVarModEq
  | TVarLShiftEq | TVarRShiftEq
  | TVarBitAndEq | TVarBitOrEq | TVarBitXOrEq
  | TLParen | TRParen
deriving Repr, DecidableEq, Inhabited

/--
  Lem:
  val tokenEqual : forall 'a. Eq 'a => arith_token 'a -> arith_token 'a -> bool -/
def tokenEqual [BEq α] : arith_token α → arith_token α → Bool
  | .TNum n1, .TNum n2 => n1 == n2
  | .TVar x1, .TVar x2 => x1 == x2
  | .TPlus, .TPlus => true
  | .TMinus, .TMinus => true
  | .TTimes, .TTimes => true
  | .TDiv, .TDiv => true
  | .TMod, .TMod => true
  | .TBitNot, .TBitNot => true
  | .TBoolNot, .TBoolNot => true
  | .TLShift, .TLShift => true
  | .TRShift, .TRShift => true
  | .TLt, .TLt => true
  | .TLte, .TLte => true
  | .TGt, .TGt => true
  | .TGte, .TGte => true
  | .TEq, .TEq => true
  | .TNEq, .TNEq => true
  | .TBitAnd, .TBitAnd => true
  | .TBitOr, .TBitOr => true
  | .TBitXOr, .TBitXOr => true
  | .TBoolAnd, .TBoolAnd => true
  | .TBoolOr, .TBoolOr => true
  | .TQuestion, .TQuestion => true
  | .TColon, .TColon => true
  | .TVarEq, .TVarEq => true
  | .TVarPlusEq, .TVarPlusEq => true
  | .TVarMinusEq, .TVarMinusEq => true
  | .TVarTimesEq, .TVarTimesEq => true
  | .TVarDivEq, .TVarDivEq => true
  | .TVarModEq, .TVarModEq => true
  | .TVarLShiftEq, .TVarLShiftEq => true
  | .TVarRShiftEq, .TVarRShiftEq => true
  | .TVarBitAndEq, .TVarBitAndEq => true
  | .TVarBitOrEq, .TVarBitOrEq => true
  | .TVarBitXOrEq, .TVarBitXOrEq => true
  | .TLParen, .TLParen => true
  | .TRParen, .TRParen => true
  | _, _ => false

instance [BEq α] : BEq (arith_token α) where
  beq := tokenEqual

def tokenNotEqual [BEq α] (x y : arith_token α) : Bool :=
  !(x == y)

/-- Lem:
    val eq_token_integer : arith_token integer -> arith_token integer -> bool -/
def eq_token_integer : arith_token Int → arith_token Int → Bool
  | t1, t2 => t1 == t2

/-- Lem:
    BinaryOperator type -/
inductive BinaryOperator where
  | Plus | Minus | Times | Div | Mod
  | LShift | RShift
  | Lt | Lte | Gt | Gte
  | Eq | NEq
  | BitAnd | BitOr | BitXOr
  | BoolAnd | BoolOr
deriving Repr, DecidableEq, BEq

/-- Lem:
    arith_exp type -/
inductive arith_exp (α : Type u) : Type u where
  | Num : α → arith_exp α
  | Var : String → arith_exp α
  | Neg : arith_exp α → arith_exp α
  | BitNot : arith_exp α → arith_exp α
  | BoolNot : arith_exp α → arith_exp α
  | Conditional : arith_exp α → arith_exp α → arith_exp α → arith_exp α
  | BinOp : BinaryOperator → arith_exp α → arith_exp α → arith_exp α
  | AssignVar : String → Option BinaryOperator → arith_exp α → arith_exp α
deriving Repr, DecidableEq

/-- Lem:
    val arithEqual : forall 'a. Eq 'a => arith_exp 'a -> arith_exp 'a -> bool -/
def arithEqual [BEq α] : arith_exp α → arith_exp α → Bool
  | .Num n1, .Num n2 => n1 == n2
  | .Var x1, .Var x2 => x1 == x2
  | .Neg a1, .Neg a2 => arithEqual a1 a2
  | .BitNot a1, .BitNot a2 => arithEqual a1 a2
  | .BoolNot a1, .BoolNot a2 => arithEqual a1 a2
  | .Conditional c1 t1 e1, .Conditional c2 t2 e2 =>
      arithEqual c1 c2 && arithEqual t1 t2 && arithEqual e1 e2
  | .BinOp op1 l1 r1, .BinOp op2 l2 r2 =>
      arithEqual l1 l2 && arithEqual r1 r2 && (op1 == op2)
  | .AssignVar x1 op1 a1, .AssignVar x2 op2 a2 =>
      (x1 == x2) && (op1 == op2) && arithEqual a1 a2
  | _, _ => false

instance [BEq α] : BEq (arith_exp α) where
  beq := arithEqual

def expNotEqual [BEq α] (x y : arith_exp α) : Bool :=
  !(x == y)

/-- Lem:
    val eq_arith_integer : arith_exp integer -> arith_exp integer -> bool -/
def eq_arith_integer : arith_exp Int → arith_exp Int → Bool
  | a1, a2 => a1 == a2

/-- Lem:
    val either_fmap : forall 'a 'b. ('a -> 'b) -> either string 'a -> either string 'b -/
@[simp] def either_fmap (fn : α → β) (a : Sum String α) : Sum String β :=
  Sum.elim (fun e => Sum.inl e) (fun b => Sum.inr (fn b)) a

@[simp] theorem either_fmap_inl (fn : α → β) (e : String) :
  either_fmap fn (Sum.inl e) = Sum.inl e := by rfl

@[simp] theorem either_fmap_inr (fn : α → β) (x : α) :
  either_fmap fn (Sum.inr x) = Sum.inr (fn x) := by rfl

/-- Lem:
    val either_monad : forall 'a 'b 'c. ('a -> either 'b 'c) -> either 'b 'a -> either 'b 'c -/
@[simp] def either_monad (fn : α → Sum String β) (a : Sum String α) : Sum String β :=
  Sum.elim (fun e => Sum.inl e) fn a

/-- Lem: is_plus -/
def is_plus (c : Char) : Bool :=
  match c with
  | '+' => true
  | _   => false

/-- Lem:
    val span : (char -> bool) -> (list char) -> ((list char) * list char) -/
def span (f : Char → Bool) : List Char → (List Char × List Char)
  | [] => ([], [])
  | c :: cs =>
      if f c then
        let (s, rst) := span f cs
        (c :: s, rst)
      else
        ([], c :: cs)

theorem span_snd_length_le (p : Char → Bool) (xs : List Char) :
  (span p xs).2.length ≤ xs.length := by
  induction xs with
  | nil => simp [span]
  |cons c sa ih =>
    by_cases h : p c
    . simp [span, h]
      exact Nat.le_add_right_of_le ih
    . simp [span, h]

/-- Lem:
    val lexer : forall 'a. Read 'a => (list char) -> either string (list (arith_token 'a)) -/
def lexer [Read α]: List Char → Sum String (List (arith_token α))
  | [] => Sum.inr []
  | '^' :: '=' :: cs => either_fmap (fun lst => .TVarBitXOrEq :: lst) (lexer cs)
  | '|' :: '=' :: cs => either_fmap (fun lst => .TVarBitOrEq  :: lst) (lexer cs)
  | '&' :: '=' :: cs => either_fmap (fun lst => .TVarBitAndEq :: lst) (lexer cs)
  | '>' :: '>' :: '=' :: cs => either_fmap (fun lst => .TVarRShiftEq :: lst) (lexer cs)
  | '<' :: '<' :: '=' :: cs => either_fmap (fun lst => .TVarLShiftEq :: lst) (lexer cs)
  | '%' :: '=' :: cs => either_fmap (fun lst => .TVarModEq   :: lst) (lexer cs)
  | '/' :: '=' :: cs => either_fmap (fun lst => .TVarDivEq   :: lst) (lexer cs)
  | '*' :: '=' :: cs => either_fmap (fun lst => .TVarTimesEq :: lst) (lexer cs)
  | '-' :: '=' :: cs => either_fmap (fun lst => .TVarMinusEq :: lst) (lexer cs)
  | '+' :: '=' :: cs => either_fmap (fun lst => .TVarPlusEq  :: lst) (lexer cs)

  | '=' :: '=' :: cs => either_fmap (fun lst => .TEq  :: lst) (lexer cs)
  | '!' :: '=' :: cs => either_fmap (fun lst => .TNEq :: lst) (lexer cs)

  | '>' :: '>' :: cs => either_fmap (fun lst => .TRShift :: lst) (lexer cs)
  | '<' :: '<' :: cs => either_fmap (fun lst => .TLShift :: lst) (lexer cs)
  | '&' :: '&' :: cs => either_fmap (fun lst => .TBoolAnd :: lst) (lexer cs)
  | '|' :: '|' :: cs => either_fmap (fun lst => .TBoolOr  :: lst) (lexer cs)

  | '=' :: cs => either_fmap (fun lst => .TVarEq    :: lst) (lexer cs)
  | ':' :: cs => either_fmap (fun lst => .TColon    :: lst) (lexer cs)
  | '?' :: cs => either_fmap (fun lst => .TQuestion :: lst) (lexer cs)

  | '^' :: cs => either_fmap (fun lst => .TBitXOr :: lst) (lexer cs)
  | '|' :: cs => either_fmap (fun lst => .TBitOr  :: lst) (lexer cs)
  | '&' :: cs => either_fmap (fun lst => .TBitAnd :: lst) (lexer cs)

  | '>' :: '=' :: cs => either_fmap (fun lst => .TGte :: lst) (lexer cs)
  | '<' :: '=' :: cs => either_fmap (fun lst => .TLte :: lst) (lexer cs)
  | '>' :: cs        => either_fmap (fun lst => .TGt  :: lst) (lexer cs)
  | '<' :: cs        => either_fmap (fun lst => .TLt  :: lst) (lexer cs)

  | '!' :: cs => either_fmap (fun lst => .TBoolNot :: lst) (lexer cs)
  | '~' :: cs => either_fmap (fun lst => .TBitNot  :: lst) (lexer cs)

  | '%' :: cs => either_fmap (fun lst => .TMod   :: lst) (lexer cs)
  | '/' :: cs => either_fmap (fun lst => .TDiv   :: lst) (lexer cs)
  | '*' :: cs => either_fmap (fun lst => .TTimes :: lst) (lexer cs)
  | '-' :: cs => either_fmap (fun lst => .TMinus :: lst) (lexer cs)
  | '+' :: cs => either_fmap (fun lst => .TPlus  :: lst) (lexer cs)

  | '(' :: cs => either_fmap (fun lst => .TLParen :: lst) (lexer cs)
  | ')' :: cs => either_fmap (fun lst => .TRParen :: lst) (lexer cs)

  | c :: cs =>
      match (isDigit c, is_variable_initial_char c) with
      | (true, _) =>
        match _h : span isNumConstChar cs with
        | (digits, rst) =>
          match Read.read (c :: digits) with
          | .ok n    => either_fmap (fun lst => .TNum n :: lst) (lexer rst)
          | .error e => Sum.inl e
      | (_, true) =>
        match _h : span is_variable_char cs with
        | (var, rst) =>
          either_fmap (fun lst => .TVar (toString (c :: var)) :: lst) (lexer rst)
      | (false, false) =>
          if isWhitespace c then
            lexer cs
          else
            Sum.inl (toString [c] ++ " is an unrecognized character")
termination_by
  s => s.length
decreasing_by
  repeat' (simp; omega)
  repeat' simp
  have hle : rst.length ≤ cs.length := by
      simpa [_h] using (span_snd_length_le (p := isNumConstChar) (xs := cs))
  exact Nat.lt_succ_of_le hle
  have hle : rst.length ≤ cs.length := by
      simpa [_h] using (span_snd_length_le (p := is_variable_char) (xs := cs))
  exact Nat.lt_succ_of_le hle

/-- Lem:
    val lexer_integer : (list char) -> either string (list (arith_token integer)) -/
def lexer_integer (cs : List Char) : Sum String (List (arith_token Int)) :=
  lexer cs

def outOfFuel : Sum String (arith_exp α × List (arith_token α)) :=
  Sum.inl "parser: out of fuel"

def defaultFuel (tkns : List (arith_token α)) : Nat :=
  tkns.length + 64

abbrev Fuel := Nat

mutual

  /-- Lem:
      val parse_assignment : forall 'a. (list (arith_token 'a)) -> either string ((arith_exp 'a) * list (arith_token 'a)) -/
  def parse_assignment :
      Fuel → List (arith_token α) → Sum String (arith_exp α × List (arith_token α))
    | 0,     _ => outOfFuel
    | .succ fuel, tkns =>
      match tkns with
      | (.TVar s :: .TVarEq :: rst) =>
          collect_assignment fuel (fun t => .AssignVar s none t) rst
      | (.TVar s :: .TVarPlusEq :: rst) =>
          collect_assignment fuel (fun t => .AssignVar s (some .Plus) t) rst
      | (.TVar s :: .TVarMinusEq :: rst) =>
          collect_assignment fuel (fun t => .AssignVar s (some .Minus) t) rst
      | (.TVar s :: .TVarTimesEq :: rst) =>
          collect_assignment fuel (fun t => .AssignVar s (some .Times) t) rst
      | (.TVar s :: .TVarDivEq :: rst) =>
          collect_assignment fuel (fun t => .AssignVar s (some .Div) t) rst
      | (.TVar s :: .TVarModEq :: rst) =>
          collect_assignment fuel (fun t => .AssignVar s (some .Mod) t) rst
      | (.TVar s :: .TVarLShiftEq :: rst) =>
          collect_assignment fuel (fun t => .AssignVar s (some .LShift) t) rst
      | (.TVar s :: .TVarRShiftEq :: rst) =>
          collect_assignment fuel (fun t => .AssignVar s (some .RShift) t) rst
      | (.TVar s :: .TVarBitAndEq :: rst) =>
          collect_assignment fuel (fun t => .AssignVar s (some .BitAnd) t) rst
      | (.TVar s :: .TVarBitOrEq :: rst) =>
          collect_assignment fuel (fun t => .AssignVar s (some .BitOr) t) rst
      | (.TVar s :: .TVarBitXOrEq :: rst) =>
          collect_assignment fuel (fun t => .AssignVar s (some .BitXOr) t) rst
      | tkns =>
          parse_conditional fuel tkns
  -- termination_by
  --   tkns             => (tkns.length, 24)
  -- decreasing_by
  --   repeat' (simp; omega)
  --   refine Prod.Lex.right tkns.length ?_; omega

  def collect_assignment :
      Fuel → (arith_exp α → arith_exp α) → List (arith_token α) →
      Sum String (arith_exp α × List (arith_token α))
    | 0,     _, _    => outOfFuel
    | .succ fuel, mk, tkns =>
      match parse_assignment fuel tkns with
      | Sum.inr (term, rst) => Sum.inr (mk term, rst)
      | Sum.inl e           => Sum.inl e
  -- termination_by
  --   _ tkns => (tkns.length, 25)
  -- decreasing_by
  --   refine Prod.Lex.right tkns.length ?_; exact Nat.lt_add_one 24

  def parse_conditional:
      Fuel → List (arith_token α) → Sum String (arith_exp α × List (arith_token α))
    | 0,     _    => outOfFuel
    | .succ fuel , tkns =>
        match parse_bool_or fuel tkns with
        | Sum.inr (term, rst) => first_conditional_term fuel term rst
        | Sum.inl e           => Sum.inl e
  -- termination_by
  --   tkns            => (tkns.length, 22)
  -- decreasing_by
  --   expose_names; refine Prod.Lex.right a.length ?_; omega
  --   apply?

  def first_conditional_term :
      Fuel → arith_exp α → List (arith_token α) →
      Sum String (arith_exp α × List (arith_token α))
    | 0,     _, _    => outOfFuel
    | .succ fuel, boolean, tkns =>
      match tkns with
      | .TQuestion :: rst1 =>
          match parse_conditional fuel rst1 with
          | Sum.inr (lhs, rst2) =>
              match second_conditional_term fuel rst2 with
              | Sum.inr (rhs, rst3) => Sum.inr (.Conditional boolean lhs rhs, rst3)
              | Sum.inl e           => Sum.inl e
          | Sum.inl e => Sum.inl e
      | _ =>
          Sum.inr (boolean, tkns)
  -- termination_by
  --   boolean tkns => (tkns.length, 21)
  -- decreasing_by
  --   refine Prod.Lex.left 22 21 ?_; exact Nat.lt_add_one rst1.length


  def second_conditional_term :
      Fuel → List (arith_token α) → Sum String (arith_exp α × List (arith_token α))
    | 0,      _    => outOfFuel
    | .succ fuel, (.TColon :: rst1) => parse_conditional fuel rst1
    | _,_               => Sum.inl "Expected ':'"
  -- termination_by
  --   tkns      => (tkns.length, 21)
  -- decreasing_by
  --   refine Prod.Lex.left 22 21 ?_; exact Nat.lt_add_one rst1.length

  def parse_bool_or :
      Fuel → List (arith_token α) → Sum String (arith_exp α × List (arith_token α))
    | 0,      _    => outOfFuel
    | .succ fuel, tkns =>
        match parse_bool_and fuel tkns with
        | Sum.inr (term, rst) => bool_or_term fuel term rst
        | Sum.inl e           => Sum.inl e
  -- termination_by
  --   tkns                => (tkns.length, 20)
  -- decreasing_by
  --   expose_names; refine Prod.Lex.right a.length ?_; omega


  def bool_or_term :
      Fuel → arith_exp α → List (arith_token α) →
      Sum String (arith_exp α × List (arith_token α))
    | 0,     _, _    => outOfFuel
    | .succ fuel, lhs, tkns =>
      match tkns with
      | .TBoolOr :: rst1 =>
          match parse_bool_and fuel rst1 with
          | Sum.inr (rhs, rst2) => bool_or_term fuel (.BinOp .BoolOr lhs rhs) rst2
          | Sum.inl e           => Sum.inl e
      | _ =>
          Sum.inr (lhs, tkns)
  -- termination_by
  --   lhs tkns => (tkns.length, 20)
  -- decreasing_by
  --   refine Prod.Lex.left 18 20 ?_; exact Nat.lt_add_one rst1.length

  def parse_bool_and :
      Fuel → List (arith_token α) → Sum String (arith_exp α × List (arith_token α))
    | 0,     _    => outOfFuel
    | .succ fuel, tkns =>
        match parse_bit_or fuel tkns with
        | Sum.inr (term, rst) => bool_and_term fuel term rst
        | Sum.inl e           => Sum.inl e
  -- termination_by
  --   tkns               => (tkns.length, 18)
  -- decreasing_by
  --   expose_names; refine Prod.Lex.right a.length ?_; omega


  def bool_and_term :
      Fuel → arith_exp α → List (arith_token α) →
      Sum String (arith_exp α × List (arith_token α))
    | 0,     _, _    => outOfFuel
    | .succ fuel, lhs, tkns =>
      match tkns with
      | .TBoolAnd :: rst1 =>
          match parse_bit_or fuel rst1 with
          | Sum.inr (rhs, rst2) => bool_and_term fuel (.BinOp .BoolAnd lhs rhs) rst2
          | Sum.inl e           => Sum.inl e
      | _ =>
          Sum.inr (lhs, tkns)
  -- termination_by
  --   lhs tkns => (tkns.length, 18)
  -- decreasing_by
  --   refine Prod.Lex.left 16 18 ?_; exact Nat.lt_add_one rst1.length

  def parse_bit_or :
      Fuel → List (arith_token α) → Sum String (arith_exp α × List (arith_token α))
    | 0,      _    => outOfFuel
    | .succ fuel, tkns =>
        match parse_bit_xor fuel tkns with
        | Sum.inr (term, rst) => bit_or_term fuel term rst
        | Sum.inl e           => Sum.inl e
  -- termination_by
  --   tkns                 => (tkns.length, 16)
  -- decreasing_by
  --   expose_names; refine Prod.Lex.right a.length ?_; omega

  def bit_or_term :
      Fuel → arith_exp α → List (arith_token α) →
      Sum String (arith_exp α × List (arith_token α))
    | 0,     _, _    => outOfFuel
    | .succ fuel, lhs, tkns =>
      match tkns with
      | .TBitOr :: rst1 =>
          match parse_bit_xor fuel rst1 with
          | Sum.inr (rhs, rst2) => bit_or_term fuel (.BinOp .BitOr lhs rhs) rst2
          | Sum.inl e           => Sum.inl e
      | _ =>
          Sum.inr (lhs, tkns)
  -- termination_by
  --   lhs tkns => (tkns.length, 16)
  -- decreasing_by
  --   refine Prod.Lex.left 14 16 ?_; exact Nat.lt_add_one rst1.length


  def parse_bit_xor :
      Fuel → List (arith_token α) → Sum String (arith_exp α × List (arith_token α))
    | 0,      _    => outOfFuel
    | .succ fuel, tkns =>
      match parse_bit_and fuel tkns with
      | Sum.inr (term, rst) => bit_xor_term fuel term rst
      | Sum.inl e           => Sum.inl e
  -- termination_by
  --   tkns => (tkns.length, 14)
  -- decreasing_by
  --   expose_names; refine Prod.Lex.right a.length ?_; omega


  def bit_xor_term :
      Fuel → arith_exp α → List (arith_token α) →
      Sum String (arith_exp α × List (arith_token α))
    | 0,     _, _    => outOfFuel
    | .succ fuel, lhs, tkns =>
      match tkns with
      | .TBitXOr :: rst1 =>
          match parse_bit_and fuel rst1 with
          | Sum.inr (rhs, rst2) => bit_xor_term fuel (.BinOp .BitXOr lhs rhs) rst2
          | Sum.inl e           => Sum.inl e
      | _ =>
          Sum.inr (lhs, tkns)
  -- termination_by
  --   lhs tkns => (tkns.length, 14)
  -- decreasing_by
  --   refine Prod.Lex.left 12 14 ?_; exact Nat.lt_add_one rst1.length


  def parse_bit_and :
      Fuel → List (arith_token α) → Sum String (arith_exp α × List (arith_token α))
    | 0,      _    => outOfFuel
    | .succ fuel, tkns =>
        match parse_equality fuel tkns with
        | Sum.inr (term, rst) => bit_and_term fuel term rst
        | Sum.inl e           => Sum.inl e
  -- termination_by
  --   tkns                => (tkns.length, 12)
  -- decreasing_by
  --   expose_names; refine Prod.Lex.right a.length ?_; omega

  def bit_and_term :
      Fuel → arith_exp α → List (arith_token α) →
      Sum String (arith_exp α × List (arith_token α))
    | 0,     _, _    => outOfFuel
    | .succ fuel, lhs, tkns =>
      match tkns with
      | .TBitAnd :: rst1 =>
          match parse_equality fuel rst1 with
          | Sum.inr (rhs, rst2) => bit_and_term fuel (.BinOp .BitAnd lhs rhs) rst2
          | Sum.inl e           => Sum.inl e
      | _ =>
          Sum.inr (lhs, tkns)
  -- termination_by
  --   lhs tkns => (tkns.length, 12)
  -- decreasing_by
  --   refine Prod.Lex.left 10 12 ?_; exact Nat.lt_add_one rst1.length


  def parse_equality :
      Fuel → List (arith_token α) → Sum String (arith_exp α × List (arith_token α))
    | 0,      _    => outOfFuel
    | .succ fuel, tkns =>
        match parse_relational fuel tkns with
        | Sum.inr (term, rst) => equality_term fuel term rst
        | Sum.inl e           => Sum.inl e
  -- termination_by
  --   tkns               => (tkns.length, 10)
  -- decreasing_by
  --   expose_names; refine Prod.Lex.right a.length ?_; omega

  def equality_term :
      Fuel → arith_exp α → List (arith_token α) →
      Sum String (arith_exp α × List (arith_token α))
    | 0,     _, _    => outOfFuel
    | .succ fuel, lhs, tkns =>
      match tkns with
      | .TEq :: rst  => collect_equality fuel (fun rhs => .BinOp .Eq  lhs rhs) rst
      | .TNEq :: rst => collect_equality fuel (fun rhs => .BinOp .NEq lhs rhs) rst
      | _            => Sum.inr (lhs, tkns)
  -- termination_by
  --   lhs tkns => (tkns.length, 10)
  -- decreasing_by
  --   repeat' (refine Prod.Lex.left 11 10 ?_; exact Nat.lt_add_one rst.length)


  def collect_equality :
      Fuel → (arith_exp α → arith_exp α) → List (arith_token α) →
      Sum String (arith_exp α × List (arith_token α))
    | 0,     _, _    => outOfFuel
    | .succ fuel, mk, tkns =>
      match parse_relational fuel tkns with
      | Sum.inr (term, rst) => equality_term fuel (mk term) rst
      | Sum.inl e           => Sum.inl e
  -- termination_by
  --   _ tkns => (tkns.length, 11)
  -- decreasing_by
  --   expose_names; refine Prod.Lex.right tkns.length ?_; omega


  def parse_relational :
      Fuel → List (arith_token α) → Sum String (arith_exp α × List (arith_token α))
    | 0,      _    => outOfFuel
    | .succ fuel, tkns =>
        match parse_bit_shift fuel tkns with
        | Sum.inr (term, rst) => relational_term fuel term rst
        | Sum.inl e           => Sum.inl e
  -- termination_by
  --   tkns             => (tkns.length, 8)
  -- decreasing_by
  --   expose_names; refine Prod.Lex.right a.length ?_; omega

  def relational_term :
      Fuel → arith_exp α → List (arith_token α) →
      Sum String (arith_exp α × List (arith_token α))
    | 0,     _, _    => outOfFuel
    | .succ fuel, lhs, tkns =>
      match tkns with
      | .TLt  :: rst => collect_relational fuel (fun rhs => .BinOp .Lt  lhs rhs) rst
      | .TLte :: rst => collect_relational fuel (fun rhs => .BinOp .Lte lhs rhs) rst
      | .TGt  :: rst => collect_relational fuel (fun rhs => .BinOp .Gt  lhs rhs) rst
      | .TGte :: rst => collect_relational fuel (fun rhs => .BinOp .Gte lhs rhs) rst
      | _            => Sum.inr (lhs, tkns)
  -- termination_by
  --   lhs tkns => (tkns.length, 8)
  -- decreasing_by
  --   repeat' (refine Prod.Lex.left 9 8 ?_; exact Nat.lt_add_one rst.length)


  def collect_relational :
      Fuel → (arith_exp α → arith_exp α) → List (arith_token α) →
      Sum String (arith_exp α × List (arith_token α))
    | 0,     _, _    => outOfFuel
    | .succ fuel, mk, tkns =>
      match parse_bit_shift fuel tkns with
      | Sum.inr (term, rst) => relational_term fuel (mk term) rst
      | Sum.inl e           => Sum.inl e
  -- termination_by
  --   _ tkns => (tkns.length, 9)
  -- decreasing_by
  --   expose_names; refine Prod.Lex.right tkns.length ?_; omega


/-- Lem:
    val parse_bit_shift : forall 'a. (list (arith_token 'a)) ->
    either string ((arith_exp 'a) * list (arith_token 'a)) -/
  def parse_bit_shift :
      Fuel → List (arith_token α) → Sum String (arith_exp α × List (arith_token α))
    | 0,      _    => outOfFuel
    | .succ fuel, tkns =>
        match parse_additive fuel tkns with
        | Sum.inr (term, rst) => shift_term fuel term rst
        | Sum.inl e           => Sum.inl e
  -- termination_by
  --   tkns              => (tkns.length, 6)
  -- decreasing_by
  --   expose_names; refine Prod.Lex.right a.length ?_; omega

/-- Lem:
    val shift_term : forall 'a. (arith_exp 'a) ->
    (list (arith_token 'a)) -> either string ((arith_exp 'a) * list (arith_token 'a)) -/
  def shift_term :
      Fuel → arith_exp α → List (arith_token α) →
      Sum String (arith_exp α × List (arith_token α))
    | 0,     _, _    => outOfFuel
    | .succ fuel, lhs, tkns =>
      match tkns with
      | .TLShift :: rst => collect_shift fuel (fun rhs => .BinOp .LShift lhs rhs) rst
      | .TRShift :: rst => collect_shift fuel (fun rhs => .BinOp .RShift lhs rhs) rst
      | _              => Sum.inr (lhs, tkns)
  -- termination_by
  --   lhs tkns => (tkns.length, 6)
  -- decreasing_by
  --   repeat' (refine Prod.Lex.left 7 6 ?_; exact Nat.lt_add_one rst.length)


/-- Lem:
    val collect_shift : forall 'a. ((arith_exp 'a) ->
    (arith_exp 'a)) -> (list (arith_token 'a)) -> either string ((arith_exp 'a) * list (arith_token 'a)) -/
  def collect_shift :
      Fuel → (arith_exp α → arith_exp α) → List (arith_token α) →
      Sum String (arith_exp α × List (arith_token α))
    | 0,     _, _    => outOfFuel
    | .succ fuel, mk, tkns =>
      match parse_additive fuel tkns with
      | Sum.inr (term, rst) => shift_term fuel (mk term) rst
      | Sum.inl e           => Sum.inl e
  -- termination_by
  --   _ tkns => (tkns.length, 7)
  -- decreasing_by
  --   expose_names; refine Prod.Lex.right tkns.length ?_; omega

/-- Lem:
    val parse_additive : forall 'a. (list (arith_token 'a)) ->
    either string ((arith_exp 'a) * list (arith_token 'a)) -/
  def parse_additive :
      Fuel → List (arith_token α) → Sum String (arith_exp α × List (arith_token α))
    | 0,      _    => outOfFuel
    | .succ fuel, tkns =>
        match parse_multiplicative fuel tkns with
        | Sum.inr (term, rst) => additive_term fuel term rst
        | Sum.inl e           => Sum.inl e
  -- termination_by
  --   tkns               => (tkns.length, 4)
  -- decreasing_by
  --   expose_names; refine Prod.Lex.right a.length ?_; omega

/-- Lem:
    val additive_term : forall 'a. (arith_exp 'a) ->
    (list (arith_token 'a)) -> either string ((arith_exp 'a) * list (arith_token 'a)) -/
  def additive_term :
      Fuel → arith_exp α → List (arith_token α) →
      Sum String (arith_exp α × List (arith_token α))
    | 0,     _, _    => outOfFuel
    | .succ fuel, lhs, tkns =>
      match tkns with
      | .TPlus  :: rst => collect_additive fuel (fun rhs => .BinOp .Plus  lhs rhs) rst
      | .TMinus :: rst => collect_additive fuel (fun rhs => .BinOp .Minus lhs rhs) rst
      | _             => Sum.inr (lhs, tkns)
  -- termination_by
  --   lhs tkns => (tkns.length, 4)
  -- decreasing_by
  --   repeat' (refine Prod.Lex.left 5 4 ?_; exact Nat.lt_add_one rst.length)

/-- Lem:
    val collect_additive : forall 'a. ((arith_exp 'a) ->
    (arith_exp 'a)) -> (list (arith_token 'a)) -> either string ((arith_exp 'a) * list (arith_token 'a)) -/
  def collect_additive :
      Fuel → (arith_exp α → arith_exp α) → List (arith_token α) →
      Sum String (arith_exp α × List (arith_token α))
    | 0,     _, _    => outOfFuel
    | .succ fuel, mk, tkns =>
      match parse_multiplicative fuel tkns with
      | Sum.inr (term, rst) => additive_term fuel (mk term) rst
      | Sum.inl e           => Sum.inl e
  -- termination_by
  --   _ tkns => (tkns.length, 5)
  -- decreasing_by
  --   expose_names; refine Prod.Lex.right tkns.length ?_; omega


/-- Lem:
    val parse_multiplicative : forall 'a. (list (arith_token 'a)) ->
    either string ((arith_exp 'a) * list (arith_token 'a)) -/
  def parse_multiplicative :
      Fuel → List (arith_token α) → Sum String (arith_exp α × List (arith_token α))
    | 0,      _    => outOfFuel
    | .succ fuel, tkns =>
        match unary_term fuel tkns with
        | Sum.inr (term, rst) => multiplicative_term fuel term rst
        | Sum.inl e           => Sum.inl e
  -- termination_by
  --   tkns         => (tkns.length, 2)
  -- decreasing_by
  --   expose_names; refine Prod.Lex.right a.length ?_; omega

/-- Lem:
    val multiplicative_term : forall 'a. (arith_exp 'a) ->
    (list (arith_token 'a)) -> either string ((arith_exp 'a) * list (arith_token 'a)) -/
  def multiplicative_term :
      Fuel → arith_exp α → List (arith_token α) →
      Sum String (arith_exp α × List (arith_token α))
    | 0,     _, _    => outOfFuel
    | .succ fuel, lhs, tkns =>
      match tkns with
      | .TTimes :: rst => collect_multiplicative fuel (fun rhs => .BinOp .Times lhs rhs) rst
      | .TDiv   :: rst => collect_multiplicative fuel (fun rhs => .BinOp .Div   lhs rhs) rst
      | .TMod   :: rst => collect_multiplicative fuel (fun rhs => .BinOp .Mod   lhs rhs) rst
      | _             => Sum.inr (lhs, tkns)
  -- termination_by
  --   lhs tkns => (tkns.length, 2)
  -- decreasing_by
  --   repeat' (refine Prod.Lex.left 3 2 ?_; exact Nat.lt_add_one rst.length)

/-- Lem:
    val collect_multiplicative : forall 'a. ((arith_exp 'a) ->
    (arith_exp 'a)) -> (list (arith_token 'a)) -> either string ((arith_exp 'a) * list (arith_token 'a)) -/
  def collect_multiplicative :
      Fuel → (arith_exp α → arith_exp α) → List (arith_token α) →
      Sum String (arith_exp α × List (arith_token α))
    | 0,     _, _    => outOfFuel
    | .succ fuel, mk, tkns =>
      match unary_term fuel tkns with
      | Sum.inr (term, rst) => multiplicative_term fuel (mk term) rst
      | Sum.inl e           => Sum.inl e
  -- termination_by
  --   _ tkns => (tkns.length, 3)
  -- decreasing_by
  --   expose_names; refine Prod.Lex.right tkns.length ?_; omega


  def unary_term :
      Fuel → List (arith_token α) → Sum String (arith_exp α × List (arith_token α))
    | 0,      _    => outOfFuel
    | .succ fuel, tkns =>
        match tkns with
        | (.TPlus :: ts) =>
            unary_term fuel ts
        | (.TMinus :: ts) =>
            match unary_term fuel ts with
            | Sum.inr (term, rst) => Sum.inr (.Neg term, rst)
            | Sum.inl e           => Sum.inl e
        | (.TBitNot :: ts) =>
            match unary_term fuel ts with
            | Sum.inr (term, rst) => Sum.inr (.BitNot term, rst)
            | Sum.inl e           => Sum.inl e
        | (.TBoolNot :: ts) =>
            match unary_term fuel ts with
            | Sum.inr (term, rst) => Sum.inr (.BoolNot term, rst)
            | Sum.inl e           => Sum.inl e
        | tkns =>
            number_term fuel tkns
  -- termination_by
  --   tkns                   => (tkns.length, 1)
  -- decreasing_by
  --   repeat' (refine Prod.Lex.left 1 1 ?_; exact Nat.lt_add_one ts.length)
  --   expose_names; refine Prod.Lex.right tkns.length ?_; omega

  def number_term :
      Fuel → List (arith_token α) → Sum String (arith_exp α × List (arith_token α))
    | 0,      _    => outOfFuel
    | .succ _fuel, (.TNum n :: ts) => Sum.inr (.Num n, ts)
    | .succ _fuel, (.TVar s :: ts) => Sum.inr (.Var s, ts)
    | .succ fuel, (.TLParen :: ts) =>
        match parse_assignment fuel ts with
        | Sum.inr (term, .TRParen :: ts1) => Sum.inr (term, ts1)
        | Sum.inr (_term, _ts)           => Sum.inl "Expected right paren found "
        | Sum.inl e                      => Sum.inl e
    | _, _ =>
        Sum.inl "Expected number or (expr) found"
  -- termination_by
  --   tkns                  => (tkns.length, 0)
  -- decreasing_by
  --   simp
  --   refine Prod.Lex.left 24 0 ?_
  --   exact Nat.lt_add_one ts.length

end

def collect_bit_and
      (fuel : Fuel) (mk : arith_exp α → arith_exp α) (tkns : List (arith_token α)) :
      Sum String (arith_exp α × List (arith_token α)) :=
    match parse_equality fuel tkns with
    | Sum.inr (term, rst) => bit_and_term fuel (mk term) rst
    | Sum.inl e           => Sum.inl e

open Smoosh.Num

/-
val parse_arith_exp : forall 'a. list (arith_token 'a) -> either string (arith_exp 'a)
-/
def parse_arith_exp {α : Type u}
    (fuel : Nat) (tkns : List (arith_token α)) : Sum String (arith_exp α) :=
  match parse_assignment (α := α) fuel tkns with
  | Sum.inr (expr, []) => Sum.inr expr
  | Sum.inr (_, _ts)   => Sum.inl "Expected EOF but found tokens"
  | Sum.inl e          => Sum.inl e
-- def parse_arith_exp {α : Type u} (tkns : List (arith_token α)) : Sum String (arith_exp α) :=
--   match parse_assignment (α := α) tkns with
--   | Sum.inr (expr, [])   => Sum.inr expr
--   | Sum.inr (_, _ts)     => Sum.inl "Expected EOF but found tokens"
--   | Sum.inl e            => Sum.inl e

/-
val bool_to_num : forall 'a. Nat 'a => bool -> 'a
-/
def bool_to_num {α : Type u} [NatConv α] (b : Bool) : α :=
  if b then NatConv.ofNat 1 else NatConv.ofNat 0

def exceptToSum {α : Type u} : Except String α → Sum String α
  | .ok a    => Sum.inr a
  | .error e => Sum.inl e

abbrev beq [DecidableEq α] (a b : α) : Bool := decide (a = b)
abbrev bne [DecidableEq α] (a b : α) : Bool := decide (a ≠ b)
abbrev blt [LT α] [DecidableRel (fun x y : α => x < y)] (a b : α) : Bool :=
  decide (a < b)
abbrev ble [LE α] [DecidableRel (fun x y : α => x ≤ y)] (a b : α) : Bool :=
  decide (a ≤ b)
abbrev bgt [LT α] [DecidableRel (fun x y : α => x < y)] (a b : α) : Bool :=
  decide (b < a)
abbrev bge [LE α] [DecidableRel (fun x y : α => x ≤ y)] (a b : α) : Bool :=
  decide (b ≤ a)
abbrev lsl [HShiftLeft α Nat α] (x : α) (n : Nat) : α :=
  HShiftLeft.hShiftLeft x n
abbrev asr [HShiftRight α Nat α] (x : α) (n : Nat) : α :=
  HShiftRight.hShiftRight x n
abbrev land [HAnd α α α] (x y : α) : α :=
  HAnd.hAnd x y
abbrev lor [HOr α α α] (x y : α) : α :=
  HOr.hOr x y
abbrev lxor [HXor α α α] (x y : α) : α :=
  HXor.hXor x y
abbrev lnot [Complement α] (x : α) : α :=
  Complement.complement x

def eval_binop
    {α : Type u}
    [DecidableEq α]
    [LT α] [LE α]
    [DecidableRel (fun x y : α => x < y)]
    [DecidableRel (fun x y : α => x ≤ y)]
    [HAdd α α α] [HSub α α α] [HMul α α α]
    [HDiv α α α] [HMod α α α]
    [Neg α]
    [HShiftLeft  α Nat α] [HShiftRight α Nat α]
    [HAnd α α α] [HOr α α α] [HXor α α α] [Complement α]
    [Smoosh.Num.NatConv α]
    (bits : α) (op : BinaryOperator) (n1 n2 : α)
    : Sum String α :=
  match op with
  | .Plus  => Sum.inr (n1 + n2)
  | .Minus => Sum.inr (n1 - n2)
  | .Times => Sum.inr (n1 * n2)
  | .Div =>
      if beq n2 (NatConv.ofNat 0) then
        Sum.inl "Divide by zero"
      else
        Sum.inr (n1 / n2)
  | .Mod =>
      Sum.inr (n1 % n2)
  | .LShift =>
      if beq bits (-(NatConv.ofNat 1)) then
        Sum.inr (lsl n1 (NatConv.toNat n2))
      else
        Sum.inr (lsl n1 (NatConv.toNat (n2 % bits)))
  | .RShift =>
      if beq bits (-(NatConv.ofNat 1)) then
        Sum.inr (asr n1 (NatConv.toNat n2))
      else
        Sum.inr (asr n1 (NatConv.toNat (n2 % bits)))
  | .Lt  => Sum.inr (bool_to_num (blt n1 n2))
  | .Lte => Sum.inr (bool_to_num (ble n1 n2))
  | .Gt  => Sum.inr (bool_to_num (bgt n1 n2))
  | .Gte => Sum.inr (bool_to_num (bge n1 n2))
  | .Eq  => Sum.inr (bool_to_num (beq n1 n2))
  | .NEq => Sum.inr (bool_to_num (bne n1 n2))
  | .BitAnd => Sum.inr (land n1 n2)
  | .BitOr  => Sum.inr (lor n1 n2)
  | .BitXOr => Sum.inr (lxor n1 n2)
  | .BoolAnd =>
      Sum.inr (bool_to_num (bne n1 (NatConv.ofNat 0) && bne n2 (NatConv.ofNat 0)))
  | .BoolOr =>
      Sum.inr (bool_to_num (bne n1 (NatConv.ofNat 0) || bne n2 (NatConv.ofNat 0)))

/-- Lem:
    val eval_arith : forall 'a 'b.
    Read 'a, Nat 'a, Eq 'a, Ord 'a, NumAdd 'a, NumMinus 'a, NumMult 'a, NumIntegerDivision 'a,
    NumRemainder 'a, NumPow 'a, NumNegate 'a, WordLsl 'a, WordLsr 'a, WordAsr 'a, WordNot 'a, WordAnd 'a, WordOr 'a, WordXor 'a, OS 'b
      => 'a -> os_state 'b -> arith_exp 'a -> either string (os_state 'b * 'a) -/
def eval_arith
    {α : Type u} {β : Type v}
    [Smoosh.Num.Read α] [Smoosh.Num.NatConv α]
    [DecidableEq α]
    [LT α] [LE α]
    [DecidableRel (fun x y : α => x < y)]
    [DecidableRel (fun x y : α => x ≤ y)]
    [HAdd α α α] [HSub α α α] [HMul α α α]
    [HDiv α α α] [HMod α α α]
    [Neg α]
    [HShiftLeft  α Nat α] [HShiftRight α Nat α]
    [HAnd α α α] [HOr α α α] [HXor α α α] [Complement α]
    [OS β]
    (bits : α) (s0 : os_state β) (e : arith_exp α)
    : Sum String (os_state β × α) :=
  match e with
  | .Num n => Sum.inr (s0, n)
  | .Var s =>
      match lookup_concrete_param s0 s with
      | .error e => Sum.inl e
      | .ok (some "") =>
          let s1 :=
            log_trace .Trace_unspec
              ("used null variable '" ++ s ++ "' in arithmetic expansion, treating as 0") s0
          Sum.inr (s1, NatConv.ofNat 0)
      | .ok (some str) =>
          match exceptToSum (Read.read (toCharList str)) with
          | Sum.inr n => Sum.inr (s0, n)
          | Sum.inl e => Sum.inl e
      | .ok none =>
          if Set.Set.member .Sh_nounset s0.sh.opts then
            Sum.inl (s ++ ": parameter unset")
          else
            Sum.inr (s0, NatConv.ofNat 0)
  | .BinOp op e1 e2 =>
      match eval_arith bits s0 e1 with
      | Sum.inl e => Sum.inl e
      | Sum.inr (s1, n1) =>
          match eval_arith bits s1 e2 with
          | Sum.inl e => Sum.inl e
          | Sum.inr (s2, n2) =>
              match eval_binop bits op n1 n2 with
              | Sum.inl e  => Sum.inl e
              | Sum.inr r  => Sum.inr (s2, r)
  | .Neg exp =>
      match eval_arith bits s0 exp with
      | Sum.inr (s1, n) => Sum.inr (s1, -n)
      | Sum.inl e       => Sum.inl e
  | .BitNot exp =>
      match eval_arith bits s0 exp with
      | Sum.inr (s1, n) => Sum.inr (s1, lnot n)
      | Sum.inl e       => Sum.inl e
  | .BoolNot exp =>
      match eval_arith bits s0 exp with
      | Sum.inl e => Sum.inl e
      | Sum.inr (s1, n) =>
          Sum.inr (s1, if bne n (NatConv.ofNat 0) then NatConv.ofNat 0 else NatConv.ofNat 1)
  | .Conditional a1 a2 a3 =>
      match eval_arith bits s0 a1 with
      | Sum.inl e => Sum.inl e
      | Sum.inr (s1, n) =>
          if bne n (NatConv.ofNat 0) then
            eval_arith bits s1 a2
          else
            eval_arith bits s1 a3
  | .AssignVar s op exp =>
      match op with
      | some o =>
          match lookup_concrete_param s0 s with
          | .error e => Sum.inl e
          | .ok (some str) =>
              match exceptToSum (Read.read (toCharList str)) with
              | Sum.inl e => Sum.inl e
              | Sum.inr n =>
                  -- 关键：不再构造 (.BinOp o (.Num n) exp) 去递归
                  match eval_arith bits s0 exp with
                  | Sum.inl e => Sum.inl e
                  | Sum.inr (s1, nExp) =>
                      match eval_binop bits o n nExp with
                      | Sum.inl e => Sum.inl e
                      | Sum.inr n2 =>
                          match set_param s (symbolic_string_of_string (Read.write n2)) s1 with
                          | .error e => Sum.inl e
                          | .ok s2   => Sum.inr (s2, n2)
          | .ok none =>
              Sum.inl ("Unbound or symbolic variable: " ++ s)
      | none =>
          match eval_arith (α := α) (β := β) bits s0 exp with
          | Sum.inl e => Sum.inl e
          | Sum.inr (s1, n) =>
              match set_param s (symbolic_string_of_string (Read.write (α := α) n)) s1 with
              | .error e => Sum.inl e
              | .ok s2   => Sum.inr (s2, n)

-- partial def eval_arith
--     {α : Type u} {β : Type v}
--     [Smoosh.Num.Read α] [Smoosh.Num.NatConv α]
--     [DecidableEq α]
--     [LT α] [LE α]
--     [DecidableRel (fun x y : α => x < y)]
--     [DecidableRel (fun x y : α => x ≤ y)]
--     [HAdd α α α] [HSub α α α] [HMul α α α]
--     [HDiv α α α] [HMod α α α]
--     [Neg α]
--     [HShiftLeft  α Nat α] [HShiftRight α Nat α]
--     [HAnd α α α] [HOr α α α] [HXor α α α] [Complement α]
--     [OS β]
--     (bits : α) (s0 : os_state β) (e : arith_exp α)
--     : Sum String (os_state β × α) :=
--   match e with
--   | .Num n =>
--       Sum.inr (s0, n)

--   | .Var s =>
--       match lookup_concrete_param s0 s with
--       | .error e => Sum.inl e
--       | .ok (some "") =>
--           let s1 :=
--             log_trace .Trace_unspec
--               ("used null variable '" ++ s ++ "' in arithmetic expansion, treating as 0") s0
--           Sum.inr (s1, fromNat 0)

--       | .ok (some str) =>
--           match exceptToSum (Read.read (α := α) (toCharList str)) with
--           | Sum.inr n => Sum.inr (s0, n)
--           | Sum.inl e => Sum.inl e

--       | .ok none =>
--           if Set.Set.member .Sh_nounset s0.sh.opts then
--             Sum.inl (s ++ ": parameter unset")
--           else
--             Sum.inr (s0, fromNat 0)

--   | .BinOp op e1 e2 =>
--       match eval_arith (α := α) (β := β) bits s0 e1 with
--       | Sum.inl e => Sum.inl e
--       | Sum.inr (s1, n1) =>
--           match eval_arith (α := α) (β := β) bits s1 e2 with
--           | Sum.inl e => Sum.inl e
--           | Sum.inr (s2, n2) =>
--               match op with
--               | .Plus  => Sum.inr (s2, n1 + n2)
--               | .Minus => Sum.inr (s2, n1 - n2)
--               | .Times => Sum.inr (s2, n1 * n2)

--               | .Div =>
--                   if beq n2 (fromNat 0) then
--                     Sum.inl "Divide by zero"
--                   else
--                     Sum.inr (s2, n1 / n2)

--               | .Mod =>
--                   Sum.inr (s2, n1 % n2)

--               | .LShift =>
--                   if beq bits (-(fromNat 1)) then
--                     Sum.inr (s2, lsl n1 (toNat n2))
--                   else
--                     Sum.inr (s2, lsl n1 (toNat (n2 % bits)))

--               | .RShift =>
--                   if beq bits (-(fromNat 1)) then
--                     Sum.inr (s2, asr n1 (toNat n2))
--                   else
--                     Sum.inr (s2, asr n1 (toNat (n2 % bits)))

--               | .Lt  => Sum.inr (s2, bool_to_num (blt n1 n2))
--               | .Lte => Sum.inr (s2, bool_to_num (ble n1 n2))
--               | .Gt  => Sum.inr (s2, bool_to_num (bgt n1 n2))
--               | .Gte => Sum.inr (s2, bool_to_num (bge n1 n2))

--               | .Eq  => Sum.inr (s2, bool_to_num (beq n1 n2))
--               | .NEq => Sum.inr (s2, bool_to_num (bne n1 n2))

--               | .BitAnd => Sum.inr (s2, land n1 n2)
--               | .BitOr  => Sum.inr (s2, lor n1 n2)
--               | .BitXOr => Sum.inr (s2, lxor n1 n2)

--               | .BoolAnd =>
--                   Sum.inr (s2, bool_to_num (bne n1 (fromNat 0) && bne n2 (fromNat 0)))

--               | .BoolOr =>
--                   Sum.inr (s2, bool_to_num (bne n1 (fromNat 0) || bne n2 (fromNat 0)))

--   | .Neg exp =>
--       match eval_arith (α := α) (β := β) bits s0 exp with
--       | Sum.inr (s1, n) => Sum.inr (s1, -n)
--       | Sum.inl e       => Sum.inl e

--   | .BitNot exp =>
--       match eval_arith (α := α) (β := β) bits s0 exp with
--       | Sum.inr (s1, n) => Sum.inr (s1, lnot n)
--       | Sum.inl e       => Sum.inl e

--   | .BoolNot exp =>
--       match eval_arith (α := α) (β := β) bits s0 exp with
--       | Sum.inl e => Sum.inl e
--       | Sum.inr (s1, n) =>
--           Sum.inr (s1, if bne n (fromNat 0) then fromNat 0 else fromNat 1)

--   | .Conditional a1 a2 a3 =>
--       match eval_arith (α := α) (β := β) bits s0 a1 with
--       | Sum.inl e => Sum.inl e
--       | Sum.inr (s1, n) =>
--           if bne n (fromNat 0) then
--             eval_arith (α := α) (β := β) bits s1 a2
--           else
--             eval_arith (α := α) (β := β) bits s1 a3

--   | .AssignVar s op exp =>
--       match op with
--       | some o =>
--           match lookup_concrete_param s0 s with
--           | .error e => Sum.inl e
--           | .ok (some str) =>
--               match exceptToSum (Read.read (α := α) (toCharList str)) with
--               | Sum.inl e => Sum.inl e
--               | Sum.inr n =>
--                   match eval_arith (α := α) (β := β) bits s0 (.BinOp o (.Num n) exp) with
--                   | Sum.inl e => Sum.inl e
--                   | Sum.inr (s1, n2) =>
--                       match set_param s (symbolic_string_of_string (Read.write (α := α) n2)) s1 with
--                       | .error e  => Sum.inl e
--                       | .ok s2 => Sum.inr (s2, n2)
--           | .ok none =>
--               Sum.inl ("Unbound or symbolic variable: " ++ s)

--       | none =>
--           match eval_arith (α := α) (β := β) bits s0 exp with
--           | Sum.inl e => Sum.inl e
--           | Sum.inr (s1, n) =>
--               match set_param s (symbolic_string_of_string (Read.write (α := α) n)) s1 with
--               | .error e  => Sum.inl e
--               | .ok s2 => Sum.inr (s2, n)

/-- Lem:
    val arith : forall 'a 'b. Read 'a, Nat 'a, Eq 'a, Ord 'a, NumAdd 'a, NumMinus 'a, NumMult 'a, NumIntegerDivision 'a,
    NumRemainder 'a, NumPow 'a, NumNegate 'a, WordLsl 'a, WordLsr 'a, WordAsr 'a, WordNot 'a, WordAnd 'a, WordOr 'a, WordXor 'a, OS 'b
    => 'a -> os_state 'b -> symbolic_string -> either string (os_state 'b * fields)

-/
def arith
    {α : Type u} {β : Type v}
    [Smoosh.Num.Read α] [Smoosh.Num.NatConv α]
    [DecidableEq α]
    [LT α] [LE α]
    [DecidableRel (fun x y : α => x < y)]
    [DecidableRel (fun x y : α => x ≤ y)]
    [HAdd α α α] [HSub α α α] [HMul α α α]
    [HDiv α α α] [HMod α α α]
    [Neg α]
    [HShiftLeft  α Nat α] [HShiftRight α Nat α]
    [HAnd α α α] [HOr α α α] [HXor α α α] [Complement α]
    [OS β]
    (bits : α) (s0 : os_state β) (str : symbolic_string) (fuel : Fuel)
    : Sum String (os_state β × fields) :=
  match try_concrete str with
  | some cstr =>
      match either_monad (parse_arith_exp fuel) (lexer (toCharList cstr)) with
      | Sum.inr aexp =>
          match eval_arith bits s0 aexp with
          | Sum.inr (s1, v) => Sum.inr (s1, [(List.map .C (toCharList (Read.write v)))])
          | Sum.inl e => Sum.inl ("arithmetic parse error on " ++ cstr ++ ": " ++ e)
      | Sum.inl e => Sum.inl ("arithmetic parsing error on " ++ cstr ++ ": " ++ e)
  | none =>
      Sum.inr (s0, [[.Sym (.SymArith (fields_of_symbolic_string str))]])

/-- Lem:
    val arith64 : forall 'a. OS 'a
    => os_state 'a -> symbolic_string -> either string (os_state 'a * fields)
-/
def arith64 [OS β] (fuel : Fuel):
    os_state β → symbolic_string → Sum String (os_state β × fields) :=
  letI : HShiftLeft Int64 Nat Int64 :=
    ⟨fun x n => x.shiftLeft (NatConv.ofNat (α := Int64) n)⟩
  letI : HShiftRight Int64 Nat Int64 :=
    ⟨fun x n => x.shiftRight (NatConv.ofNat (α := Int64) n)⟩
  arith (α := Int64) (β := β) (NatConv.ofNat (α := Int64) 64) (fuel := fuel)


end Smoosh.Num
