namespace Smoosh.Syntax

/-- substring_mode in Lem -/
inductive SubstringMode where
  | shortest
  | longest
  deriving DecidableEq, Repr

/-- substring_side in Lem -/
inductive SubstringSide where
  | prefix
  | suffix
  deriving DecidableEq, Repr

/-
We start with a *stub* for Stmt just to break the cycle:
`sym` has `SymCommand of stmt` in Lem.

Next step (after this builds): replace `Stmt` with the full AST.
-/
mutual
  inductive Stmt : Type where
    | stub : Stmt
    deriving Repr

  inductive Sym : Type where
    | symArith   : Fields -> Sym
    | symCommand : Stmt -> Sym
    | symPat     : SubstringSide -> SubstringMode -> SymbolicString -> SymbolicString -> Sym
    deriving Repr

  inductive SymbolicChar : Type where
    | c   : Char -> SymbolicChar
    | sym : Sym  -> SymbolicChar
    deriving Repr
end

/-- symbolic_string = list symbolic_char -/
abbrev SymbolicString : Type := List SymbolicChar

/-- fields = list symbolic_string -/
abbrev Fields : Type := List SymbolicString

end Smoosh.Syntax
