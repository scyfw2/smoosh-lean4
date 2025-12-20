import Std
namespace Smoosh.Compat

universe u
/-
A tiny compatibility layer. We will add helpers here only when the port
from Lem needs them; prefer Lean's Std library when possible.
-/

variable{α β: Type u}

def Option.toList : Option α → List α
  | none   => []
  | some a => [a]

def List.assoc? [DecidableEq α] (k : α) : List (α × β) → Option β
  | [] => none
  | (k', v) :: xs => if k = k' then some v else assoc? k xs

def List.updateAssoc [DecidableEq α] (k : α) (v : β) : List (α × β) → List (α × β)
  | [] => [(k, v)]
  | (k', v') :: xs =>
      if k = k' then (k, v) :: xs else (k', v') :: updateAssoc k v xs

end Smoosh.Compat
