-- Smoosh/Prelude/Set.lean
-- Lem-style finite Set, executable, backed by List (deduplicated).

namespace Smoosh.Set

universe u v

/-- Executable finite set backed by a list.
    Invariant (maintained by constructors below): no duplicates. -/
structure Set (α : Type u) where
  elems : List α
deriving Repr, Nonempty, DecidableEq

namespace Set

variable {α : Type u}

@[simp] def empty : Set α := ⟨[]⟩

@[simp] def singleton (a : α) : Set α := ⟨[a]⟩

/-- Boolean emptiness test (Lem: `null`). -/
def null (s : Set α) : Bool :=
  match s.elems with
  | [] => true
  | _  => false

/-- Boolean membership (no Std, no BEq required). -/
def member [DecidableEq α] (a : α) : Set α → Bool
  | ⟨[]⟩ => false
  | ⟨x :: xs⟩ =>
      if x = a then true else member a ⟨xs⟩

/-- Delete an element (remove all occurrences; keeps invariant). -/
def delete [DecidableEq α] (a : α) (s : Set α) : Set α :=
  ⟨s.elems.filter (fun x => decide (x ≠ a))⟩

/-- Insert an element (overwrites by removing old then cons). -/
def insert [DecidableEq α] (a : α) (s : Set α) : Set α :=
  ⟨a :: (delete a s).elems⟩

/-- Union (Lem: `Set.(union)`), keeps invariant. -/
def union [DecidableEq α] (s t : Set α) : Set α :=
  s.elems.foldl (fun acc x => insert x acc) t

/-- Lem: unions : forall 'a. SetType 'a => list (set 'a) -> set 'a -/
def unions [DecidableEq α] : List (Set α) → Set α :=
  fun ss => ss.foldr (fun s acc => union s acc) empty

/-- Convert to list (order = internal order, deterministic given construction). -/
def toList (s : Set α) : List α := s.elems

/-- Build from list (later insertions appear earlier in the internal order). -/
def fromList [DecidableEq α] (xs : List α) : Set α :=
  xs.foldl (fun acc x => insert x acc) empty

/-
  Deterministic ordered list output.
  We avoid `Ord` (Std); instead require `<` + decidability.
-/
private def insertSorted [LT α] [DecidableRel (fun a b : α => a < b)]
    (x : α) : List α → List α
  | [] => [x]
  | y :: ys =>
      if x < y then x :: y :: ys else y :: insertSorted x ys

private def sortList [LT α] [DecidableRel (fun a b : α => a < b)] : List α → List α
  | [] => []
  | x :: xs => insertSorted x (sortList xs)

/-- Like Lem's `Set_extra.toOrderedList`: deterministic sorted list.
    Requires an order `<` on α. -/
def toOrderedList [LT α] [DecidableRel (fun a b : α => a < b)] (s : Set α) : List α :=
  sortList s.elems

def findMax [LT α] [DecidableRel (fun a b : α => a < b)] (s : Set α) : Option α :=
  match s.elems with
  | []      => none
  | x :: xs =>
      some <|
        xs.foldl
          (fun m a => if m < a then a else m)
          x

def difference [DecidableEq α] (s t : Set α) : Set α :=
  t.elems.foldl (fun acc x => delete x acc) s

/-- Lem-style `Set.map`: map elements, deduplicating results to keep the invariant. -/
def map {β : Type v} [DecidableEq β] (f : α → β) (s : Set α) : Set β :=
  fromList (s.elems.map f)

/-- Predicate version: `p : α → Prop` with decidable predicate. -/
def filter [DecidableEq α] (p : α → Bool) (s : Set α) : Set α :=
  ⟨s.elems.filter p⟩

def foldl {β : Type v} (f : β → α → β) (init : β) (s : Set α) : β :=
  s.elems.foldl f init

def any (p : α → Bool) (s : Set α) : Bool :=
  s.elems.any p

def all (p : α → Bool) (s : Set α) : Bool :=
  s.elems.all p

private def insertBy (cmp : α → α → Ordering) (x : α) : List α → List α
  | [] => [x]
  | y :: ys =>
      match cmp x y with
      | .lt => x :: y :: ys
      | .eq => x :: y :: ys
      | .gt => y :: insertBy cmp x ys

private def sortBy (cmp : α → α → Ordering) : List α → List α
  | [] => []
  | x :: xs => insertBy cmp x (sortBy cmp xs)

def toOrderedListBy (cmp : α → α → Ordering) (s : Set α) : List α :=
  sortBy cmp s.elems

def bigunion {β : Type v} [DecidableEq β] (ss : Set (Set β)) : Set β :=
  ss.elems.foldl (fun acc t => union t acc) empty

def bigunionMap {β : Type v} [DecidableEq β] (f : α → Set β) (s : Set α) : Set β :=
  s.elems.foldl (fun acc a => union (f a) acc) empty

def bigunionMapBy {β : Type v} [DecidableEq β]
    (cmp : α → α → Ordering) (f : α → Set β) (s : Set α) : Set β :=
  (toOrderedListBy cmp s).foldl (fun acc a => union (f a) acc) empty

def filterP (p : α → Bool) (s : Set α) : Set α :=
  ⟨s.elems.filter p⟩

def mapMaybe {β : Type v} [DecidableEq β] (f : α → Option β) (s : Set α) : Set β :=
  s.elems.foldl
    (fun acc a =>
      match f a with
      | some b => insert b acc
      | none   => acc)
    empty

end Set

instance {α : Type u} : Inhabited (Smoosh.Set.Set α) :=
  ⟨Smoosh.Set.Set.empty⟩

end Smoosh.Set
