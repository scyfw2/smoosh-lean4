-- Smoosh/Prelude/Map.lean
-- A lightweight "Map" implementation backed by List (k × v)
import Smoosh.Set

open Smoosh
namespace Map

universe u v w

/-- A tiny map, backed by a list of key-value pairs.
    Invariant (maintained by `insert`/`fromList`): at most one entry per key,
    keeping the *latest inserted* binding at the head. -/
structure map (k : Type u) (α : Type v) where
  entries : List (k × α)
deriving Repr, DecidableEq
namespace map

variable {k : Type u} {α : Type v}

@[simp] def empty : map k α := ⟨[]⟩

@[simp] def toList (m : map k α) : List (k × α) := m.entries

def isEmpty (m : map k α) : Bool :=
  m.entries.isEmpty

/-- Delete all bindings for `key`. -/
def delete [DecidableEq k] (key : k) (m : map k α) : map k α :=
  ⟨m.entries.filter (fun kv => decide (kv.1 ≠ key))⟩

/-- Insert a binding, overriding any existing binding for the same key. -/
def insert [DecidableEq k] (key : k) (val : α) (m : map k α) : map k α :=
  ⟨(key, val) :: (delete key m).entries⟩

/-- Lookup the value for `key` (returns the first match, i.e. the most recent insertion). -/
def lookup [DecidableEq k] (key : k) : map k α → Option α
  | ⟨[]⟩ => none
  | ⟨(k', v') :: xs⟩ =>
      if k' = key then
        some v'
      else
        lookup key ⟨xs⟩

def contains [DecidableEq k] (key : k) (m : map k α) : Bool :=
  match lookup (k := k) (α := α) key m with
  | some _ => true
  | none   => false

/-- Build a map from a list, later pairs override earlier ones. -/
def fromList [DecidableEq k] (xs : List (k × α)) : map k α :=
  xs.foldl (fun m kv => insert (k := k) (α := α) kv.1 kv.2 m) empty

/-- The set of keys (Finset). -/
def domain [DecidableEq k] (m : map k α) : Smoosh.Set.Set k :=
  Set.Set.fromList (m.entries.map Prod.fst)

/-- Map over values. -/
def mapValues {β : Type w} (f : α → β) (m : map k α) : map k β :=
  ⟨m.entries.map (fun kv => (kv.1, f kv.2))⟩

/-- Map over values with possible failure; drop entries mapped to `none`. -/
def mapMaybe {β : Type w} (f : k → α → Option β) (m : map k α) : map k β :=
  ⟨m.entries.foldr
      (fun kv acc =>
        match f kv.1 kv.2 with
        | some b => (kv.1, b) :: acc
        | none   => acc)
      []⟩

/-- Fold (right fold) over entries, Lem 风格：`f key val acc`. -/
def fold {β : Type w} (f : k → α → β → β) (m : map k α) (init : β) : β :=
  m.entries.foldr (fun kv acc => f kv.1 kv.2 acc) init

def null (m : map k α) : Bool :=
  m.entries.isEmpty

def toSetBy {k : Type u} {α : Type v}
    (_cmp : (k × α) → (k × α) → Ordering) (m : map k α) : Set.Set (k × α) :=
  ⟨m.entries⟩

/-- Right-biased union: bindings in `m₂` override bindings in `m₁` on key clashes. -/
def union [DecidableEq k] (m₁ m₂ : map k α) : map k α :=
  m₂.entries.foldl
    (fun acc kv => insert (k := k) (α := α) kv.1 kv.2 acc)
    m₁

/-- Lem: Map.toSet : map k α -> Set (k × α) -/
def toSet [DecidableEq (k × α)] (m : map k α) : Smoosh.Set.Set (k × α) :=
  Smoosh.Set.Set.fromList m.entries


end map

abbrev empty {k : Type u} {α : Type v} : map k α := map.empty
abbrev toList {k : Type u} {α : Type v} (m : map k α) : List (k × α) := map.toList m
abbrev isEmpty {k : Type u} {α : Type v} (m : map k α) : Bool := map.isEmpty m

abbrev delete {k : Type u} {α : Type v} [DecidableEq k] (key : k) (m : map k α) : map k α :=
  map.delete (k := k) (α := α) key m

abbrev lookup {k : Type u} {α : Type v} [DecidableEq k] (key : k) (m : map k α) : Option α :=
  map.lookup (k := k) (α := α) key m

abbrev insert {k : Type u} {α : Type v} [DecidableEq k] (key : k) (val : α) (m : map k α) : map k α :=
  map.insert (k := k) (α := α) key val m

abbrev fromList {k : Type u} {α : Type v} [DecidableEq k] (xs : List (k × α)) : map k α :=
  map.fromList (k := k) (α := α) xs

abbrev domain {k : Type u} {α : Type v} [DecidableEq k] (m : map k α) : Set.Set k :=
  map.domain (k := k) (α := α) m

abbrev mapValues {k : Type u} {α : Type v} {β : Type w} (f : α → β) (m : map k α) : map k β :=
  map.mapValues (k := k) (α := α) (β := β) f m

abbrev mapMaybe {k : Type u} {α : Type v} {β : Type w} (f : k → α → Option β) (m : map k α) : map k β :=
  map.mapMaybe (k := k) (α := α) (β := β) f m

abbrev fold {k : Type u} {α : Type v} {β : Type w} (f : k → α → β → β) (m : map k α) (init : β) : β :=
  map.fold (k := k) (α := α) (β := β) f m init

abbrev null {k : Type u} {α : Type v} (m : map k α) : Bool :=
  map.null (k := k) (α := α) m

abbrev toSetBy {k : Type u} {α : Type v}
    (_cmp : (k × α) → (k × α) → Ordering) (m : map k α) : Smoosh.Set.Set (k × α) :=
  map.toSetBy (k := k) (α := α) _cmp m

abbrev union {k : Type u} {α : Type v} [DecidableEq k] (m₁ m₂ : map k α) : map k α :=
  map.union (k := k) (α := α) m₁ m₂

abbrev toSet {k : Type u} {α : Type v} [DecidableEq (k × α)] (m : map k α) : Smoosh.Set.Set (k × α) :=
  map.toSet (k := k) (α := α) m

end Map
