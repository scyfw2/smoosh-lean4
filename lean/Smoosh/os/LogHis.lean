import Smoosh.Prelude.All
import Smoosh.Map
import Smoosh.Set
import Smoosh.os.OsState
import Smoosh.Num
import Smoosh.os.ParamHelper

universe u

namespace Smoosh
open Smoosh

/-- Lem: val log : forall 'a. log_entry -> os_state 'a -> os_state 'a -/
def log {α : Type u} (entry : log_entry) (os : os_state α) : os_state α :=
  { os with log := entry :: os.log }

/-- Lem: val out_of_fuel : forall 'a. os_state 'a -> bool -/
def out_of_fuel {α : Type u} (os : os_state α) : Bool :=
  match os.fuel with
  | none   => false
  | some n => n = 0

/-- Lem: string_of_fuel : forall 'a. os_state 'a -> string -/
def string_of_fuel {α : Type u} (os : os_state α) : String :=
  match os.fuel with
  | none   => "unbounded"
  | some n => stringFromNat n

/-- Lem: entry_unspecified : log_entry -> bool -/
def entry_unspecified (entry : log_entry) : Bool :=
  match entry with
  | .LogTrace .Trace_unspec _ => true
  | .LogTrace .Trace_undef _  => true
  | _                       => false

/-- Lem: entry_undefined : log_entry -> bool -/
def entry_undefined (entry : log_entry) : Bool :=
  match entry with
  | .LogTrace .Trace_undef _ => true
  | _                      => false

/-- Lem: try_entry_step : log_entry -> maybe evaluation_step -/
def try_entry_step (entry : log_entry) : Option evaluation_step :=
  match entry with
  | .LogStep step => some step
  | _            => none

/-- Lem: in_unspecified_state : forall 'a. os_state 'a -> bool -/
def in_unspecified_state {α : Type u} (os : os_state α) : Bool :=
  os.log.any entry_unspecified

/-- Lem: in_undefined_state : forall 'a. os_state 'α -> bool -/
def in_undefined_state {α : Type u} (os : os_state α) : Bool :=
  os.log.any entry_undefined

/-- Lem: extract_unspec : forall 'a. os_state 'α -> list string -/
def extract_unspec {α : Type u} (os : os_state α) : List String :=
  os.log.filterMap (fun entry =>
    match entry with
    | .LogTrace .Trace_unspec msg => some ("[unspec] " ++ msg)
    | .LogTrace .Trace_undef  msg => some ("[undef] "  ++ msg)
    | _                         => none)

/-- Lem: extract_trace : forall 'a. os_state 'α -> list evaluation_step -/
def extract_trace {α : Type u} (os : os_state α) : List evaluation_step :=
  os.log.filterMap try_entry_step

/-- Lem: log_step : forall 'a. evaluation_step -> os_state 'α -> os_state 'α -/
def log_step {α : Type u} (step : evaluation_step) : os_state α → os_state α :=
  log (.LogStep step)

/--
Lem: log_trace_with :
  forall 'a. (string -> os_state 'α -> os_state 'α) -> trace_tag -> string -> os_state 'α -> os_state 'α
-/
def log_trace_with {α : Type u}
    (write : String → os_state α → os_state α)
    (tag : trace_tag) (msg : String) (os0 : os_state α) : os_state α :=
  let entry := .LogTrace tag msg
  let os1 := log entry os0
  if Set.Set.member (.Sh_trace tag) os1.sh.opts then
    write (ps4 os0 ++ string_of_log_entry entry ++ "\n") os1
  else
    os1

/-- Lem: log_concretization : forall 'a. symbolic_string -> os_state 'α -> os_state 'α -/
def log_concretization {α : Type u} (ss : symbolic_string) : os_state α → os_state α :=
  log (.LogConcretization ss)

/-- Lem: histwrap : forall 'a. os_state 'α -> nat -/
def histwrap {α : Type u} (os : os_state α) : Nat :=
  let hard_upper_limit : Nat := Num.NatConv.toNat (α := Int32) Num.int32Max
  match lookup_concrete_param os "HISTSIZE" with
  | .error _ =>
      hard_upper_limit
  | .ok none =>
      hard_upper_limit
  | .ok (some n_str) =>
      let usr_n : Nat :=
        match Num.readUnsignedInteger 10 n_str.toList with
        | .error _ =>
            hard_upper_limit
        | .ok n =>
            Nat.max (Num.NatConv.toNat n) 128
      Nat.min usr_n hard_upper_limit

/-- Lem: next_histnum : forall 'a. os_state 'α -> nat -/
def next_histnum {α : Type u} (os : os_state α) : Nat :=
  match os.sh.history with
  | [] => 1
  | (last, _) :: _ =>
      if last = histwrap os then 1 else last + 1

/-- Lem: add_to_history : forall 'a. stmt -> os_state 'α -> os_state 'α -/
def add_to_history {α : Type u} (c : stmt) (os : os_state α) : os_state α :=
  if Set.Set.member .Sh_nolog os.sh.opts then
    os
  else
    let histnum := next_histnum os
    { os with
      sh := { os.sh with
        history := (histnum, c) :: os.sh.history } }

end Smoosh
