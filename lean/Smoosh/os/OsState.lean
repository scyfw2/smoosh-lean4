import Smoosh.Prelude.All

open Smoosh

/-- Lem: log_entry type -/
inductive log_entry where
  | LogTrace : trace_tag → String → log_entry
  | LogConcretization : symbolic_string → log_entry
  | LogStep : evaluation_step → log_entry

/-- Lem: string_of_log_entry : log_entry -> string -/
def string_of_log_entry : log_entry → String
  | log_entry.LogTrace tag msg =>
      "[" ++ string_of_trace_tag tag ++ "] " ++ msg
  | log_entry.LogConcretization ss =>
      "[concretized] " ++ string_of_symbolic_string ss
  | log_entry.LogStep step =>
      "[step] " ++ string_of_evaluation_step step

/-- The actual OS state. -/
structure os_state (α : Type u) where
  symbolic : α
  sh : shell_state
  log : List log_entry
  fuel : Option Nat
