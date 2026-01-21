import Smoosh.Smoosh
import Smoosh.Fields
import Smoosh.Arith
import Smoosh.Pattern
import Smoosh.Command.All
import Smoosh.Semantics.SharedDecl

universe u

namespace Smoosh

/-- Lem: internal_check_traps -/
partial def internal_check_traps {α : Type u} [OS α]
    (step : evaluation_step) (s0 : os_state α) (c : stmt) :
    Except String (evaluation_step × os_state α × stmt) :=
  match pending_signal (α := α) s0 with
  | .error e =>
      .error e
  | .ok (s1, none) =>
      .ok (step, s1, c)
  | .ok (s1, some signal) =>
      match Map.lookup signal s1.sh.traps with
      | none =>
          internal_check_traps step s1 c
      | some ss_handler =>
          let (s2, _, s_handler) := concretize s1 ss_handler
          let src  := .ParseString .ParseTrap s_handler
          let sstr := parse_init src
          let c_handler :=
            .EvalLoop 1 (.Mk sstr (some (stack_init ()))) src .Noninteractive .Subsidiary
          .ok
            ( .XSNested (.XSTrap signal "trapped") step
            , s2
            , .Trapped signal s2.sh.exit_code c_handler c
            )

/-- Lem: check_traps -/
def check_traps {α : Type u} [OS α]
    (res : evaluation_step × os_state α × stmt) :
    Except String (evaluation_step × os_state α × stmt) :=
  match res with
  | (step, s, .Exit) =>
      .ok (step, s, .Exit)
  | (step0, s0, c0) =>
      let s1 := log_trace .Trace_traps "checked traps" s0
      internal_check_traps step0 s1 c0

/-- Lem: expansion_error -/
def expansion_error {α : Type u} [OS α]
    (may_exit : Bool) (s0 : os_state α)
    (evalstep : evaluation_step) (expstep : expansion_step) (err : fields) :
    Except String (evaluation_step × os_state α × stmt) :=
  let msg := string_of_symbolic_string (symbolic_string_of_fields err)
  let s1 := fail_with msg s0
  check_traps
    ( .XSExpand evalstep expstep
    , s1
    , if may_exit && is_interactive s1 then .Done else .Exit
    )

end Smoosh
