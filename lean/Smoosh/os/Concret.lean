import Smoosh.Prelude.All
import Smoosh.Map
import Smoosh.Set
import Smoosh.os.OsState
import Smoosh.Num
import Smoosh.os.ParamHelper
import Smoosh.os.LogHis
import Smoosh.os.Hashing

universe u

namespace Smoosh
open Smoosh

/-- Lem: val concretize
    : forall 'a. os_state 'a -> symbolic_string -> os_state 'a * bool * string -/
def concretize : ∀ {α : Type u}, os_state α → symbolic_string → (os_state α × Bool × String)
| _, os0, ss =>
  match try_concrete ss with
  | none =>
      ( log_concretization ss os0
      , true
      , string_of_symbolic_string ss )
  | some s =>
      (os0, false, s)

/-- Lem: val concretize_many
    : forall 'a. os_state 'a -> fields -> os_state 'a * bool * list string
-/
def concretize_many : ∀ {α : Type u}, os_state α → fields → (os_state α × Bool × List String)
| _, os0, f =>
  List.foldr
    (fun ss acc =>
      match acc with
      | (os, (before, strs)) =>
          match concretize os ss with
          | (os', (now, str)) =>
              (os', (now || before, str :: strs)))
    (os0, (false, []))
    f

/-- Lem: val concretize_fields
    : forall 'a. os_state 'a -> fields -> os_state 'a * bool * string
-/
def concretize_fields : ∀ {α : Type u}, os_state α → fields → (os_state α × Bool × String)
| _, os0, f =>
  match f with
  | [] =>
      (os0, false, "")
  | [ss] =>
      concretize os0 ss
  | ss :: f' =>
      match concretize os0 ss with
      | (os1, (c1, s)) =>
          match concretize_fields os1 f' with
          | (os2, (c2, s')) =>
              (os2, (c1 || c2, s ++ " " ++ s'))

--/* Useful predicates ************************************************** */
/-- Lem: val is_interactive : forall 'a. os_state 'a -> bool -/
def is_interactive : ∀ {α : Type u}, os_state α → Bool
| _, os =>
  Set.Set.member .Sh_interactive os.sh.opts

/-- Lem: val interactivity_mode_of : forall 'a. os_state 'a -> interactivity_mode -/
def interactivity_mode_of : ∀ {α : Type u}, os_state α → interactivity_mode
| _, os =>
  if is_interactive os then .Interactive else .Noninteractive

/-- Lem: val is_monitoring : forall 'a. os_state 'a -> bool -/
def is_monitoring : ∀ {α : Type u}, os_state α → Bool
| _, os =>
  Set.Set.member .Sh_monitor os.sh.opts

--/* Exit codes ********************************************************* */
/-- Lem: val exit_with : forall 'a. nat -> os_state 'a -> os_state 'a -/
def exit_with : ∀ {α : Type u}, Nat → os_state α → os_state α
| _, ec, os =>
  { os with sh := { os.sh with exit_code := ec } }

--/* FS helpers ********************************************************* */
/-- Lem: val path_dotdot_rev_cl : list char -> list char -/
def path_dotdot_rev_cl : List Char → List Char
| []           => ['/' ]        -- stop at the root
| ['/' ]       => ['/' ]        -- stop at the root
| '/' :: rest  => rest
| _   :: rest  => path_dotdot_rev_cl rest

/-- Lem: val dotdot : path -> path -/
def dotdot (path : path) : Smoosh.path :=
  let cs : List Char := path.toList
  let rev := cs.reverse
  let cut := path_dotdot_rev_cl rev
  String.ofList cut.reverse

--/* Functions and positional param management ************************** */
/-- Lem: val defun : forall 'a. string -> stmt -> os_state 'a -> os_state 'a -/
def defun : ∀ {α : Type u}, String → stmt → os_state α → os_state α
| _, name, body, os =>
  { os with sh := { os.sh with funcs := Map.insert name body os.sh.funcs } }

/-- Lem: val lookup_function : forall 'a. string -> os_state 'a -> maybe stmt -/
def lookup_function : ∀ {α : Type u}, String → os_state α → Option stmt
| _, name, os =>
  Map.lookup name os.sh.funcs

/-- Lem: val set_function_params : forall 'a. nat -> fields -> os_state 'a -> os_state 'a -/
def set_function_params : ∀ {α : Type u}, Nat → fields → os_state α → os_state α
| _, ln, argv, os =>
  let new_params :=
    match os.sh.positional_params with
    | []        => ([] : symbolic_string) :: argv
    | arg0 :: _ => arg0 :: argv
  { os with sh := { os.sh with loop_nest := ln, positional_params := new_params } }

/-- Lem: val enter_loop : forall 'a. os_state 'a -> os_state 'a -/
def enter_loop : ∀ {α : Type u}, os_state α → os_state α
| _, os =>
  { os with sh := { os.sh with loop_nest := os.sh.loop_nest + 1 } }

/-- Lem: val exit_loop : forall 'a. os_state 'a -> os_state 'a -/
def exit_loop : ∀ {α : Type u}, os_state α → os_state α
| _, os =>
  { os with sh := { os.sh with loop_nest := os.sh.loop_nest - 1 } }

 /-- Lem: val set_last_pid : forall 'a. pid -> os_state 'a -> os_state 'a -/
def set_last_pid : ∀ {α : Type u}, pid → os_state α → os_state α
| _, p, os =>
  { os with sh := { os.sh with last_pid := some p } }

--/* Job control ********************************************************* */

namespace Signal_platform
  opaque platform_int_of_signal : signal → Nat
end Signal_platform

/-- Lem: val ec_of_job_status : job_status -> maybe nat -/
def ec_of_job_status (status : job_status) : Option Nat :=
  let ec_of_signal (sig : signal) : Option Nat :=
    some (128 + Signal_platform.platform_int_of_signal sig)
  match status with
  | .JobRunning            => none
  | .JobStopped .TSTP       => ec_of_signal .SIGTSTP
  | .JobStopped .STOP       => ec_of_signal .SIGSTOP
  | .JobStopped .TTIN       => ec_of_signal .SIGTTIN
  | .JobStopped .TTOU       => ec_of_signal .SIGTTOU
  | .JobTerminated sig     => ec_of_signal sig
  | .JobDone code          => some code

/-- Lem: val job_status_of_ec : nat -> job_status -/
def job_status_of_ec (ec : Nat) : job_status :=
  match List.find? (fun sig => ec = 128 + Signal_platform.platform_int_of_signal sig) all_signals with
  | some sig =>
      match sig with
      | .SIGTSTP => .JobStopped .TSTP
      | .SIGTTIN => .JobStopped .TTIN
      | .SIGTTOU => .JobStopped .TTOU
      | .SIGSTOP => .JobStopped .STOP
      | _       => .JobTerminated sig
  | none =>
      .JobDone ec

/-- Lem: val delete_job : forall 'a. os_state 'a -> nat (* job id *) -> os_state 'a -/
def delete_job {α : Type u} (os0 : os_state α) (id : Nat) : os_state α :=
  { os0 with sh :=
      { os0.sh with
        jobs := (os0.sh.jobs).filter (fun j => j.id ≠ id || is_active_job j) } }

/-- Lem: val delete_job_with_pid : forall 'a. os_state 'a -> pid -> os_state 'a -/
def delete_job_with_pid {α : Type u} (os0 : os_state α) (pid : pid) : os_state α :=
  { os0 with sh :=
      { os0.sh with
        jobs := (os0.sh.jobs).filter (fun j => j.pid ≠ pid || is_active_job j) } }

/-- Lem: val find_job_with_pid : forall 'a. os_state 'a -> pid -> maybe job_info -/
def find_job_with_pid {α : Type u} (os0 : os_state α) (pid : pid) : Option job_info :=
  List.find?
    (fun j =>
      j.pid = pid ||
      j.pipeline.any (fun pr => pr.1 = pid))
    os0.sh.jobs

-- /* Traps **************************************************************/
/-- Lem: val update_trap : forall 'a. os_state 'a -> signal -> maybe symbolic_string -> os_state 'a -/
def update_trap {α : Type u} (os0 : os_state α) (sig : signal) (action : Option symbolic_string) : os_state α :=
  match action with
  | none =>
      { os0 with sh := { os0.sh with traps := Map.delete sig os0.sh.traps } }
  | some cmd =>
      { os0 with sh := { os0.sh with traps := Map.insert sig cmd os0.sh.traps } }

/-- Lem: val clear_traps_for_subshell : shell_state -> shell_state * list signal -/
def clear_traps_for_subshell (sh : shell_state) : shell_state × List signal :=
  let traps : List (signal × symbolic_string) := Map.toList sh.traps
  let (ignored, handled) :=
    traps.partition (fun pr => string_of_symbolic_string pr.2 = "")
  ( { sh with
      traps := Map.fromList ignored
      supershell_traps := some sh.traps }
  , handled.map Prod.fst )

/-- Lem: val clear_supershell_traps : forall 'a. os_state 'a -> os_state 'a -/
def clear_supershell_traps {α : Type u} (os : os_state α) : os_state α :=
  { os with sh := { os.sh with supershell_traps := none } }

/-- Lem: val exit_trap : forall 'a. os_state 'a -> os_state 'a * maybe stmt -/
def exit_trap {α : Type u} (s0 : os_state α) : os_state α × Option stmt :=
  match Map.lookup .EXIT s0.sh.traps with
  | none =>
      (s0, none)
  | some ss_cmd =>
      (update_trap s0 .EXIT none, some (command_eval ss_cmd))

/-- Lem: val prepare_subshell : shell_state -> shell_state * list signal -/
def prepare_subshell (sh0 : shell_state) : shell_state × List signal :=
  let sh1 :=
    { sh0 with
      outermost := false
      optoff := none
      jobs := []
      loop_nest := 0 }
  clear_traps_for_subshell sh1

-- /* Aliases ************************************************************/

opaque dash_setalias : String → String → Unit
opaque dash_unalias : String → Unit

/-- Lem: val set_alias : forall 'a. os_state 'a -> string -> string -> os_state 'a -/
def set_alias {α : Type u} (os : os_state α) (name mapping : String) : os_state α :=
  let _ := dash_setalias name mapping
  { os with sh := { os.sh with aliases := Map.insert name mapping os.sh.aliases } }

/-- Lem: val free_alias : forall 'a. os_state 'a -> string -> os_state 'a -/
def free_alias {α : Type u} (os : os_state α) (name : String) : os_state α :=
  let _ := dash_unalias name
  { os with sh := { os.sh with aliases := Map.delete name os.sh.aliases } }


end Smoosh
