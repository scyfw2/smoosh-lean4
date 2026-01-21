import Smoosh.Prelude.All
import Smoosh.Map
import Smoosh.Set
import Smoosh.os.OsState
import Smoosh.Num
import Smoosh.os.FsState
import Smoosh.os.ParamHelper
import Smoosh.os.OsClass
-- TODO: partial in mutual
universe u

open Smoosh

variable {α : Type u}
/-- Lem: val try_write_fd : forall 'a. OS 'a => fd -> string -> os_state 'a -> os_state 'a * bool -/
def try_write_fd [OS α]
    (fdNum : Smoosh.fd) (s : String) (os : os_state α) : (os_state α × Bool) :=
  match write_fd os fdNum s with
  | some os' => (os', true)
  | none     => (os, false)

/-- Lem: val write_stdout : forall 'a. OS 'a => string -> os_state 'a -> os_state 'a -/
def write_stdout [OS α] (msg : String) (os : os_state α) : os_state α :=
  (try_write_fd STDOUT msg os).1
/-- Lem: val write_stderr : forall 'a. OS 'a => string -> os_state 'a -> os_state 'a -/
def write_stderr [OS α] (msg : String) (os : os_state α) : os_state α :=
  (try_write_fd STDERR msg os).1
/-- Lem: val fail_with_code : forall 'a. OS 'a => nat -> string -> os_state 'a -> os_state 'a -/
def fail_with_code [OS α] (ec : Nat) (msg : String) (os : os_state α) : os_state α :=
  exit_with ec (write_stderr (msg ++ "\n") os)
/-- Lem: val fail_with : forall 'a. OS 'a => string -> os_state 'a -> os_state 'a -/
def fail_with [OS α] (msg : String) (os : os_state α) : os_state α :=
  fail_with_code (α := α) 1 msg os
/-- Lem: val safe_write_stdout : forall 'a. OS 'a => string -> string -> os_state 'a -> os_state 'a -/
def safe_write_stdout [OS α]
    (writer : String) (msg : String) (os : os_state α) : os_state α :=
  let (os', ok) := try_write_fd (α := α) STDOUT msg os
  if !ok then
    fail_with_code (α := α) 2 ("smoosh: " ++ writer ++ ": I/O error") os'
  else
    os'
/-- Lem: safe_write_stderr -/
def safe_write_stderr [OS α]
    (msg : String) (os : os_state α) : os_state α :=
  let (os', ok) := try_write_fd (α := α) STDERR msg os
  if !ok then
    exit_with 2 os'
  else
    os'

-- (* FS and path manipulation *******************************************)
/-- Lem: val is_dir : forall 'a. OS 'a => os_state 'a -> path -> bool -/
def is_dir [OS α] (os : os_state α) (p : path) : Bool :=
  file_typeF os p = some .FileDirectory
/-- Lem: val canonicalize_split_path : forall 'a. OS 'a => os_state 'a -> path -> list string -> maybe string -/
def canonicalize_split_path [OS α]
    (os : os_state α) (p : path) (components : List String) : Option path :=
  match components with
  | [] => some p
  | "" :: cs =>
      canonicalize_split_path os p cs         -- result of //
  | "." :: cs =>
      canonicalize_split_path os p cs
  | ".." :: cs =>
      if is_dir os p then
        canonicalize_split_path os (dotdot p) cs
      else
        none
  | dir :: cs =>
      canonicalize_split_path os (join_path p dir) cs
/-- Lem: val canonicalize_path : forall 'a. OS 'a => os_state 'a -> path -> maybe path  -/
def canonicalize_path [OS α] (os : os_state α) (p : path) : Option path :=
  let (initial, p') :=
    match toCharList p with
    | '/' :: '/' :: rest =>
        ("//", toString rest)      -- save initial double slash
    | '/' :: rest =>
        ("/", toString rest)
    | _ =>
        ("/", p)
  let components := split_string_on false '/' p'
  canonicalize_split_path (α := α) os initial components

-- (* Job control ********************************************************)
/-- LEm: val show_job : forall 'a. OS 'a => jobs_mode -> pid * pid -> job_info -> os_state 'a -> os_state 'a -/
def show_job [OS α]
    (mode : jobs_mode) (curjob : pid × pid) (job : job_info) (os0 : os_state α) : os_state α :=
  safe_write_stdout (α := α) "jobs" (string_of_job mode curjob job) os0
/-- Lem: val show_job_when : forall 'a. OS 'a => sh_opt -> jobs_mode -> pid * pid -> job_info -> os_state 'a -> os_state 'a -/
def show_job_when [OS α]
    (opt : sh_opt) (mode : jobs_mode) (curjob : pid × pid) (job : job_info) (os0 : os_state α) : os_state α :=
  if Set.Set.member opt os0.sh.opts then
    let os1 :=
      if opt = .Sh_notify then
        write_stderr (α := α) "\n" os0    -- async: make sure we add a newline
      else
        os0
    write_stderr (α := α) (string_of_job mode curjob job) os1
  else
    os0
/-- Lem: val active_jobs : forall 'a. OS 'a => os_state 'a -> os_state 'a * list job_info -/
def active_jobs [OS α] (os0 : os_state α) : (os_state α × List job_info) :=
  let real_jobs := List.filter is_active_job os0.sh.jobs
  ( { os0 with sh := { os0.sh with jobs := real_jobs } }
  , real_jobs )
/-- Lem: val show_jobs : forall 'a. OS 'a => maybe sh_opt -> jobs_mode -> nat * nat -> list job_info -> os_state 'a -> os_state 'a -/
def show_jobs [OS α]
    (mopt : Option sh_opt) (mode : jobs_mode) (cur_prev : Nat × Nat)
    (jobs : List job_info) (s0 : os_state α) : os_state α :=
  let showJ : jobs_mode → (Nat × Nat) → job_info → os_state α → os_state α :=
    match mopt with
    | none     => show_job (α := α)
    | some opt => show_job_when (α := α) opt
  List.foldl (fun os job => showJ mode cur_prev job os) s0 (sort jobs)
/-- Lem: jobs_update_mode type -/
inductive jobs_update_mode where
  | DeleteJobs
  | NoDeleteJobs
deriving DecidableEq, Repr
/-- Lem: delete_jobs -/
def delete_jobs : jobs_update_mode → Bool
  | .DeleteJobs   => true
  | .NoDeleteJobs => false

/- helper for the interactive shell in -m and -b; used in EvalLoop

   this is all a recursive loop because add_job needs to
   show_changed_jobs and show_changed_jobs needs to update_jobs and
   update_jobs needs to add_job
-/

mutual
  /-- Lem: val show_changed_jobs : forall 'a. OS 'a => jobs_update_mode -> sh_opt -> os_state 'a -> os_state 'a -/
  partial def show_changed_jobs {α : Type u} [OS α]
      (jum : jobs_update_mode) (opt : sh_opt) (s0 : os_state α) : os_state α :=
    let (s1, changed) := update_jobs s0
    let s2 :=
      show_jobs (some opt) .JobsNormal (cur_prev_jobs s1.sh.jobs) changed s1
    if Set.Set.member opt s0.sh.opts && delete_jobs jum then
      List.foldl (fun os j => delete_job os j.id) s2 changed
    else
      s2

  /-- Lem: val add_job : forall 'a. OS 'a =>
        os_state 'a ->
        list (pid * stmt) -> pid -> stmt (* cmd *) -> bg_mode -> job_status ->
        os_state 'a * job_info -/
  partial def add_job [OS α]
      (os0 : os_state α)
      (pipeline : List (pid × stmt)) (pidNum : pid) (cmd : stmt)
      (bg : bg_mode) (status : job_status) : (os_state α × job_info) :=
    let os1 := show_changed_jobs jobs_update_mode.NoDeleteJobs .Sh_monitor os0
    let highest_job_num : Nat :=
      match os1.sh.jobs with
      | [] => 0
      | js => (js.map (fun job => job.id)).foldl Nat.max 0
    let new_job : job_info :=
      { id := highest_job_num + 1
      , pid := pidNum
      , cmd := cmd
      , status := status
      , pipeline := pipeline
      }
    let os2 :=
      if is_monitoring os1 && is_bg bg && is_active_job new_job then
        let msg := "[" ++ stringFromNat new_job.id ++ "] " ++ string_of_pid pidNum ++ "\n"
        write_stdout msg os1
      else
        os1
    ( { os2 with sh := { os1.sh with jobs := new_job :: os1.sh.jobs } }
    , new_job )

  /-- Lem: val update_job_with_pid : forall 'a. OS 'a => os_state 'a -> nat -> job_status -> os_state 'a * maybe job_info -/
  partial def update_job_with_pid {α : Type u} [OS α]
      (os0 : os_state α) (pidNum : pid) (new_status : job_status) :
      (os_state α × Option job_info) :=
    match List.find? (fun j => j.pid = pidNum) os0.sh.jobs with
    | none =>
        -- sub-child / dead code path in Lem: keep behaviour (no update)
        (os0, none)
    | some job =>
        let job' : job_info := { job with status := new_status }
        let cur_jobs :=
          os0.sh.jobs.map (fun j => if j.id = job'.id then job' else j)
        let os1 : os_state α :=
          { os0 with sh := { os0.sh with jobs := cur_jobs } }
        let os2 :=
          show_job_when .Sh_notify .JobsNormal (cur_prev_jobs os1.sh.jobs) job' os1
        (os2, some job')

  /-- Lem: val update_jobs_loop : forall 'a. OS 'a => os_state 'a -> list job_info -> os_state 'a * list job_info -/
  partial def update_jobs_loop {α : Type u} [OS α]
      (os0 : os_state α) (changes : List job_info) : (os_state α × List job_info) :=
    match waitchild os0 with
    | (os1, none) => (os1, changes)
    | (os1, some (pidNum, status)) =>
        let (os2, m_job') := update_job_with_pid os1 pidNum status
        let changes' :=
          match m_job' with
          | none      => changes
          | some job' => job' :: changes
        update_jobs_loop os2 changes'

  /-- Lem: val update_jobs : forall 'a. OS 'a => os_state 'a -> os_state 'a * list job_info (* changed *) -/
  partial def update_jobs {α : Type u} [OS α]
      (os0 : os_state α) : (os_state α × List job_info) :=
    update_jobs_loop os0 []
end

/-- Lem: waitpid_or_lookup -/
def waitpid_or_lookup [OS α]
    (step_eval : step_fun α) (os0 : os_state α) (pidNum : pid) :
    (os_state α × Option (Except evaluation_step Nat)) :=
  match waitpid step_eval os0 pidNum with
  | (os1, none) =>
      -- got ECHILD, consult job table
      match find_job_with_pid os1 pidNum with
      | none => (os1, none)
      | some job =>
          match ec_of_job_status job.status with
          | none => (os1, none)
          | some code =>
              let os2 := delete_job os1 job.id
              (os2, some (.ok code))
  | (os1, some (.error step)) => (os1, some (.error step))
  | (os1, some (.ok code)) =>
      let status := job_status_of_ec code
      let (os2, m_job) := update_job_with_pid (α := α) os1 pidNum status
      let os3 :=
        match m_job, status with
        | some job, job_status.JobStopped _ =>
            if Set.Set.member .Sh_monitor os2.sh.opts then
              show_job (α := α) .JobsNormal (cur_prev_jobs os1.sh.jobs) job (write_stderr (α := α) "\n" os2)
            else
              os2
        | _, _ => os2
      (os3, some (.ok code))
/-
We need to:
  (a) make sure everything in the job is done, and
  (b) return the exit code of the pid we care about
-/

/-- Lem: wait_for_job -/
def wait_for_job [OS α]
    (step_eval : step_fun α)
    (os0 : os_state α) (job : job_info) (pipeline : pipeline_info)
    (tgt_pid : pid) (mec : Option Nat) :
    (os_state α × Option (Except evaluation_step Nat)) :=
  match pipeline with
  | [] =>
      match mec with
      | none    => waitpid_or_lookup step_eval os0 tgt_pid
      | some ec => (os0, some (.ok ec))
  | (pidNum, _) :: pipeline' =>
      match waitpid_or_lookup step_eval os0 pidNum with
      | (os1, none) => (os1, none)
      | (os1, some (.error step)) => (os1, some (.error step))
      | (os1, some (.ok ec)) =>
          let mec' := if pidNum = tgt_pid then some ec else mec
          wait_for_job step_eval os1 job pipeline' tgt_pid mec'

def wait_for_pid [OS α]
    (step_eval : step_fun α) (os0 : os_state α) (pidNum : pid) :
    (os_state α × Option (Except evaluation_step Nat)) :=
  match find_job_with_pid os0 pidNum with
  | none => waitpid_or_lookup step_eval os0 pidNum
  | some job =>
      /-
        we reverse the pipeline so that we wait for the final job in
        the pipeline _first_.

        this gives us a better schedule in symbolic mode

        it shouldn't matter at all in system mode
      -/
      wait_for_job step_eval os0 job (List.reverse job.pipeline) pidNum none

-- (* Redirects **********************************************************)
/-- Lem: val redirect : forall 'a. OS 'a => os_state 'a -> expanded_redir ->
               os_state 'a * either string saved_fds -/
def redirect [OS α]
    (os0 : os_state α) (er : expanded_redir) :
    (os_state α × Except String saved_fds) :=
  match er with
  | .ERFile ty wantedFd sfile =>
      match open_file_for_redir os0 ty sfile with
      | (os1, .error err)     => (os1, .error err)
      | (os1, .ok newFd)      => renumber_fd os1 .CloseOrig newFd wantedFd
  | .ERDup _ty _closeOrig origFd none =>
      -- meant to close origFd
      close_and_save_fd os0 origFd
  | .ERDup _ty closeOrig origFd (some wantedFd) =>
      -- dash treats both directions the same: dup2 doesn't care
      renumber_fd os0 closeOrig wantedFd origFd
  | .ERHeredoc _ty wantedFd ss =>
      -- ty irrelevant now; used earlier for expansion choices
      let (os1, _concretized, s) := concretize os0 ss
      match open_heredoc os1 s with
      | .error err          => (os1, .error err)
      | .ok (os2, newFd)    => renumber_fd os2 .CloseOrig newFd wantedFd

/-- Lem: val restore_fds : forall 'a. OS 'a => os_state 'a -> saved_fds -> os_state 'a -/
def restore_fds [OS α]
    (os : os_state α) (saved : saved_fds) : os_state α :=
  List.foldr
    (fun (p : Smoosh.fd × saved_fd_info) os' =>
      restore_fd os' p.1 p.2)
    os
    saved
/-- Lem: really_do_redirs -/
def really_do_redirs [OS α]
    (os0 : os_state α) (ers : List expanded_redir) :
    (os_state α × Except String saved_fds) :=
  match ers with
  | [] => (os0, .ok [])
  | er :: ers' =>
      match redirect os0 er with
      | (os1, .error err) => (os1, .error err)
      | (os1, .ok saved)  =>
          match really_do_redirs os1 ers' with
          | (os2, .error err)    => (os2, .error err)
          | (os2, .ok saved')    => (os2, .ok (saved ++ saved'))
/-- Lem: val do_redirs : forall 'a. OS 'a => os_state 'a -> list expanded_redir ->
                os_state 'a * either string saved_fds -/
def do_redirs [OS α]
    (os0 : os_state α) (ers : List expanded_redir) :
    (os_state α × Except String saved_fds) :=
  if Set.Set.member .Sh_noexec os0.sh.opts then
    (os0, .ok [])
  else
    really_do_redirs os0 ers

-- (* Pipes **************************************************************)
/-- Lem: val fork_pipe_subshell : forall 'a. OS 'a =>
                 os_state 'a ->
                 stmt -> (* actual stmt *)
                 bg_mode -> (* bg? [for tty] *)
                 maybe pid -> (* pipeline pgrp *)
                 bool -> (* last job? *)
                 pipeline_info ->
                 os_state 'a * pipeline_info * pid -/
def fork_pipe_subshell [OS α]
    (s0 : os_state α)
    (st : stmt)
    (bg : bg_mode)
    (pgid : Option pid)
    (last : Bool)
    (pipeline : pipeline_info) :
    (os_state α × pipeline_info × pid) :=
  let (s1, childPid) := fork_and_subshell s0 st bg pgid last
  (s1, pipeline, childPid)

/-- Lem: val run_pipe_loop : forall 'a. OS 'a =>
                 os_state 'a ->
                 list stmt ->
                 fd ->
                 bg_mode -> (* bg? [for tty] *)
                 maybe pid -> (* pipeline pgrp *)
                 pipeline_info ->
                 either string (os_state 'a * pipeline_info * pid) -/
def run_pipe_loop [OS α]
    (s0 : os_state α)
    (stmts : List stmt)
    (fdPrev : Smoosh.fd)
    (bg : bg_mode)
    (pgid : Option pid)
    (pipeline : pipeline_info) :
    Except String (os_state α × pipeline_info × pid) :=
  match stmts with
  | [] => .ok (fork_pipe_subshell (α := α) s0 stmt.Done bg pgid true pipeline)
  | [st] =>
      -- last one
      let (s1, pipeline', lastPid) :=
        fork_pipe_subshell (α := α)
          s0
          (with_redirs
            (try_avoid_fork st)
            [ .ERDup .ToFD .CloseOrig STDIN (some fdPrev) ])
          bg
          pgid
          true
          pipeline
      let s2 := close_fd s1 fdPrev
      .ok (s2, List.reverse ((lastPid, st) :: pipeline'), lastPid)
  | st :: stmts' =>
      match pipe s0 with
      | .error err => .error err
      | .ok (s1, fdNext, fdWrite) =>
          let (s2, pipeline', childPid) :=
            fork_pipe_subshell
              s1
              (with_redirs
                (close_fd_and_then fdNext st)
                [ .ERDup .ToFD .CloseOrig STDIN  (some fdPrev)
                , .ERDup .ToFD .CloseOrig STDOUT (some fdWrite) ])
              bg
              pgid
              false
              pipeline
          let s3 := close_fd s2 fdPrev
          let s4 := close_fd s3 fdWrite
          run_pipe_loop s4 stmts' fdNext bg pgid ((childPid, st) :: pipeline')

/-- Lem: val run_pipe : forall 'a. OS 'a =>
                 os_state 'a ->
                 list stmt ->
                 bg_mode -> (* bg? [for tty] *)
                 either string (os_state 'a * pipeline_info * pid) -/
def run_pipe [OS α]
    (s0 : os_state α)
    (stmts : List stmt)
    (bg : bg_mode) :
    Except String (os_state α × pipeline_info × pid) :=
  match stmts with
  | [] => .ok (fork_pipe_subshell s0 stmt.Done bg none true [])
  | [st] => .ok (fork_pipe_subshell s0 st bg none true [])
  | st :: stmts' =>
      match pipe s0 with
      | .error err => .error err
      | .ok (s1, fdNext, fdWrite) =>
          let (s2, pipeline, childPid) :=
            fork_pipe_subshell
              s1
              (with_redirs
                (close_fd_and_then fdNext st)
                [ .ERDup .ToFD .CloseOrig STDOUT (some fdWrite) ])
              bg
              none
              false
              []
          let s3 := close_fd s2 fdWrite
          run_pipe_loop s3 stmts' fdNext bg (some childPid) ((childPid, st) :: pipeline)

-- (* Parameters and the environment *************************************)
/-- Lem: val xtrace : forall 'a. OS 'a => string -> os_state 'a -> os_state 'a -/
def xtrace [OS α] (msg : String) (os : os_state α) : os_state α :=
  if Set.Set.member .Sh_xtrace os.sh.opts && msg ≠ "" then
    write_stderr (ps4 os ++ msg ++ "\n") os
  else
    os
/-- Lem: val checked_set_param : forall 'a. OS 'a =>
                  string -> symbolic_string -> os_state 'a -> os_state 'a -/
def checked_set_param [OS α]
    (x : String) (v : symbolic_string) (os0 : os_state α) : os_state α :=
  let os1 := internal_set_param x v os0
  let os2 :=
    -- dash vs bash behaviour comment left as-is
    if Set.Set.member .Sh_allexport os1.sh.opts then
      { os1 with sh := { os1.sh with exported := Set.Set.insert x os1.sh.exported } }
    else
      os1
  -- special variable handling
  if x = "OPTIND" then
    { os2 with sh := { os2.sh with optoff := none } }
  else if x = "PS1" then
    set_ps1 os2 v
  else if x = "PS2" then
    set_ps2 os2 v
  else if x = "PATH" then
    clear_hash os2
  else
    os2
/-- Lem: val set_param : forall 'a. OS 'a =>
                  string -> symbolic_string -> os_state 'a -> either string (os_state 'a) -/
def set_param [OS α]
    (x : String) (v : symbolic_string) (os0 : os_state α) : Except String (os_state α) :=
  match check_param x os0 with
  | some err => .error err
  | none     => .ok (checked_set_param (α := α) x v os0)

-- (* Shell options ******************************************************)
/-- Lem: val set_sh_opt : forall 'a. OS 'a => os_state 'a -> sh_opt -> os_state 'a -/
def set_sh_opt [OS α] (os0 : os_state α) (opt : sh_opt) : os_state α :=
  let os1 :=
    if List.elem opt unimplemented_sh_opts then
      write_stderr ("set: warning: " ++ string_of_sh_opt opt ++ " is unimplemented\n") os0
    else
      os0
  let os2 :=
    if opt = .Sh_monitor then
      -- If -m: ignore SIGTTIN/SIGTTOU/SIGTSTP
      let os2' := set_job_control os1 true
      let os3  := handle_signal os2' .SIGTTOU (some [])
      let os4  := handle_signal os3  .SIGTTIN (some [])
      let os5  := handle_signal os4  .SIGTSTP (some [])
      os5
    else
      os1
  { os2 with sh := { os2.sh with opts := Set.Set.insert opt os2.sh.opts } }

/-- Lem: val unset_sh_opt : forall 'a. OS 'a => os_state 'a -> sh_opt -> os_state 'a -/
def unset_sh_opt [OS α] (os0 : os_state α) (opt : sh_opt) : os_state α :=
  let os1 :=
    if opt = .Sh_monitor then
      let os1' := set_job_control os0 false
      let os2  := handle_signal os1' .SIGTTOU none
      let os3  := handle_signal os2  .SIGTTIN none
      let os4  := handle_signal os3  .SIGTSTP none
      os4
    else
      os0
  { os1 with sh := { os1.sh with opts := Set.Set.delete opt os1.sh.opts } }
