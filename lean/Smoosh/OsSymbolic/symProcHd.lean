import Smoosh.os.All
import Smoosh.Prelude.All
import Smoosh.OsSymbolic.symFSst
import Smoosh.OsSymbolic.symOSst

open Smoosh

/-- Lem: val proc_exit_status : proc -> maybe nat -/
def proc_exit_status : proc → Option Nat
  | proc.Shell _ _ _ _ _ _ => none
  | proc.Zombie ec         => some ec

/-- Lem: val proc_alive : proc -> bool -/
def proc_alive (p : proc) : Bool :=
  match proc_exit_status p with
  | none   => true
  | some _ => false

/-- Lem: val proc_stepped : proc -> bool -/
def proc_stepped_bool : proc → Bool
  | proc.Shell _ _ _ _ (proc_stepped.Stepped b) _ => b
  | proc.Zombie _ => true  -- since it can't step anyway

/-- Lem: val proc_stmt : os_state symbolic -> pid -> stmt -/
def proc_stmt (os : os_state symbolic) (pid : pid) : stmt :=
  match index os.symbolic.procs pid with
  | none => .Done
  | some (proc.Zombie ec) =>
      simple_command "exit"
        [symbolic_string_of_string (stringFromNat ec)]
        Map.empty
  | some (proc.Shell _ st _ _ _ _) => st

/-- Lem: val symbolic_clear_stepped : os_state symbolic -> os_state symbolic -/
def symbolic_clear_stepped (os : os_state symbolic) : os_state symbolic :=
  { os with
    symbolic :=
      { os.symbolic with
        procs :=
          os.symbolic.procs.map (fun p =>
            match p with
            | proc.Zombie _ => p
            | proc.Shell status st sh fds _stepped pending =>
                proc.Shell status st sh fds (proc_stepped.Stepped false) pending) } }

/-- Lem: val proc_set_ec : os_state symbolic -> pid -> nat -> os_state symbolic -/
def proc_set_ec (os0 : os_state symbolic) (pid : pid) (ec : Nat) : os_state symbolic :=
  match adjust_nth os0.symbolic.procs pid (fun _p => (proc.Zombie ec, ())) with
  | none => os0
  | some (procs', ()) =>
      { os0 with symbolic := { os0.symbolic with procs := procs' } }

/-- Lem: val proc_set_stmt : os_state symbolic -> pid -> stmt -> os_state symbolic -/
def proc_set_stmt (os0 : os_state symbolic) (pid : pid) (st : stmt) : os_state symbolic :=
  let m_procs' :=
    adjust_nth os0.symbolic.procs pid (fun p =>
      match p with
      | proc.Zombie _ => (p, ())
      | proc.Shell status _old sh fds _stepped pending =>
          (proc.Shell status st sh fds (proc_stepped.Stepped true) pending, ()))
  match m_procs' with
  | none => os0
  | some (procs', ()) =>
      { os0 with symbolic := { os0.symbolic with procs := procs' } }

/-- records current shell state in the process table
  Lem: val proc_save_state : os_state symbolic -> os_state symbolic -/
def proc_save_state (os0 : os_state symbolic) : os_state symbolic :=
  let m_procs' :=
    adjust_nth os0.symbolic.procs os0.symbolic.curpid (fun p =>
      match p with
      | proc.Zombie _ => (p, ())
      | proc.Shell status c _sh _fds stepped pending =>
          (proc.Shell status c os0.sh os0.symbolic.sh_fds stepped pending, ()))
  match m_procs' with
  | none => os0
  | some (procs', ()) =>
      { os0 with symbolic := { os0.symbolic with procs := procs' } }

/-- Lem: selected_proc type -/
inductive selected_proc where
  | SProc_NotFound
  | SProc_Stopped
  | SProc_Done    : Nat → selected_proc
  | SProc_Running : stmt → proc_stepped → selected_proc

/-- Lem: val proc_select : os_state symbolic -> pid -> os_state symbolic * selected_proc -/
def proc_select (os0 : os_state symbolic) (pid : pid) : os_state symbolic × selected_proc :=
  let os1 := proc_save_state os0
  match index os1.symbolic.procs pid with
  | none => (os1, selected_proc.SProc_NotFound)
  | some (proc.Zombie ec) => (os1, selected_proc.SProc_Done ec)
  | some (proc.Shell proc_status.Proc_Stopped _c _sh' _fds' _stepped _pending) =>
      (os1, selected_proc.SProc_Stopped)
  | some (proc.Shell proc_status.Proc_Running c sh' fds' stepped _pending) =>
      let os2 := proc_save_state os1
      ( { os2 with
          sh := sh'
          symbolic := { os1.symbolic with sh_fds := fds', curpid := pid } }
      , selected_proc.SProc_Running c stepped
      )
