import Smoosh.os.All
import Smoosh.Prelude.All
import Smoosh.OsSymbolic.symFSst

open Smoosh

/-- Lem: fd_tgt type -/
inductive fd_tgt where
  | FIFO : Nat → fd_tgt
  | Path : path → fd_tgt
deriving Repr, DecidableEq

/-- Mapping of FD numbers
  Lem: fds type -/
abbrev fds := Map.map fd fd_tgt

/-- FIFO pipes for symbolic FDs -/
abbrev fifo := String
abbrev fifo_num := Nat

/-- Lem: proc_stepped type -/
inductive proc_stepped where
  | Stepped : Bool → proc_stepped
deriving Repr, DecidableEq

/-- INVARIANT: first to process is at the front of the list -/
abbrev proc_signals := List signal

/-- Lme: val no_signals : proc_signals -/
def no_signals : proc_signals := []

/-- Lem: proc_status type -/
inductive proc_status where
  | Proc_Running
  | Proc_Stopped
deriving Repr, DecidableEq

/-- Lem: proc type -/
inductive proc where
  | Shell  : proc_status → stmt → shell_state → fds → proc_stepped → proc_signals → proc
  | Zombie : Nat → proc   -- exit code

/-- Lem: symbolic type -/
structure symbolic where
  passwd : Map.map String String
  sh_fds : fds
  fs_root : fs
  fifos : List fifo
  procs : List proc
  umask : perms
  curpid : pid

/-- Lem: evaluation_trace_entry type -/
abbrev evaluation_trace_entry := evaluation_step × shell_state × symbolic × stmt
/-- Lem: evaluation_trace type -/
abbrev evaluation_trace := List evaluation_trace_entry × os_state symbolic

/-- Default FD mapping (FIFO 0/1/2 correspond to STDIN/STDOUT/STDERR) -/
def fds_default : fds :=
  Map.insert STDIN  (fd_tgt.FIFO 0) <|
  Map.insert STDOUT (fd_tgt.FIFO 1) <|
  Map.insert STDERR (fd_tgt.FIFO 2) <|
  Map.empty

/-- Lem: symbolic_empty : symbolic -/
def symbolic_empty : symbolic :=
  { sh_fds := fds_default
  , passwd := Map.empty
  , fs_root := fs_empty
  , fifos := ["", "", ""]
  , procs := [proc.Shell proc_status.Proc_Running .Done default_shell_state fds_default
                (proc_stepped.Stepped false) no_signals]
  , umask := default_umask
  , curpid := 0
  }

/-- Lem: os_empty : os_state symbolic -/
def os_empty : os_state symbolic :=
  { symbolic := symbolic_empty
  , sh := default_shell_state
  , log := []
  , fuel := some 500
  }
