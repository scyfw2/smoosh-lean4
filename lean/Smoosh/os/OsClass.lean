import Smoosh.Prelude.All
import Smoosh.Map
import Smoosh.Set
import Smoosh.os.OsState
import Smoosh.Num
import Smoosh.os.FsState
import Smoosh.os.ParamHelper
import Smoosh.os.Hashing
import Smoosh.os.LogHis
import Smoosh.os.Concret
-- CHECKED
universe u v

open Smoosh

/-- Lem: step_fun 'a type -/
abbrev step_fun (α : Type u) :=
  os_state α →
  checking_mode →
  stmt →
  (evaluation_step × os_state α × stmt)

/-- Lem: signal_mode type -/
inductive signal_mode where
  | SignalProcess
  | SignalProcessGroup
deriving DecidableEq, Repr

/-- Lem: val signal_processgroup : signal_mode -> bool -/
def signal_processgroup : signal_mode → Bool
  | .SignalProcess      => false
  | .SignalProcessGroup => true

/-- Lem: escape_mode type -/
inductive escape_mode where
  | BackslashEscapes
  | NoEscapes
deriving DecidableEq, Repr

/-- Lem: val allow_escapes : escape_mode -> bool -/
def allow_escapes : escape_mode → Bool
  | .BackslashEscapes => true
  | .NoEscapes        => false

/-- Lem: class ( OS 'a ) -/
class OS (α : Type u) where
  -- FOR SYMBOLIC TRACKING
  os_tick : os_state α → os_state α

  -- PARSER INTERACTIONS
  os_set_ps1 : os_state α → symbolic_string → os_state α
  os_set_ps2 : os_state α → symbolic_string → os_state α

  -- SYSTEM CALLS
  os_getpwnam : os_state α → String → Option String

  os_execve :
    os_state α →
    symbolic_string →   -- cmd
    symbolic_string →   -- argv[0]
    List symbolic_string →  -- argv w/o cmd
    env →
    binsh_mode →
    (os_state α × Except String stmt)

  os_fork_and_subshell :
    os_state α →
    stmt →
    bg_mode →
    Option pid →   -- pgrp id
    Bool →         -- do job control?
    (os_state α × pid)

  os_exit : os_state α → os_state α

  -- don't call this directly; call wait_for_pid
  os_waitpid :
    step_fun α →     -- opportunistic scheduling in symbolic mode
    os_state α → pid →
    (os_state α × Option (Except evaluation_step Nat))

  os_waitchild : os_state α → (os_state α × Option (pid × job_status))

  os_handle_signal : os_state α → signal → Option symbolic_string → os_state α
  os_signal_pid : os_state α → signal → pid → signal_mode → (os_state α × Bool)
  os_pending_signal : os_state α → Except String (os_state α × Option signal)

  os_tc_setfg : os_state α → pid → (os_state α × Bool)
  os_set_job_control : os_state α → Bool → os_state α

  os_times :
    os_state α →
    (String × String × String × String)  -- utime, stime, utime+children, stime+children

  os_get_umask : os_state α → perms
  os_set_umask : os_state α → perms → os_state α

  -- FS CALLS
  os_physical_cwd : os_state α → String
  os_chdir : os_state α → path → (os_state α × Option String)
  os_readdir : os_state α → path → Set.Set (path × file Unit)
  os_file_exists : os_state α → path → Bool

  -- stat calls
  os_file_type : os_state α → path → Option file_type
  -- lstat (follow links)
  os_file_type_follow : os_state α → path → Option file_type
  os_file_size : os_state α → path → Option Nat
  os_file_perms : os_state α → path → Option perms
  os_file_mtime : os_state α → path → Option Rat -- Real noncomputable
  os_file_number : os_state α → path → Option (Int × Int)

  os_is_tty : os_state α → fd → Bool
  os_is_readable : os_state α → path → Bool
  os_is_writeable : os_state α → path → Bool
  os_is_executable : os_state α → path → Bool

  os_write_fd : os_state α → fd → String → Option (os_state α)

  os_read_all_fd :
    step_fun α →
    os_state α → fd →
    (os_state α × Except evaluation_step (Option String))

  os_read_line_fd :
    os_state α → fd → escape_mode →
    (os_state α × read_result String)

  os_close_fd : os_state α → fd → os_state α

  os_pipe : os_state α → Except String (os_state α × fd × fd)

  os_open_file_for_redir :
    os_state α → redir_type → symbolic_string →
    (os_state α × Except String fd)

  os_open_heredoc : os_state α → String → Except String (os_state α × fd)

  os_close_and_save_fd : os_state α → fd → (os_state α × Except String saved_fds)

  os_renumber_fd :
    os_state α →
    orig_fd_action →
    fd → fd →
    (os_state α × Except String saved_fds)

  os_restore_fd : os_state α → fd → saved_fd_info → os_state α

-- /* Logging for syscalls ***********************************************/

/-
  for -d[...] and -o trace[...]

  this version is useful inside os instances (os_*.lem), which can't
  recursively use their own typeclass

  we're using it here to just bootstrap some logging
-/

variable
{α : Type u}
{β : Type v}

/-- Lem: val unlogged_write_stderr : forall 'a. OS 'a => string -> os_state 'a -> os_state 'a -/
def unlogged_write_stderr [OS α] (s : String) (os : os_state α) : os_state α :=
  match OS.os_write_fd os STDERR s with
  | some os' => os'
  | none     => os

/-- Lem: val log_trace : forall 'a. OS 'a => trace_tag -> string -> os_state 'a -> os_state 'a -/
def log_trace [OS α] : trace_tag → String → os_state α → os_state α :=
  log_trace_with unlogged_write_stderr

/-- Lem: val log_syscall : forall 'a. OS 'a => string -> os_state 'a -> os_state 'a -/
def log_syscall [OS α] (msg : String) (os : os_state α) : os_state α :=
  log_trace .Trace_syscall msg os

/-- Lem: val wrap_syscall : forall 'a 'b. OS 'a => string -> os_state 'a -> (os_state 'a -> 'b) -> 'b -/
def wrap_syscall [OS α]
    (msg : String) (os : os_state α) (f : os_state α → β) : β :=
  f (log_syscall msg os)

/-- Lem: val wrap_syscall_path : forall 'a 'b. OS 'a => string -> path -> os_state 'a -> (os_state 'a -> path -> 'b) -> 'b -/
def wrap_syscall_path [OS α]
    (msg : String) (p : path) (os : os_state α) (f : os_state α → path → β) : β :=
  f (log_syscall (msg ++ "(" ++ p ++ ")") os) p

/-- Lem: val wrap_syscall_fd : forall 'a 'b. OS 'a => string -> fd -> os_state 'a -> (os_state 'a -> fd -> 'b) -> 'b -/
def wrap_syscall_fd [OS α]
    (msg : String) (fd : fd) (os : os_state α) (f : os_state α → Smoosh.fd → β) : β :=
  f (log_syscall (msg ++ "(" ++ stringFromNat fd ++ ")") os) fd

-- /* Wrapped syscalls ***************************************************/

/-- tick -/
def tick [OS α] (os : os_state α) : os_state α :=
  { (OS.os_tick os) with
    fuel := Option.map (fun n => if n > 0 then n - 1 else 0) os.fuel }

/-- set_ps1 / set_ps2 -/
def set_ps1 [OS α] (os : os_state α) : symbolic_string → os_state α :=
  wrap_syscall "set_ps1" os OS.os_set_ps1
def set_ps2 [OS α] (os : os_state α) : symbolic_string → os_state α :=
  wrap_syscall "set_ps2" os OS.os_set_ps2

/-- getpwnam -/
def getpwnam [OS α] (os : os_state α) (user : String) : Option String :=
  OS.os_getpwnam (log_syscall ("getpwnam(" ++ user ++ ")") os) user

/-- execve -/
def execve [OS α] (os : os_state α) (cmd : symbolic_string) :=
  OS.os_execve (log_syscall ("execve(" ++ string_of_symbolic_string cmd ++ ")") os) cmd
/-- fork_and_subshell -/
def fork_and_subshell [OS α] (os : os_state α) :=
  wrap_syscall "fork_and_subshell" os OS.os_fork_and_subshell
/-- exit -/
def exit [OS α] (os : os_state α) :=
  wrap_syscall "exit" os OS.os_exit

/-- waitpid / waitchild -/
def waitpid [OS α] (step : step_fun α) (os : os_state α) (pidNum : pid) :=
  OS.os_waitpid step (log_syscall ("waitpid(" ++ stringFromNat pidNum ++ ")") os) pidNum
def waitchild [OS α] (os : os_state α) :=
  wrap_syscall "waitchild" os OS.os_waitchild

/-- handle_signal / signal_pid / pending_signal -/
def handle_signal [OS α] (os : os_state α) (sig : signal) :=
  OS.os_handle_signal (log_syscall ("handle_signal(" ++ string_of_signal sig ++ ")") os) sig
def signal_pid [OS α]
    (os : os_state α) (sig : signal) (pidNum : pid) (mode : signal_mode) :=
  let pid_s :=
    (if signal_processgroup mode then "-" else "") ++ stringFromNat pidNum
  let msg :=
    "signal_pid(" ++ string_of_signal sig ++ ", " ++ pid_s ++ ")"
  OS.os_signal_pid (log_syscall msg os) sig pidNum mode
def pending_signal [OS α] (os : os_state α) :=
  wrap_syscall "pending_signal" os OS.os_pending_signal

/-- tc_setfg / set_job_control -/
def tc_setfg [OS α] (os : os_state α) (pidNum : pid) :=
  OS.os_tc_setfg (log_syscall ("tc_setfg(" ++ stringFromNat pidNum ++ ")") os) pidNum
def set_job_control [OS α] (os : os_state α) (on : Bool) :=
  let msg :=
    "set_job_control(" ++ (if on then "on" else "off") ++ ")"
  OS.os_set_job_control (log_syscall msg os) on

/-- Lem: val times : forall 'a. OS 'a => os_state 'a ->
               (string (* utime *)            * string (* stime *) *
                string (* utime + children *) * string (* stime + children *))
-/
def times [OS α] (os : os_state α) :=
  wrap_syscall "times" os OS.os_times
/-- Lem: get_umask -/
def get_umask [OS α] (os : os_state α) :=
  wrap_syscall "get_umask" os OS.os_get_umask
/-- Lem: set_umask -/
def set_umask [OS α] (os : os_state α) :=
  wrap_syscall "set_umask" os OS.os_set_umask

/-- Lem: physical_cwd -/
def physical_cwd [OS α] (os : os_state α) :=
  wrap_syscall "physical_cwd" os OS.os_physical_cwd
/-- Lem: chdir -/
def chdir [OS α] (os : os_state α) (p : path) :=
  wrap_syscall_path "chdir" p os OS.os_chdir
/-- Lem: val readdir : forall 'a. OS 'a => os_state 'a -> path -> set (path * file unit) -/
def readdir [OS α] (os : os_state α) (p : path) :=
  wrap_syscall_path "readdir" p os OS.os_readdir
/-- Lem: file_exists -/
def file_exists [OS α] (os : os_state α) (p : path) :=
  wrap_syscall_path "file_exists" p os OS.os_file_exists
/-- Lem: file_type (name already declared)-/
def file_typeF [OS α] (os : os_state α) (p : path) :=
  wrap_syscall_path "file_type" p os OS.os_file_type
/-- Lem: file_type_follow -/
def file_type_follow [OS α] (os : os_state α) (p : path) :=
  wrap_syscall_path "file_type_follow" p os OS.os_file_type_follow
/-- Lem: file_size -/
def file_size [OS α] (os : os_state α) (p : path) :=
  wrap_syscall_path "file_size" p os OS.os_file_size
/-- Lem: file_perms -/
def file_perms [OS α] (os : os_state α) (p : path) :=
  wrap_syscall_path "file_perms" p os OS.os_file_perms
/-- Lem: is_readable -/
def is_readable [OS α] (os : os_state α) (p : path) :=
  wrap_syscall_path "is_readable" p os OS.os_is_readable
/-- Lem: is_writeable -/
def is_writeable [OS α] (os : os_state α) (p : path) :=
  wrap_syscall_path "is_writeable" p os OS.os_is_writeable
/-- Lem: is_executable -/
def is_executable [OS α] (os : os_state α) (p : path) :=
  wrap_syscall_path "is_executable" p os OS.os_is_executable
/-- Lem: file_mtime -/
def file_mtime [OS α] (os : os_state α) (p : path) :=
  wrap_syscall_path "file_mtime" p os OS.os_file_mtime
/-- Lem: file_number -/
def file_number [OS α] (os : os_state α) (p : path) :=
  wrap_syscall_path "file_number" p os OS.os_file_number
/-- Lem: is_tty -/
def is_tty [OS α] (os : os_state α) (fdNum : Smoosh.fd) :=
  wrap_syscall_fd "is_tty" fdNum os OS.os_is_tty
/-- Lem: write_fd -/
def write_fd [OS α] (os : os_state α) (fdNum : Smoosh.fd) :=
  wrap_syscall_fd "write_fd" fdNum os OS.os_write_fd
/-- Lem: read_all_fd -/
def read_all_fd [OS α] (step : step_fun α) (os : os_state α) (fdNum : Smoosh.fd) :=
  wrap_syscall_fd "read_all_fd" fdNum os (fun os1 => OS.os_read_all_fd step os1)
/-- Lem: read_line_fd -/
def read_line_fd [OS α] (os : os_state α) (fdNum : Smoosh.fd) :=
  wrap_syscall_fd "read_line_fd" fdNum os OS.os_read_line_fd
/-- Lem: close_fd -/
def close_fd [OS α] (os : os_state α) (fdNum : Smoosh.fd) :=
  wrap_syscall_fd "close_fd" fdNum os OS.os_close_fd
/-- Lem: pipe -/
def pipe [OS α] (os : os_state α) :=
  wrap_syscall "pipe" os OS.os_pipe
/-- Lem: open_file_for_redir -/
def open_file_for_redir [OS α]
    (os : os_state α) (rt : redir_type) (spath : symbolic_string) :=
  let msg := "open_file_for_redir(" ++ string_of_symbolic_string spath ++ ")"
  OS.os_open_file_for_redir (log_syscall msg os) rt spath
/-- Lem: open_heredoc -/
def open_heredoc [OS α] (os : os_state α) :=
  wrap_syscall "open_heredoc" os OS.os_open_heredoc
/-- Lem: close_and_save_fd -/
def close_and_save_fd [OS α] (os : os_state α) (fdNum : Smoosh.fd) :=
  wrap_syscall_fd "close_and_save_fd" fdNum os OS.os_close_and_save_fd
/-- Lem: renumber_fd -/
def renumber_fd [OS α]
    (os : os_state α) (action : orig_fd_action) (origFd wantedFd : Smoosh.fd) :=
  let msg :=
    "renumber_fd(" ++ stringFromNat origFd ++ ", " ++ stringFromNat wantedFd ++ ")"
  OS.os_renumber_fd (log_syscall msg os) action origFd wantedFd
/-- Lem: restore_fd -/
def restore_fd [OS α] (os : os_state α) (fdNum : Smoosh.fd) :=
  wrap_syscall_fd "restore_fd" fdNum os OS.os_restore_fd
