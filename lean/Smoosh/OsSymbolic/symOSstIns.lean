import Smoosh.os.All
import Smoosh.Prelude.All
import Smoosh.OsSymbolic.symFSst
import Smoosh.OsSymbolic.symOSst
import Smoosh.OsSymbolic.symProcHd
import Smoosh.Signal
-- TODO: mutual partial
open Smoosh
namespace Smoosh

-- (* SYMBOLIC OS STATE INSTANCE *****************************************)
/-- Lem: val symbolic_resolve_fd : symbolic -> fd -> maybe nat-/
def symbolic_resolve_fd (sym : symbolic) (fd : fd) : Option Nat :=
  match Map.lookup fd sym.sh_fds with
  | some (fd_tgt.FIFO fifo_num) => some fifo_num
  | _                           => none

/-- Lem: val mkfifo : symbolic -> symbolic * fifo_num-/
def mkfifo (sym : symbolic) : symbolic × fifo_num :=
  let fifo_num : Nat := sym.fifos.length
  ( { sym with fifos := sym.fifos ++ [""] }, fifo_num )

/-- Lem: val write_fifo : symbolic -> fifo_num -> string -> maybe (symbolic) -/
def write_fifo (sym : symbolic) (fifo_num : fifo_num) (s : String) : Option symbolic :=
  match adjust_nth sym.fifos fifo_num (fun fifo_cts => (fifo_cts ++ s, ())) with
  | none => none
  | some (new_fifos, ()) => some { sym with fifos := new_fifos }

/-- Lem: val read_fifo : symbolic -> fifo_num -> maybe (symbolic * string) -/
def read_fifo (sym : symbolic) (fifo_num : fifo_num) : Option (symbolic × String) :=
  match adjust_nth sym.fifos fifo_num (fun fifo_cts => ("", fifo_cts)) with
  | none => none
  | some (new_fifos, s) => some ({ sym with fifos := new_fifos }, s)

/-- Lem: val read_char_fifo : symbolic -> fifo_num -> maybe (symbolic * char) -/
def read_char_fifo (sym : symbolic) (fifo_num : fifo_num) : Option (symbolic × Char) :=
  let get_char (fifo_cts : String) : String × Option Char :=
    match toCharList fifo_cts with
    | []      => ("", none)
    | c :: cs => (toString cs, some c)
  match adjust_nth sym.fifos fifo_num get_char with
  | none => none
  | some (new_fifos, some c) => some ({ sym with fifos := new_fifos }, c)
  | some (_, none) => none

/-- Lem: val string_read_line_cl
    : list char -> escape_mode -> list char ->
      list char * list char * read_eof -/
def string_read_line_cl
    (cs : List Char) (escapes : escape_mode) (line : List Char)
    : List Char × List Char × read_eof :=
  match cs, escapes with
  -- terminator
  | [], _ => (line, [], .ReadEOF)
  | '\n' :: cs', _ => (line, cs', .ReadContinue)
  -- backslash
  | ['\\'], .BackslashEscapes => ('\\' :: line, [], .ReadEOF)
  | '\\' :: '\n' :: cs', .BackslashEscapes => string_read_line_cl cs' escapes line
  | '\\' :: c :: cs', .BackslashEscapes    => string_read_line_cl cs' escapes (c :: line)
  -- ordinary char
  | c :: cs', _ => string_read_line_cl cs' escapes (c :: line)

/-- Lem: val string_read_line
    : string -> escape_mode -> string * string * read_eof -/
def string_read_line (s : String) (escapes : escape_mode) : String × String × read_eof :=
  let (line_cs, rest, hit_eof) := string_read_line_cl (toCharList s) escapes []
  (toString (line_cs.reverse), toString rest, hit_eof)

/-- Lem: val symbolic_fresh_fd : fds -> fd -/
def symbolic_fresh_fd (sh_fds : fds) : fd :=
  match Set.Set.findMax (Map.domain sh_fds) with
  | none     => 0
  | some max => max + 1

/-- Lem: val symbolic_fds_reads_fifo : fifo_num -> fds -> bool -/
def symbolic_fds_reads_fifo (fifo_num : fifo_num) (fds : fds) : Bool :=
  let select_readers (_fd : fd) (tgt : fd_tgt) : Option fd_tgt :=
    match tgt with
    | fd_tgt.FIFO fifo_num' =>
        if fifo_num = fifo_num' then some (fd_tgt.FIFO fifo_num') else none
    | fd_tgt.Path _ => none
  let readers := Map.mapMaybe select_readers fds
  not (Map.null readers)

/-- Lem: val symbolic_has_reader : os_state symbolic -> fifo_num -> bool -/
def symbolic_has_reader (os : os_state symbolic) (fifo_num : fifo_num) : Bool :=
  -- STDOUT and STDERR always have readers, let's pretend
  fifo_num = 1 || fifo_num = 2 ||
  -- do any other processes read this FIFO?
  let rec go (pid : Nat) (ps : List proc) : Bool :=
    match ps with
    | [] => false
    | p :: ps' =>
        let rest := go (pid + 1) ps'
        if pid = os.symbolic.curpid then
          rest
        else
          match p with
          | proc.Zombie _ => rest
          | proc.Shell _ _ _ fds _ _ =>
              (symbolic_fds_reads_fifo fifo_num fds) || rest
  termination_by ps
  go 0 os.symbolic.procs

/-- Lem: val symbolic_fds_writes_fifo : fifo_num -> fds -> bool -/
def symbolic_fds_writes_fifo (fifo_num : fifo_num) (fds : fds) : Bool :=
  let select_writers (fd : fd) (tgt : fd_tgt) : Option fd_tgt :=
    match tgt with
    | fd_tgt.FIFO fifo_num' =>
        if fd ≠ STDIN && fifo_num = fifo_num' then some (fd_tgt.FIFO fifo_num') else none
    | fd_tgt.Path _ => none
  let writers := Map.mapMaybe select_writers fds
  not (Map.null writers)

/-- Lem: val symbolic_writes_fifo : fifo_num -> proc -> bool -/
def symbolic_writes_fifo (fifo_num : fifo_num) (p : proc) : Bool :=
  match p with
  | proc.Zombie _ => false
  | proc.Shell _ _ _ fds _ _ => symbolic_fds_writes_fifo fifo_num fds

/-- Lem: val symbolic_find_writer : os_state symbolic -> fifo_num -> list pid -/
def symbolic_find_writer (os : os_state symbolic) (fifo_num : fifo_num) : List pid :=
  let rec go (pid : Nat) (ps : List proc) (accRev : List Smoosh.pid) : List Smoosh.pid :=
    match ps with
    | [] => accRev.reverse
    | p :: ps' =>
        let accRev :=
          if pid ≠ os.symbolic.curpid && symbolic_writes_fifo fifo_num p
          then pid :: accRev
          else accRev
        go (pid + 1) ps' accRev
  termination_by ps
  go 0 os.symbolic.procs []

/-
  A recursive knot (mutual recursion):
    writing to an FD can cause SIGPIPE
    sending a signal might need to write to an FD
-/

def update {α : Type u} : List α → Nat → α → List α
  | [],      _i, _a => []
  | _ :: xs, 0,  a  => a :: xs
  | x :: xs, i+1, a => x :: update xs i a

mutual
  /-- Lem: symbolic_write_fd -/
  partial def symbolic_write_fd (os : os_state symbolic) (fd : fd) (s : String)
      : Option (os_state symbolic) :=
    match symbolic_resolve_fd os.symbolic fd with
    | some fifo_num =>
        match write_fifo os.symbolic fifo_num s with
        | none => none
        | some symbolic' =>
            if symbolic_has_reader os fifo_num then
              some { os with symbolic := symbolic' }
            else
              -- send SIGPIPE
              let (os', _sent) := symbolic_signal_pid os .SIGPIPE os.symbolic.curpid signal_mode.SignalProcess
              some os'
    | none => none
  /-- Lem: symbolic_write_stderr -/
  partial def symbolic_write_stderr (s : String) (os : os_state symbolic) : os_state symbolic :=
    match symbolic_write_fd os STDERR s with
    | none => os
    | some os' => os'
  /-- Lem: symbolic_log_trace -/
  partial def symbolic_log_trace (tr : trace_tag) (msg : String) (os : os_state symbolic)
      : os_state symbolic :=
    log_trace_with symbolic_write_stderr tr msg os
  /-- Lem: proc_receive_signal -/
  partial def proc_receive_signal
      (os0 : os_state symbolic) (sig : signal) (pid : pid) (_as_pg : signal_mode) (p : proc)
      : os_state symbolic × Bool :=
    match p with
    | proc.Zombie _ec => (os0, false)
    | proc.Shell status c proc_sh proc_fds stepped pending =>
        let (os1, p') : os_state symbolic × proc :=
          match Map.lookup sig proc_sh.traps with
          | none =>
              match signal_default_behavior sig with
              | .Terminate actions =>
                  let os1 :=
                    if actions then
                      symbolic_log_trace .Trace_unspec
                        "Implementation-defined abnormal termination actions, such as creation of a core file, may also occur."
                        os0
                    else os0
                  let ec := 128 + Signal_platform.platform_int_of_signal sig
                  (os1, proc.Zombie ec)
              | .Ignore =>
                  let os1 :=
                    symbolic_log_trace .Trace_traps
                      (string_of_signal sig ++ " ignored by process with pid " ++ stringFromNat pid)
                      os0
                  (os1, p)
              | .Stop =>
                  (os0, proc.Shell proc_status.Proc_Stopped c proc_sh proc_fds stepped pending)
              | .Continue =>
                  (os0, proc.Shell proc_status.Proc_Running c proc_sh proc_fds stepped pending)
          | some _ =>
              -- recorded as pending
              (os0, proc.Shell status c proc_sh proc_fds stepped (pending ++ [sig]))

        let procs' := update os1.symbolic.procs pid p'
        ( { os1 with symbolic := { os1.symbolic with procs := procs' } }, true )
  /-- Lem: symbolic_signal_pid -/
  partial def symbolic_signal_pid
      (os0 : os_state symbolic) (sig : signal) (pid : pid) (as_pg : signal_mode)
      : os_state symbolic × Bool :=
    let os1 := proc_save_state os0
    match index os1.symbolic.procs pid with
    | none => (os1, false)
    | some p => proc_receive_signal os1 sig pid as_pg p

end

/-- Lem: symbolic_step_pid -/
def symbolic_step_pid
    (step_eval : os_state symbolic → checking_mode → stmt → evaluation_step × os_state symbolic × stmt)
    (os0 : os_state symbolic) (pid : pid)
    : os_state symbolic × Option (Except evaluation_step Nat) :=
  let (os1, selected) := proc_select os0 pid
  match selected with
  | selected_proc.SProc_NotFound => (os1, none)
  | selected_proc.SProc_Done ec  => (os1, some (Except.ok ec))
  | selected_proc.SProc_Stopped  =>
      let os2 :=
        symbolic_write_stderr ("warning: process with pid " ++ stringFromNat pid ++ " is stopped") os1
      (os2, none)
  | selected_proc.SProc_Running st (proc_stepped.Stepped true) =>
      (os1, some (Except.error (.XSNested (.XSSimple "already stepped") (.XSProc pid st))))
  | selected_proc.SProc_Running st (proc_stepped.Stepped false) =>
      let (step, os2, st') := step_eval os1 .Unchecked st
      let (os3, res) : os_state symbolic × Option (Except evaluation_step Nat) :=
        match st' with
        | .Done =>
            let (os3, m_handler) := exit_trap os2
            match m_handler with
            | some handler =>
                ( proc_set_stmt os3 pid handler
                , some (Except.error (.XSNested (.XSSimple "trapped on EXIT") (.XSProc pid handler))) )
            | none =>
                let ec := os3.sh.exit_code
                ( proc_set_ec os3 pid ec
                , some (Except.ok ec) )
        | _ =>
            ( proc_set_stmt os2 pid st'
            , some (Except.error (.XSNested step (.XSProc pid st'))) )
      -- restore the original state
      ( (proc_select os3 os0.symbolic.curpid).1, res )

/-- Lem: symbolic_file_type -/
def symbolic_file_type (os : os_state symbolic) (path : String) : Option file_type :=
  match symbolic_fs_resolve_path os.symbolic.fs_root path with
  | none => none
  | some .File     => some .FileRegular
  | some (.Dir _)  => some .FileDirectory

/-- Lem: symbolic_file_type_follow -/
def symbolic_file_type_follow (os : os_state symbolic) (path : String) : Option file_type :=
  symbolic_file_type os path



instance : OS symbolic where
  os_tick os := symbolic_clear_stepped os

  -- don't actually send these to libdash
  os_set_ps1 os _new_ps1 := os
  os_set_ps2 os _new_ps2 := os

  os_getpwnam os u := Map.lookup u os.symbolic.passwd

  os_execve os _prog _prog_argv0 _argv _env _binsh :=
    (os, Except.error "symbolic execve unimplemented")

  os_fork_and_subshell os st _bg _pgid _jc :=
    let proc_num := os.symbolic.procs.length
    let (subsh, _handlers) := prepare_subshell os.sh
    let p : proc :=
      proc.Shell proc_status.Proc_Running (try_avoid_fork st) subsh os.symbolic.sh_fds
        (proc_stepped.Stepped false) no_signals
    ( { os with symbolic := { os.symbolic with procs := os.symbolic.procs ++ [p] } }
    , proc_num )

  os_exit os0 :=
    proc_set_ec os0 os0.symbolic.curpid os0.sh.exit_code

  os_waitpid step_eval os0 pid :=
    symbolic_step_pid step_eval os0 pid

  os_waitchild os0 := (os0, none)

  os_handle_signal os _signal _action := os

  os_signal_pid os0 sig pid as_pg :=
    symbolic_signal_pid os0 sig pid as_pg

  os_pending_signal os0 :=
    let m_procs' :=
      adjust_nth os0.symbolic.procs os0.symbolic.curpid (fun p =>
        match p with
        | proc.Zombie _ec => (p, none)
        | proc.Shell _status _stmt _sh _fds _stepped [] => (p, none)
        | proc.Shell status stmt sh fds stepped (sig :: pending) =>
            (proc.Shell status stmt sh fds stepped pending, some sig))
    match m_procs' with
    | none =>
        .error
          ("os_pending_signal: couldn't find current process " ++ stringFromNat os0.symbolic.curpid)
    | some (procs', m_sig) =>
        .ok ( { os0 with symbolic := { os0.symbolic with procs := procs' } }
        , m_sig )

  os_tc_setfg os0 _pid := (os0, false)

  os_set_job_control os0 _on := os0

  os_times _os0 := ("0m0s", "0m0s", "0m0s", "0m0s")

  os_get_umask os0 := os0.symbolic.umask

  os_set_umask os0 mask :=
    { os0 with symbolic := { os0.symbolic with umask := mask } }

  os_readdir os path :=
    match symbolic_fs_resolve_dir os.symbolic.fs_root path with
    | none => Set.Set.empty
    | some fs =>
        Set.Set.map
        (fun (p : Smoosh.path × file symbolic_fs) =>
          let (name, f) := p
          ( name
          , match f with
            | .File  => .File
            | .Dir _ => .Dir () ))
        (Map.toSetBy compare_by_first fs.contents)

  os_physical_cwd os := os.sh.cwd

  os_chdir os path :=
    match symbolic_fs_resolve_dir os.symbolic.fs_root path with
    | none    => (os, some ("no such directory: " ++ path))
    | some _  => ({ os with sh := { os.sh with cwd := path } }, none)

  os_file_exists os path :=
    match symbolic_fs_resolve_path os.symbolic.fs_root path with
    | none   => false
    | some _ => true

  os_file_size os path :=
    match symbolic_fs_resolve_path os.symbolic.fs_root path with
    | none        => none
    | some (.Dir _) => some 512
    | some .File    => some 1

  os_file_perms os path :=
    match symbolic_fs_resolve_path os.symbolic.fs_root path with
    | none        => none
    | some (.Dir _) => some (invert_perms default_umask)
    | some .File    => some (invert_perms default_umask)

  os_file_type os path := symbolic_file_type os path
  os_file_type_follow os path := symbolic_file_type_follow os path

  os_is_tty os fd :=
    match symbolic_resolve_fd os.symbolic fd with
    | some fifo_num =>
        List.elem fifo_num [STDIN, STDOUT, STDERR] && is_interactive os
    | none => false

  os_is_readable os path :=
    match symbolic_fs_resolve_path os.symbolic.fs_root path with
    | none   => false
    | some _ => true

  os_is_writeable os path :=
    match symbolic_fs_resolve_path os.symbolic.fs_root path with
    | none   => false
    | some _ => true

  os_is_executable os path :=
    match symbolic_fs_resolve_path os.symbolic.fs_root path with
    | none   => false
    | some _ => true

  os_file_mtime _os _path := none
  os_file_number _os _path := none

  os_write_fd := symbolic_write_fd

  os_read_all_fd step_eval os0 fd :=
    match symbolic_resolve_fd os0.symbolic fd with
    | some fifo_num =>
        let commit_read (os : os_state symbolic) :=
          match read_fifo os.symbolic fifo_num with
          | none => (os, Except.ok none)
          | some (symbolic', s) => ({ os with symbolic := symbolic' }, Except.ok (some s))
        match symbolic_find_writer os0 fifo_num with
        | [] => commit_read os0
        | pid :: _ =>
            let (os1, m_step) := symbolic_step_pid step_eval os0 pid
            match m_step with
            | none => commit_read os1
            | some (Except.error step) => (os1, Except.error step)
            | some (Except.ok _ec) => commit_read os1
    | none =>
        (os0, Except.ok none)

  os_read_line_fd os fd escapes :=
    match symbolic_resolve_fd os.symbolic fd with
    | some fifo_num =>
        match index os.symbolic.fifos fifo_num with
        | none => (os, .ReadError "broken pipe ")
        | some cts =>
            let (line, cts', hit_eof) := string_read_line cts escapes
            let commit_read :=
              ( { os with symbolic := { os.symbolic with fifos := update os.symbolic.fifos fifo_num cts' } }
              , .ReadSuccess line hit_eof )
            if not (read_eof_toBool hit_eof) then
              commit_read
            else
              match symbolic_find_writer os fifo_num with
              | [] => commit_read
              | pid :: _ => (os, .ReadBlocked pid)
    | none =>
        (os, .ReadError ("bad file descriptor " ++ stringFromNat fd))

  os_close_fd os fd :=
    { os with symbolic := { os.symbolic with sh_fds := Map.delete fd os.symbolic.sh_fds } }

  os_pipe os0 :=
    let (sym1, fifo_num) := mkfifo os0.symbolic
    let fd_read := symbolic_fresh_fd sym1.sh_fds
    let fds' := Map.insert fd_read (fd_tgt.FIFO fifo_num) sym1.sh_fds
    let fd_write := symbolic_fresh_fd fds'
    let fds'' := Map.insert fd_write (fd_tgt.FIFO fifo_num) fds'
    Except.ok ( { os0 with symbolic := { sym1 with sh_fds := fds'' } }
              , fd_read, fd_write )

  os_open_file_for_redir os0 _ty file :=
    let fd := symbolic_fresh_fd os0.symbolic.sh_fds
    let (os1, _, sfile) := concretize os0 file
    let sh_fds' := Map.insert fd (fd_tgt.Path sfile) os1.symbolic.sh_fds
    let os2 := { os1 with symbolic := { os1.symbolic with sh_fds := sh_fds' } }
    (os2, Except.ok fd)

  os_open_heredoc os0 s :=
    let (sym1, fifo_num) := mkfifo os0.symbolic
    let fd := symbolic_fresh_fd sym1.sh_fds
    let sym2 := { sym1 with sh_fds := Map.insert fd (fd_tgt.FIFO fifo_num) sym1.sh_fds }
    match write_fifo sym2 fifo_num s with
    | none => Except.error "broken pipe"
    | some sym3 => Except.ok ({ os0 with symbolic := sym3 }, fd)

  os_close_and_save_fd os0 fd :=
    let sym1 := { os0.symbolic with sh_fds := Map.delete fd os0.symbolic.sh_fds }
    let os1 := { os0 with symbolic := sym1 }
    match Map.lookup fd os0.symbolic.sh_fds with
    | none => (os1, Except.ok [])
    | some (fd_tgt.FIFO fifo_num) => (os1, Except.ok [(fd, saved_fd_info.Saved fifo_num)])
    | some (fd_tgt.Path _path) => (os1, Except.error "TODO 2018-08-24 symbolic path FDs unimplemented")

  os_renumber_fd os0 orig_action new_fd wanted_fd :=
    if new_fd = wanted_fd then
      (os0, Except.ok (if should_close_orig orig_action then [(wanted_fd, saved_fd_info.Close)] else []))
    else
      match Map.lookup new_fd os0.symbolic.sh_fds with
      | none => (os0, Except.error "broken pipe (tried to renumber closed fd)")
      | some new_tgt =>
          let saved :=
            match Map.lookup wanted_fd os0.symbolic.sh_fds with
            | none => []
            | some (fd_tgt.FIFO fifo_num) => [(wanted_fd, saved_fd_info.Saved fifo_num)]
            | some (fd_tgt.Path _path) => []
          let fds0 := Map.insert wanted_fd new_tgt os0.symbolic.sh_fds
          let fds1 := if should_close_orig orig_action then Map.delete new_fd fds0 else fds0
          ( { os0 with symbolic := { os0.symbolic with sh_fds := fds1 } }
          , Except.ok saved )

  os_restore_fd os0 fd info :=
    match info with
    | saved_fd_info.Saved fifo_num =>
        let fds := Map.insert fd (fd_tgt.FIFO fifo_num) os0.symbolic.sh_fds
        { os0 with symbolic := { os0.symbolic with sh_fds := fds } }
    | saved_fd_info.Close =>
        let fds := Map.delete fd os0.symbolic.sh_fds
        { os0 with symbolic := { os0.symbolic with sh_fds := fds } }

/-- Lem: val set_pwdir : string -> string -> os_state symbolic -> os_state symbolic -/
def set_pwdir (u d : String) (os : os_state symbolic) : os_state symbolic :=
  { os with
    symbolic := { os.symbolic with
      passwd := Map.insert u d os.symbolic.passwd } }

def fromMaybe {α : Type u} (default : α) : Option α → α
  | none => default
  | some x => x

/-- Lem: val get_stdout : os_state symbolic -> string -/
def get_stdout (os : os_state symbolic) : String :=
  fromMaybe "" (index os.symbolic.fifos 1)

/-- Lem: val get_stderr : os_state symbolic -> string -/
def get_stderr (os : os_state symbolic) : String :=
  fromMaybe "" (index os.symbolic.fifos 2)

/-- Lem: val symbolic_set_param : string -> string -> os_state symbolic -> os_state symbolic -/
def symbolic_set_param (x v : String) (os : os_state symbolic) : os_state symbolic :=
  match set_param x (symbolic_string_of_string v) os with
  | .error _err => os
  | .ok os'     => os'
