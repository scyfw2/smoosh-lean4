/-
  Smoosh.OsSymbolic — Symbolic filesystem, processes, and OS instance
  Translated from `os_symbolic.lem` (866 lines).

  Provides the symbolic `OS` instance used for test execution:
  - `SymbolicFS`: in-memory filesystem with files and directories
  - `SymbolicProc`: process table with stdin/stdout/stderr FDs
  - `osWaitpid`: symbolic process stepping (runs subshells to completion)
  - `osExecve`: symbolic command execution (stubbed for external commands)
-/
import Smoosh.Os

/-! # Symbolic filesystem -/

inductive SymbolicFs where
  | fsFile (contents : String) (mode : UInt32) (mtime : Nat)
  | fsDir (entries : List (String × SymbolicFs))
  deriving Repr

def symbolicFsSubdir (fs : SymbolicFs) (name : String) : Option SymbolicFs :=
  match fs with
  | .fsFile _ _ _ => none
  | .fsDir entries =>
    match entries.find? (fun (n, _) => n == name) with
    | some (_, subfs) => some subfs
    | none => none

def symbolicFsResolveComps (fs : SymbolicFs) : List String → Option (FileUnit)
  | [] => match fs with
    | .fsFile _ _ _ => some .file
    | .fsDir _ => some (.dir "")
  | dir :: comps' =>
    match symbolicFsSubdir fs dir with
    | some fs' => symbolicFsResolveComps fs' comps'
    | none => none

def normalizeFsComponents (comps : List String) : List String :=
  comps.filter fun c => c != "" && c != "."

def symbolicFsResolvePath (fs : SymbolicFs) (path : String) : Option (FileUnit) :=
  let comps := normalizeFsComponents (splitStringOn false '/' path)
  symbolicFsResolveComps fs comps

def symbolicFsResolveNode (fs : SymbolicFs) (path : String) : Option SymbolicFs :=
  let comps := normalizeFsComponents (splitStringOn false '/' path)
  let rec traverse (fs : SymbolicFs) (comps : List String) : Option SymbolicFs :=
    match comps with
    | [] => some fs
    | dir :: rest =>
      match symbolicFsSubdir fs dir with
      | some subfs => traverse subfs rest
      | none => none
  traverse fs comps

def symbolicFsWrite (fs : SymbolicFs) (path : String) (content : String) (append : Bool) : Option SymbolicFs :=
  if path == "/dev/full" then none
  else if path == "/dev/null" then some fs
  else
  let comps := splitStringOn false '/' path
  let rec update (fs : SymbolicFs) (comps : List String) : Option SymbolicFs :=
    match comps with
    | [] => none
    | [name] =>
      match fs with
      | .fsFile _ _ _ => none
      | .fsDir entries =>
        let newEntry := match entries.find? (fun (n, _) => n == name) with
        | some (_, .fsFile oldContent oldMode oldMtime) =>
           if append then (name, .fsFile (oldContent ++ content) oldMode oldMtime)
           else (name, .fsFile content oldMode oldMtime)
        | some (_, .fsDir _) => (name, .fsFile content 0o644 0) -- Force overwrite?
        | none => (name, .fsFile content 0o644 0)
        let entries' := entries.filter (fun (n, _) => n != name)
        some (.fsDir (newEntry :: entries'))
    | dir :: rest =>
      match fs with
      | .fsFile _ _ _ => none
      | .fsDir entries =>
        match entries.find? (fun (n, _) => n == dir) with
        | some (_, subfs) =>
          match update subfs rest with
          | some subfs' =>
            let entries' := entries.filter (fun (n, _) => n != dir)
            some (.fsDir ((dir, subfs') :: entries'))
          | none => none
        | none => none
  update fs comps

/-- Create a directory at the given path in the symbolic filesystem.
    If mkdirP is true, creates intermediate directories (like mkdir -p). -/
def symbolicFsMkdir (fs : SymbolicFs) (path : String) (mkdirP : Bool) : Option SymbolicFs :=
  let comps := (splitStringOn false '/' path).filter (· != "")
  let rec create (fs : SymbolicFs) (comps : List String) : Option SymbolicFs :=
    match comps with
    | [] => some fs
    | [name] =>
      match fs with
      | .fsFile _ _ _ => none
      | .fsDir entries =>
        match entries.find? (fun (n, _) => n == name) with
        | some (_, .fsDir _) => some fs  -- already exists
        | some _ => none  -- file exists with same name
        | none =>
          some (.fsDir ((name, .fsDir []) :: entries))
    | dir :: rest =>
      match fs with
      | .fsFile _ _ _ => none
      | .fsDir entries =>
        match entries.find? (fun (n, _) => n == dir) with
        | some (_, subfs) =>
          match create subfs rest with
          | some subfs' =>
            let entries' := entries.filter (fun (n, _) => n != dir)
            some (.fsDir ((dir, subfs') :: entries'))
          | none => none
        | none =>
          if mkdirP then
            -- Create intermediate directory
            match create (.fsDir []) rest with
            | some subfs' => some (.fsDir ((dir, subfs') :: entries))
            | none => none
          else none
  create fs comps

/-- Remove a file or directory from the symbolic filesystem.
    If recursive is true, removes directories and their contents. -/
def symbolicFsRemove (fs : SymbolicFs) (path : String) (recursive : Bool) : Option SymbolicFs :=
  let comps := (splitStringOn false '/' path).filter (· != "")
  let rec remove (fs : SymbolicFs) (comps : List String) : Option SymbolicFs :=
    match comps with
    | [] => none
    | [name] =>
      match fs with
      | .fsFile _ _ _ => none
      | .fsDir entries =>
        match entries.find? (fun (n, _) => n == name) with
        | some (_, .fsDir _) =>
          if recursive then some (.fsDir (entries.filter (fun (n, _) => n != name)))
          else none  -- can't remove directory without -r
        | some _ => some (.fsDir (entries.filter (fun (n, _) => n != name)))
        | none => some fs  -- already gone
    | dir :: rest =>
      match fs with
      | .fsFile _ _ _ => none
      | .fsDir entries =>
        match entries.find? (fun (n, _) => n == dir) with
        | some (_, subfs) =>
          match remove subfs rest with
          | some subfs' =>
            let entries' := entries.filter (fun (n, _) => n != dir)
            some (.fsDir ((dir, subfs') :: entries'))
          | none => none
        | none => some fs  -- parent doesn't exist
  remove fs comps

/-! # Symbolic fd targets -/

abbrev FifoNum := Nat

inductive FdTarget where
  | fifo (n : FifoNum)
  | path (p : String)
  deriving Repr, BEq

abbrev Fds := List (Fd × FdTarget)

/-! # FIFO state -/

abbrev Fifo := String

/-! # Process model -/

inductive ProcStepped where
  | stepped (b : Bool)
  deriving Repr, BEq

def noSignals : List Signal := []

inductive ProcStatus where
  | procRunning | procStopped
  deriving Repr, BEq

inductive Proc where
  | shell (status : ProcStatus) (stmt : Stmt) (sh : ShellState) (fds : Fds) (stepped : ProcStepped) (pending : List Signal)
  | zombie (ec : Nat)

/-! # Symbolic state -/

structure Symbolic where
  passwd : List (String × String)
  shFds : Fds
  fsRoot : SymbolicFs
  fifos : List Fifo
  procs : List Proc
  umask : Perms
  curpid : Pid

/-! # Process helpers -/

def procExitStatus : Proc → Option Nat
  | .shell .. => none
  | .zombie ec => some ec

def procAlive (proc : Proc) : Bool :=
  (procExitStatus proc).isNone

def listGet? {α : Type} (l : List α) (n : Nat) : Option α :=
  if h : n < l.length then some (l.get ⟨n, h⟩) else none


/-! # Process management functions -/

def procSetEc (os : OsState Symbolic) (pid : Pid) (ec : Nat) : OsState Symbolic :=
  match adjustNth os.symbolic.procs pid (fun _ => (Proc.zombie ec, ())) with
  | none => os
  | some (procs', ()) =>
    { os with symbolic := { os.symbolic with procs := procs' } }

def procSaveState (os : OsState Symbolic) : OsState Symbolic :=
  let pid := os.symbolic.curpid
  match adjustNth os.symbolic.procs pid (fun proc =>
    match proc with
    | .shell status stmt _ fds stepped pending =>
      (.shell status stmt os.sh fds stepped pending, ())
    | p => (p, ())) with
  | none => os
  | some (procs', ()) =>
    { os with symbolic := { os.symbolic with procs := procs' } }


/-! # Process scheduling -/

inductive SelectedProc where
  | sProcNotFound
  | sProcStopped
  | sProcDone (ec : Nat)
  | sProcRunning (stmt : Stmt) (stepped : ProcStepped)

/-! # Symbolic FD operations -/

def symbolicResolveFd (sym : Symbolic) (fd : Fd) : Option FdTarget :=
  match sym.shFds.find? (fun (f, _) => f == fd) with
  | some (_, tgt) => some tgt
  | _ => none

def readAllFifo (sym : Symbolic) (fifoNum : FifoNum) : Option (Symbolic × String) :=
  match adjustNth sym.fifos fifoNum (fun fifoContents => ("", fifoContents)) with
  | none => none
  | some (newFifos, s) => some ({ sym with fifos := newFifos }, s)

def readCharFifo (sym : Symbolic) (fifoNum : FifoNum) : Option (Symbolic × Char) :=
  let getChar (fifoContents : String) : String × Option Char :=
    match fifoContents.toList with
    | [] => ("", none)
    | c :: cs => (String.ofList cs, some c)
  match adjustNth sym.fifos fifoNum getChar with
  | none => none
  | some (_, none) => none
  | some (newFifos, some c) => some ({ sym with fifos := newFifos }, c)

def symbolicFreshFd (shFds : Fds) : Fd :=
  let fdNums := shFds.map Prod.fst
  match fdNums with
  | [] => 0
  | _ => fdNums.foldl max 0 + 1

def symbolicFdsReadsFifo (fifoNum : FifoNum) (fds : Fds) : Bool :=
  fds.any (fun (_, tgt) =>
    match tgt with
    | .fifo n => n == fifoNum
    | _ => false)

def symbolicFdsWritesFifo (fifoNum : FifoNum) (fds : Fds) : Bool :=
  fds.any (fun (fd, tgt) =>
    match tgt with
    | .fifo n => fd != STDIN && n == fifoNum
    | _ => false)

def countOpenFifo (sym : Symbolic) (fifoNum : FifoNum) : Nat :=
  let shCount := sym.shFds.foldl (fun acc (_, tgt) =>
    match tgt with | .fifo n => if n == fifoNum then acc + 1 else acc | _ => acc) 0
  let procCount := sym.procs.foldl (fun acc proc =>
    match proc with
    | .shell _ _ _ fds _ _ =>
      acc + fds.foldl (fun acc2 (_, tgt) =>
        match tgt with | .fifo n => if n == fifoNum then acc2 + 1 else acc2 | _ => acc2) 0
    | _ => acc) 0
  shCount + procCount

def stepWorld (stepFun : StepFun Symbolic) (os : OsState Symbolic) : OsState Symbolic × Bool :=
  let rec loop (pid : Nat) (os : OsState Symbolic) (progress : Bool) : OsState Symbolic × Bool :=
    if pid >= os.symbolic.procs.length then (os, progress)
    else if pid == os.symbolic.curpid then
      -- Skip the current process (it's being stepped by the caller)
      loop (pid + 1) os progress
    else
      match listGet? os.symbolic.procs pid with
      | some (.shell .procRunning stmt sh fds stepped pending) =>
        let childOs : OsState Symbolic :=
             { os with sh := sh,
                       symbolic := { os.symbolic with shFds := fds, curpid := pid } }
        let (childOs', res) := stepFun childOs stmt
        match res with
        | .inl (step, stmt') =>
           let newProc := Proc.shell .procRunning stmt' childOs'.sh childOs'.symbolic.shFds (.stepped true) pending
           let procs' := match adjustNth os.symbolic.procs pid (fun _ => (newProc, ())) with | some (p, _) => p | none => os.symbolic.procs
           let sym' := { os.symbolic with
                         fifos := childOs'.symbolic.fifos,
                         fsRoot := childOs'.symbolic.fsRoot,
                         procs := procs' }
           let os' := { os with symbolic := sym' }
           (os', true)
        | .inr (some _ec) =>
           -- OCaml: symbolic_step_pid:490-505 — check EXIT trap before zombifying
           let (childOs2, trapOpt) := exitTrap childOs'
           match trapOpt with
           | some handler =>
             -- EXIT trap exists: keep process running with handler, then exit
             let sHandler := stringOfSymbolicString handler
             let handlerCmd := Stmt.evalLoop 1 (none, none) (.parseString .parseTrap sHandler) .noninteractive .subsidiary
             let exitStmt := Stmt.semi handlerCmd .exit_
             let newProc := Proc.shell .procRunning exitStmt childOs2.sh childOs2.symbolic.shFds (.stepped true) pending
             let procs' := match adjustNth os.symbolic.procs pid (fun _ => (newProc, ())) with | some (p, _) => p | none => os.symbolic.procs
             let sym' := { os.symbolic with fifos := childOs2.symbolic.fifos, fsRoot := childOs2.symbolic.fsRoot, procs := procs' }
             ({ os with symbolic := sym' }, true)
           | none =>
             -- No EXIT trap: zombie the process
             let newProc := Proc.zombie childOs2.sh.exitCode
             let procs' := match adjustNth os.symbolic.procs pid (fun _ => (newProc, ())) with | some (p, _) => p | none => os.symbolic.procs
             let sym' := { os.symbolic with fifos := childOs2.symbolic.fifos, fsRoot := childOs2.symbolic.fsRoot, procs := procs' }
             ({ os with symbolic := sym' }, true)
         | .inr none =>
           loop (pid + 1) os progress
      | _ => loop (pid + 1) os progress
  loop 0 os false

partial def blockingReadAllFd (stepFun : StepFun Symbolic) (os : OsState Symbolic) (fifoNum : FifoNum) (acc : String) : OsState Symbolic × Option String :=
  match readAllFifo os.symbolic fifoNum with
  | some (sym', data) =>
    let os' := { os with symbolic := sym' }
    let newAcc := acc ++ data
    if data != "" then
      blockingReadAllFd stepFun os' fifoNum newAcc
    else
      if countOpenFifo os'.symbolic fifoNum > 1 then
        let (os'', progress) := stepWorld stepFun os'
        if progress then blockingReadAllFd stepFun os'' fifoNum newAcc
        else (os'', some newAcc)
      else
        (os', some newAcc)
  | none => (os, some acc)

def symbolicWritesFifo (fifoNum : FifoNum) : Proc → Bool
  | .zombie _ => false
  | .shell _ _ _ fds _ _ => symbolicFdsWritesFifo fifoNum fds

/-- OCaml: symbolic_has_reader — check if any OTHER process (not curpid) reads this FIFO.
    STDOUT (fifo 1) and STDERR (fifo 2) always have readers. -/
def symbolicHasReader (os : OsState Symbolic) (fifoNum : FifoNum) : Bool :=
  fifoNum == 1 || fifoNum == 2 ||
  -- enumerate procs with their index (pid)
  let rec go (pid : Nat) (procs : List Proc) : Bool :=
    match procs with
    | [] => false
    | proc :: rest =>
      let isMatch := pid != os.symbolic.curpid &&
        match proc with
        | .shell _ _ _ fds _ _ => symbolicFdsReadsFifo fifoNum fds
        | .zombie _ => false
      if isMatch then true else go (pid + 1) rest
  go 0 os.symbolic.procs

/-- OCaml: symbolic_find_writer — find pids of processes (other than curpid) writing to FIFO -/
def symbolicFindWriter (os : OsState Symbolic) (fifoNum : FifoNum) : List Pid :=
  let rec go (pid : Nat) (procs : List Proc) (acc : List Pid) : List Pid :=
    match procs with
    | [] => acc.reverse
    | proc :: rest =>
      if pid != os.symbolic.curpid && symbolicWritesFifo fifoNum proc
      then go (pid + 1) rest (pid :: acc)
      else go (pid + 1) rest acc
  go 0 os.symbolic.procs []

/-- OCaml: string_read_line_cl — read characters until newline, handling escapes -/
def stringReadLineCl : List Char → EscapeMode → List Char → List Char × List Char × ReadEof
  -- EOF
  | [], _, line => (line, [], .hitEof)
  -- newline terminates
  | '\n' :: cs', _, line => (line, cs', .noEof)
  -- backslash escapes
  | ['\\'], .escapeOn, line => ('\\' :: line, [], .hitEof)
  | '\\' :: '\n' :: cs, .escapeOn, line => stringReadLineCl cs .escapeOn line
  | '\\' :: c :: cs, .escapeOn, line => stringReadLineCl cs .escapeOn (c :: line)
  -- ordinary char
  | c :: cs, esc, line => stringReadLineCl cs esc (c :: line)

/-- OCaml: string_read_line — read a line from string, returning (line, rest, eof) -/
def stringReadLine (s : String) (escapes : EscapeMode) : String × String × ReadEof :=
  let (lineCs, rest, eof) := stringReadLineCl s.toList escapes []
  (String.ofList lineCs.reverse, String.ofList rest, eof)

/-! # Symbolic write/read -/

/-- OCaml: symbolic_write_fd — write to FD, send SIGPIPE if no readers -/
def symbolicWriteFd (os : OsState Symbolic) (fd : Fd) (s : String) : Option (OsState Symbolic) :=
  match symbolicResolveFd os.symbolic fd with
  | none => none
  | some (.fifo fifoNum) =>
    match adjustNth os.symbolic.fifos fifoNum (fun contents => (contents ++ s, ())) with
    | none => none
    | some (newFifos, ()) =>
      let os' := { os with symbolic := { os.symbolic with fifos := newFifos } }
      -- OCaml: check if there are still readers for this FIFO
      if symbolicHasReader os' fifoNum
      then some os'
      else
        -- No readers: send SIGPIPE to current process
        -- OCaml: symbolic_signal_pid os SIGPIPE os.symbolic.curpid SignalProcess
        -- Simplified: just append SIGPIPE to current process pending signals
        let pid := os'.symbolic.curpid
        match listGet? os'.symbolic.procs pid with
        | some (.shell status stmt sh fds stepped pending) =>
          let newProc := Proc.shell status stmt sh fds stepped (pending ++ [.SIGPIPE])
          let procs' := os'.symbolic.procs.set pid newProc
          some { os' with symbolic := { os'.symbolic with procs := procs' } }
        | _ => some os'  -- zombie or not found, just succeed
  | some (.path p) =>
    match symbolicFsWrite os.symbolic.fsRoot p s true with
    | none => none
    | some newFs =>
      some { os with symbolic := { os.symbolic with fsRoot := newFs } }

def symbolicWriteStderr (s : String) (os : OsState Symbolic) : OsState Symbolic :=
  match symbolicWriteFd os STDERR s with
  | none => os
  | some os' => os'

/-! # Symbolic OS instance -/

-- Helper: default symbolic state
def defaultSymbolic : Symbolic :=
  { passwd := [],
    shFds := [(0, .fifo 0), (1, .fifo 1), (2, .fifo 2)],
    fsRoot := .fsDir [],
    fifos := ["", "", ""],  -- stdin, stdout, stderr
    -- OCaml: procs starts with [Shell(Proc_Running, Done, default_shell_state, fds_default, ...)]
    procs := [Proc.shell .procRunning .done defaultShellState [(0, .fifo 0), (1, .fifo 1), (2, .fifo 2)] (.stepped false) []],
    umask := defaultUmask,
    curpid := 0 }

instance : OS Symbolic where
  osInit _mode _level :=
    { sh := defaultShellState,
      symbolic := defaultSymbolic,
      fuel := none,
      log := [] }

  osTick os :=
    -- OCaml: symbolic_clear_stepped — reset stepped flag on all processes
    -- Optimization: skip if only parent process (no children to clear)
    if os.symbolic.procs.length ≤ 1 then os
    else
    { os with symbolic :=
      { os.symbolic with procs := os.symbolic.procs.map (fun proc =>
          match proc with
          | .zombie _ => proc
          | .shell status stmt sh fds _stepped pending =>
            .shell status stmt sh fds (.stepped false) pending) } }
  osSetPs1 os _v := os
  osSetPs2 os _v := os
  osExecve os _cmd := os
  osForkAndSubshell os stmt _bg _pgid _last :=
    let newPid := os.symbolic.procs.length
    -- OCaml: prepare_subshell clears traps, resets loop_nest/jobs/outermost
    let subOs := prepareSubshell os
    let newProc := Proc.shell .procRunning stmt subOs.sh os.symbolic.shFds (.stepped false) []
    let os' := { os with symbolic :=
      { os.symbolic with
        procs := os.symbolic.procs ++ [newProc] } }
    (os', newPid)

  osExit os := procSetEc os os.symbolic.curpid os.sh.exitCode

  osGetpwnam os user :=
    match os.symbolic.passwd.find? (fun (u, _) => u == user) with
    | some (_, dir) => some dir
    | none => none

  osWaitpid stepFun os pid :=
    -- OCaml: symbolic_step_pid uses proc_select directly (no job table check)
    -- The job table check is done by waitpid_or_lookup/wait_for_pid in Os.lean
      -- OCaml: proc_select saves current state, then swaps to target pid
      let os1 := procSaveState os
      match listGet? os1.symbolic.procs pid with
      | some (Proc.zombie ec) => (os1, some (.inr ec))
      | some (.shell .procStopped _ _ _ _ _) => (os1, none)
      | some (.shell .procRunning stmt _sh _fds (.stepped true) _pending) =>
        -- Already stepped this tick, return step info
        (os1, some (.inl (.xsNested (.xsSimple "already stepped") (.xsProc pid stmt))))
      | some (.shell .procRunning stmt sh fds (.stepped false) pending) =>
        -- Switch to child context: swap sh + shFds + curpid
        -- This is the OCaml proc_select pattern: shared FIFOs!
        let os2 := procSaveState os1  -- save parent state into proc table
        let childOs : OsState Symbolic :=
          { os2 with sh := sh,
                     symbolic := { os2.symbolic with shFds := fds, curpid := pid } }

        -- Step the child (using shared FIFO state)
        let (childOs', res) := stepFun childOs stmt

        match res with
        | .inl (step, stmt') =>
          -- Child took a step, still running
          -- Save child state back into proc table
          let os3 : OsState Symbolic :=
            match adjustNth childOs'.symbolic.procs pid (fun _ =>
              (Proc.shell .procRunning stmt' childOs'.sh childOs'.symbolic.shFds (.stepped true) pending, ())) with
            | some (procs', ()) => { childOs' with symbolic := { childOs'.symbolic with procs := procs' } }
            | none => childOs'
          -- Restore parent context
          match listGet? os3.symbolic.procs os.symbolic.curpid with
          | some (.shell _ _ parentSh parentFds _ _) =>
            let sym' := { os3.symbolic with shFds := parentFds, curpid := os.symbolic.curpid }
            ({ os3 with sh := parentSh, symbolic := sym' }, some (.inl (.xsNested step (.xsProc pid stmt'))))
          | _ =>
            let sym' := { os3.symbolic with shFds := os.symbolic.shFds, curpid := os.symbolic.curpid }
            ({ os3 with sh := os.sh, symbolic := sym' }, some (.inl (.xsNested step (.xsProc pid stmt'))))
        | .inr (some ec) =>
          -- Child exited: check for EXIT trap before zombifying (OCaml: symbolic_step_pid)
          let (childOs2, trapOpt) := exitTrap childOs'
          match trapOpt with
          | some handler =>
            -- EXIT trap exists: keep process running with handler, then exit
            let sHandler := stringOfSymbolicString handler
            let handlerCmd := Stmt.evalLoop 1 (none, none) (.parseString .parseTrap sHandler) .noninteractive .subsidiary
            let exitStmt := Stmt.semi handlerCmd .exit_
            -- Save child state back into proc table with handler as new statement
            let os3 : OsState Symbolic :=
              match adjustNth childOs2.symbolic.procs pid (fun _ =>
                (Proc.shell .procRunning exitStmt childOs2.sh childOs2.symbolic.shFds (.stepped true) pending, ())) with
              | some (procs', ()) => { childOs2 with symbolic := { childOs2.symbolic with procs := procs' } }
              | none => childOs2
            -- Restore parent context
            match listGet? os3.symbolic.procs os.symbolic.curpid with
            | some (.shell _ _ parentSh parentFds _ _) =>
              let sym' := { os3.symbolic with shFds := parentFds, curpid := os.symbolic.curpid }
              ({ os3 with sh := parentSh, symbolic := sym' },
                some (.inl (.xsNested (.xsSimple "trapped on EXIT") (.xsProc pid exitStmt))))
            | _ =>
              let sym' := { os3.symbolic with shFds := os.symbolic.shFds, curpid := os.symbolic.curpid }
              ({ os3 with sh := os.sh, symbolic := sym' },
                some (.inl (.xsNested (.xsSimple "trapped on EXIT") (.xsProc pid exitStmt))))
          | none =>
            -- No EXIT trap: zombie the process
            let os3 := procSetEc childOs' pid ec
            -- Restore parent context
            match listGet? os3.symbolic.procs os.symbolic.curpid with
            | some (.shell _ _ parentSh parentFds _ _) =>
              let sym' := { os3.symbolic with shFds := parentFds, curpid := os.symbolic.curpid }
              ({ os3 with sh := parentSh, symbolic := sym' }, some (.inr ec))
            | _ =>
              let sym' := { os3.symbolic with shFds := os.symbolic.shFds, curpid := os.symbolic.curpid }
              ({ os3 with sh := os.sh, symbolic := sym' }, some (.inr ec))
        | .inr none =>
          -- Child is stuck
          (os1, some (.inl (.xsSimple "stuck")))
      | _ => (os1, none)

  osWaitchild os := (os, none)

  osHandleSignal os _sig _handler := os
  osSignalPid os sig pid _asPg :=
    -- OCaml: proc_receive_signal (os_symbolic.lem:430-464)
    -- Save state first, then check trap/default behavior
    let os1 := procSaveState os
    match listGet? os1.symbolic.procs pid with
    | some (.shell status stmt procSh fds stepped pending) =>
      -- Check if process has a trap handler for this signal
      let (os2, proc') :=
        match procSh.traps.find? (fun (s, _) => s == sig) with
        | some _ =>
          -- Trap exists: add signal to pending for check_traps to handle
          (os1, Proc.shell status stmt procSh fds stepped (pending ++ [sig]))
        | none =>
          -- No trap: apply default signal behavior
          match sig.defaultBehavior with
          | .terminate _actions =>
            let ec := 128 + sig.platformInt
            (os1, Proc.zombie ec)
          | .ignore =>
            (os1, Proc.shell status stmt procSh fds stepped pending)
          | .stop =>
            (os1, Proc.shell .procStopped stmt procSh fds stepped pending)
          | .continue_ =>
            (os1, Proc.shell .procRunning stmt procSh fds stepped pending)
      let procs' := os2.symbolic.procs.set pid proc'
      ({ os2 with symbolic := { os2.symbolic with procs := procs' } }, true)
    | some (.zombie _) => (os1, false)
    | _ => (os1, false)

  osPendingSignal os :=
    -- OCaml: check current process pending list, pop head
    let pid := os.symbolic.curpid
    match listGet? os.symbolic.procs pid with
    | some (.shell status stmt sh fds stepped (sig :: rest)) =>
      let newProc := Proc.shell status stmt sh fds stepped rest
      let procs' := os.symbolic.procs.set pid newProc
      ({ os with symbolic := { os.symbolic with procs := procs' } }, some sig)
    | _ => (os, none)

  osTcSetfg os _pid := (os, false)
  osSetJobControl os _on := os

  osTimes _os := ("0", "0", "0", "0")

  osGetUmask os := os.symbolic.umask
  osSetUmask os perms := { os with symbolic := { os.symbolic with umask := perms } }

  osPhysicalCwd os := os.sh.cwd

  osChdir os path :=
    -- Resolve path: ensure it's normalized
    let resolvedPath := if path == "/" then "/" else
      -- Strip trailing slash
      let p := if path.endsWith "/" && path.length > 1
        then path.dropRight 1 else path
      p
    -- Check if directory exists in symbolic FS (lenient in symbolic mode — always succeed)
    ({ os with sh := { os.sh with cwd := resolvedPath } }, none)

  osReaddir os path :=
    match symbolicFsResolveNode os.symbolic.fsRoot path with
    | some (.fsDir entries) => entries.map (fun (name, node) =>
        match node with
        | .fsFile _ _ _ => (name, .file)
        | .fsDir _ => (name, .dir name))
    | _ => []
  osFileExists os path :=
    match symbolicFsResolvePath os.symbolic.fsRoot path with
    | some _ => true
    | none => false

  osFileType os path :=
    match symbolicFsResolvePath os.symbolic.fsRoot path with
    | some .file => some .fileRegular
    | some (.dir _) => some .fileDirectory
    | none => none
  osFileTypeFollow os path := -- Missing method implementation
    match symbolicFsResolvePath os.symbolic.fsRoot path with
    | some .file => some .fileRegular
    | some (.dir _) => some .fileDirectory
    | none => none
  osFileSize os path :=
    match symbolicFsResolveNode os.symbolic.fsRoot path with
    | some (.fsFile content _ _) => some content.length
    | _ => none
  osFilePerms os path :=
    match symbolicFsResolveNode os.symbolic.fsRoot path with
    | some (.fsFile _ mode _) => some (permsOfNat (UInt32.toNat mode))
    | some (.fsDir _) => some (permsOfNat 0o755)
    | none => none
  osFileMtime os path :=
    match symbolicFsResolveNode os.symbolic.fsRoot path with
    | some (.fsFile _ _ mtime) => some (Float.ofNat mtime)
    | some (.fsDir _) => some 0.0
    | none => none
  osFileNumber os path := none
  osIsTty os fd :=
    match symbolicResolveFd os.symbolic fd with
    | some (.fifo fifoNum) =>
      (fifoNum == STDIN || fifoNum == STDOUT || fifoNum == STDERR) && isInteractive os
    | _ => false
  osIsReadable os path :=
    match symbolicFsResolvePath os.symbolic.fsRoot path with
    | some _ => true
    | none => false
  osIsWriteable os path :=
    match symbolicFsResolvePath os.symbolic.fsRoot path with
    | some _ => true
    | none => false
  osIsExecutable os path :=
    match symbolicFsResolvePath os.symbolic.fsRoot path with
    | some _ => true
    | none => false

  osReadFile os path :=
    match symbolicFsResolveNode os.symbolic.fsRoot path with
    | some (.fsFile content _ _) => some content
    | _ => none

  osMkdir os path mkdirP :=
    match symbolicFsMkdir os.symbolic.fsRoot path mkdirP with
    | some newFs => ({ os with symbolic := { os.symbolic with fsRoot := newFs } }, true)
    | none => (os, false)

  osRmFile os path recursive :=
    match symbolicFsRemove os.symbolic.fsRoot path recursive with
    | some newFs => ({ os with symbolic := { os.symbolic with fsRoot := newFs } }, true)
    | none => (os, false)

  osWriteFd os fd s := symbolicWriteFd os fd s

  osReadAllFd stepFun os fd :=
    match symbolicResolveFd os.symbolic fd with
    | none => (os, .inr none)
    | some (.fifo fifoNum) =>
      let (os', res) := blockingReadAllFd stepFun os fifoNum ""
      (os', .inr res)
    | some (.path _) => (os, .inr none)


  osReadLineFd os fd escMode :=
    match symbolicResolveFd os.symbolic fd with
    | some (.fifo fifoNum) =>
      match listGet? os.symbolic.fifos fifoNum with
      | none => (os, ("", "", .hitEof))  -- broken pipe
      | some cts =>
        let (line, cts', eofFlag) := stringReadLine cts escMode
        let commitRead :=
          let newFifos := os.symbolic.fifos.set fifoNum cts'
          ({ os with symbolic := { os.symbolic with fifos := newFifos } },
           (line, "", eofFlag))
        if eofFlag == .noEof then
          commitRead
        else
          -- EOF: check if someone is still writing to this FIFO
          match symbolicFindWriter os fifoNum with
          | [] => commitRead  -- no writer, return EOF
          | _ => (os, ("", "", .hitEof))  -- writer exists, block (simplified: return EOF)
    | some (.path _) => (os, ("", "", .hitEof))
    | none => (os, ("", "", .hitEof))

  osCloseFd os fd :=
    { os with symbolic :=
      { os.symbolic with shFds := os.symbolic.shFds.filter (fun (f, _) => f != fd) } }

  osPipe os :=
    -- OCaml: mkfifo, then allocate read FD, then allocate write FD from updated map
    let newFifo := ""
    let fifoIdx := os.symbolic.fifos.length
    let sym1 := { os.symbolic with fifos := os.symbolic.fifos ++ [newFifo] }
    -- Allocate read FD
    let fdRead := symbolicFreshFd sym1.shFds
    let fds1 := sym1.shFds ++ [(fdRead, .fifo fifoIdx)]
    -- Allocate write FD from updated map
    let fdWrite := symbolicFreshFd fds1
    let fds2 := fds1 ++ [(fdWrite, .fifo fifoIdx)]
    let sym2 := { sym1 with shFds := fds2 }
    .inr ({ os with symbolic := sym2 }, fdRead, fdWrite)

  osOpenFileForRedir os ty ss :=
    let (_, _, sfile) := concretize os ss
    -- For From redirects, check if file exists in the symbolic filesystem.
    -- Real shells fail when trying to redirect input from a nonexistent file.
    -- Special device files (/dev/null, /dev/stdin, etc.) are always considered to exist.
    let isDeviceFile := sfile.startsWith "/dev/"
    match ty with
    | .from_ =>
      if isDeviceFile then
        -- /dev/null, /dev/stdin etc. — always succeed
        let fd := symbolicFreshFd os.symbolic.shFds
        let sym' := { os.symbolic with
          shFds := os.symbolic.shFds ++ [(fd, .path sfile)] }
        ( { os with symbolic := sym' }, .inr fd )
      else
        match symbolicFsResolveNode os.symbolic.fsRoot sfile with
        | some (.fsFile content _ _) =>
          -- Create a FIFO with the file content so osReadLineFd/osReadAllFd can read from it
          let fifoIdx := os.symbolic.fifos.length
          let fd := symbolicFreshFd os.symbolic.shFds
          let sym' := { os.symbolic with
            shFds := os.symbolic.shFds ++ [(fd, .fifo fifoIdx)],
            fifos := os.symbolic.fifos ++ [content] }
          ( { os with symbolic := sym' }, .inr fd )
        | some (.fsDir _) =>
          ( os, .inl (sfile ++ ": Is a directory") )
        | none =>
          ( os, .inl (sfile ++ ": No such file or directory") )
    | .to =>
      -- Check noclobber: if set, refuse to overwrite existing regular files
      let noclobber := os.sh.opts.contains .noclobber
      if noclobber && !isDeviceFile then
        match symbolicFsResolveNode os.symbolic.fsRoot sfile with
        | some (.fsFile _ _ _) =>
          -- File exists and is regular: noclobber prevents overwriting
          ( os, .inl (sfile ++ ": cannot overwrite existing file") )
        | _ =>
          -- File doesn't exist or is not regular: create empty file, proceed normally
          let fd := symbolicFreshFd os.symbolic.shFds
          let newFs := match symbolicFsWrite os.symbolic.fsRoot sfile "" false with
            | some fs => fs | none => os.symbolic.fsRoot
          let sym' := { os.symbolic with
            shFds := os.symbolic.shFds ++ [(fd, .path sfile)],
            fsRoot := newFs }
          ( { os with symbolic := sym' }, .inr fd )
      else
        -- Truncate/create file (> without noclobber)
        let fd := symbolicFreshFd os.symbolic.shFds
        let newFs := match symbolicFsWrite os.symbolic.fsRoot sfile "" false with
          | some fs => fs | none => os.symbolic.fsRoot
        let sym' := { os.symbolic with
          shFds := os.symbolic.shFds ++ [(fd, .path sfile)],
          fsRoot := newFs }
        ( { os with symbolic := sym' }, .inr fd )
    | .append =>
      -- For append: create file if not exists, but don't truncate existing
      let fd := symbolicFreshFd os.symbolic.shFds
      let newFs := match symbolicFsResolveNode os.symbolic.fsRoot sfile with
        | some _ => os.symbolic.fsRoot  -- File exists, don't touch it
        | none => match symbolicFsWrite os.symbolic.fsRoot sfile "" false with
          | some fs => fs | none => os.symbolic.fsRoot
      let sym' := { os.symbolic with
        shFds := os.symbolic.shFds ++ [(fd, .path sfile)],
        fsRoot := newFs }
      ( { os with symbolic := sym' }, .inr fd )
    | _ =>
      -- Other output redirect types (.clobber, .fromto): truncate/create
      let fd := symbolicFreshFd os.symbolic.shFds
      let newFs := match symbolicFsWrite os.symbolic.fsRoot sfile "" false with
        | some fs => fs | none => os.symbolic.fsRoot
      let sym' := { os.symbolic with
        shFds := os.symbolic.shFds ++ [(fd, .path sfile)],
        fsRoot := newFs }
      ( { os with symbolic := sym' }, .inr fd )
  osOpenHeredoc os s :=
    let fifoIdx := os.symbolic.fifos.length
    let fd := symbolicFreshFd os.symbolic.shFds
    let sym' := { os.symbolic with
      shFds := os.symbolic.shFds ++ [(fd, .fifo fifoIdx)],
      fifos := os.symbolic.fifos ++ [s] }
    .inr ({ os with symbolic := sym' }, fd)

  osCloseAndSaveFd os fd :=
    -- OCaml: close the fd and save its FIFO target for later restoration
    let sym := os.symbolic
    match sym.shFds.find? (fun (f, _) => f == fd) with
    | none =>
      -- Already closed: save a close marker so restore will close it if reopened
      -- OCaml returns Right [(fd, Saved_close)] to ensure fd is closed on restore
      let os' := { os with symbolic := { sym with shFds := sym.shFds.filter (fun (f, _) => f != fd) } }
      (os', .inr [(fd, .inr ())])
    | some (_, .fifo fifoNum) =>
      -- Save the FIFO number (OCaml: Saved fifo_num)
      let os' := { os with symbolic := { sym with shFds := sym.shFds.filter (fun (f, _) => f != fd) } }
      (os', .inr [(fd, .inl fifoNum)])
    | some (_, .path _) =>
      -- OCaml: Left "TODO 2018-08-24 symbolic path FDs unimplemented"
      let os' := { os with symbolic := { sym with shFds := sym.shFds.filter (fun (f, _) => f != fd) } }
      (os', .inl "TODO symbolic path FDs unimplemented")

  osRenumberFd os action origFd wantedFd :=
    -- OCaml: if origFd == wantedFd, just return close info if needed
    if origFd == wantedFd then
      let savedInfo : SavedFds := if action.shouldClose then [(wantedFd, .inr ())] else []
      (os, .inr savedInfo)
    else
      match os.symbolic.shFds.find? (fun (f, _) => f == origFd) with
      | none => (os, .inl "broken pipe (tried to renumber closed fd)")
      | some (_, newTgt) =>
        -- Save existing wanted_fd target if present
        let saved : SavedFds := match os.symbolic.shFds.find? (fun (f, _) => f == wantedFd) with
          | none => []  -- wanted_fd is free
          | some (_, .fifo fifoNum) => [(wantedFd, .inl fifoNum)]
          | some (_, .path _) => []  -- TODO: path FDs
        -- Install the new FD and optionally close the original
        let fds0 := (wantedFd, newTgt) :: os.symbolic.shFds.filter (fun (f, _) => f != wantedFd)
        let fds1 := if action.shouldClose then fds0.filter (fun (f, _) => f != origFd) else fds0
        let os' := { os with symbolic := { os.symbolic with shFds := fds1 } }
        (os', .inr saved)

  osRestoreFd os fd info :=
    match info with
    | .inl fifoNum =>
      -- Restore: create a fresh FD entry pointing to the saved FIFO
      let fds' := (fd, .fifo fifoNum) :: os.symbolic.shFds.filter (fun (f, _) => f != fd)
      { os with symbolic := { os.symbolic with shFds := fds' } }
    | .inr () =>
      -- Close: remove the fd
      { os with symbolic := { os.symbolic with shFds := os.symbolic.shFds.filter (fun (f, _) => f != fd) } }
