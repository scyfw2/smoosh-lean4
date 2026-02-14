/-
  Smoosh.OsSymbolic — Symbolic filesystem, processes, and OS instance
  Translated from os_symbolic.lem (866 lines)
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

def symbolicFsResolvePath (fs : SymbolicFs) (path : String) : Option (FileUnit) :=
  let comps := splitStringOn false '/' path
  symbolicFsResolveComps fs comps

def symbolicFsResolveNode (fs : SymbolicFs) (path : String) : Option SymbolicFs :=
  let comps := splitStringOn false '/' path
  let rec traverse (fs : SymbolicFs) (comps : List String) : Option SymbolicFs :=
    match comps with
    | [] => some fs
    | dir :: rest =>
      match symbolicFsSubdir fs dir with
      | some subfs => traverse subfs rest
      | none => none
  traverse fs comps

def symbolicFsWrite (fs : SymbolicFs) (path : String) (content : String) (append : Bool) : Option SymbolicFs :=
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
  fds.any (fun (_, tgt) =>
    match tgt with
    | .fifo n => n == fifoNum
    | _ => false)

def symbolicWritesFifo (fifoNum : FifoNum) : Proc → Bool
  | .zombie _ => false
  | .shell _ _ _ fds _ _ => symbolicFdsWritesFifo fifoNum fds

/-! # Symbolic write/read -/

def symbolicWriteFd (os : OsState Symbolic) (fd : Fd) (s : String) : Option (OsState Symbolic) :=
  match symbolicResolveFd os.symbolic fd with
  | none => none
  | some (.fifo fifoNum) =>
    match adjustNth os.symbolic.fifos fifoNum (fun contents => (contents ++ s, ())) with
    | none => none
    | some (newFifos, ()) =>
      some { os with symbolic := { os.symbolic with fifos := newFifos } }
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
    procs := [],
    umask := defaultUmask,
    curpid := 0 }

instance : OS Symbolic where
  osInit _mode _level :=
    { sh := defaultShellState,
      symbolic := defaultSymbolic,
      fuel := none,
      log := [] }

  osTick os := os
  osSetPs1 os _v := os
  osSetPs2 os _v := os
  osExecve os _cmd := os
  osForkAndSubshell os stmt _bg _pgid _last :=
    let newPid := os.symbolic.procs.length
    let newProc := Proc.shell .procRunning stmt os.sh os.symbolic.shFds (.stepped false) []
    let os' := { os with symbolic :=
      { os.symbolic with
        procs := os.symbolic.procs ++ [newProc],
        curpid := newPid } }
    (os', newPid)

  osExit os := os

  osGetpwnam os user :=
    match os.symbolic.passwd.find? (fun (u, _) => u == user) with
    | some (_, dir) => some dir
    | none => none

  osWaitpid stepFun os pid :=
    match findJobWithPid os pid with
    | some job =>
      -- If job is already done, return exit code
      match ecOfJobStatus job.status with
      | some ec => (deleteJob os job.id, some (.inr ec))
      | none => (os, none)
    | none =>
      match listGet? os.symbolic.procs pid with
      | some (Proc.zombie ec) => (os, some (.inr ec))
      | some (.shell status stmt sh fds stepped pending) =>
        -- construct child OS
        let childOs : OsState Symbolic :=
          { sh := sh, symbolic := { os.symbolic with shFds := fds }, fuel := os.fuel, log := os.log }

        -- step child
        let (childOs', res) := stepFun childOs stmt

        -- recover updated state
        let (newStmt, newStatus, newEc, res') : Stmt × ProcStatus × Option Nat × Option (Sum EvaluationStep Nat) :=
          match res with
          | .inl (step, nextStmt) => (nextStmt, status, none, some (.inl step))
          | .inr (some ec) => (stmt, ProcStatus.procStopped, some ec, some (.inr ec))
          | .inr none => (stmt, status, none, some (.inl (EvaluationStep.xsSimple "stuck")))

        -- If exited, update to zombie
        match newEc with
        | some ec =>
          let procs' := os.symbolic.procs.set pid (Proc.zombie ec)
          ({ os with symbolic := { os.symbolic with procs := procs' } }, res')
        | none =>
          let newProc := Proc.shell newStatus newStmt childOs'.sh childOs'.symbolic.shFds stepped pending
          let procs' := os.symbolic.procs.set pid newProc
          let logDiff := childOs'.log.take (childOs'.log.length - os.log.length)
          let os' := { os with log := logDiff ++ os.log, symbolic := { os.symbolic with procs := procs' } }
          (os', res')
      | _ => (os, none)

  osWaitchild os := (os, none)

  osHandleSignal os _sig _handler := os
  osSignalPid os _sig _pid _asPg := (os, false)
  osPendingSignal os := (os, none)

  osTcSetfg os _pid := (os, false)
  osSetJobControl os _on := os

  osTimes _os := ("0", "0", "0", "0")

  osGetUmask os := os.symbolic.umask
  osSetUmask os perms := { os with symbolic := { os.symbolic with umask := perms } }

  osPhysicalCwd os := os.sh.cwd

  osChdir os path :=
    ({ os with sh := { os.sh with cwd := path } }, none)

  osReaddir _os _path := []
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
  osIsTty _os _fd := false
  osIsReadable _os _path := false
  osIsWriteable _os _path := false
  osIsExecutable _os _path := false

  osWriteFd os fd s := symbolicWriteFd os fd s

  osReadAllFd _stepFun os fd :=
    match symbolicResolveFd os.symbolic fd with
    | none => (os, .inr none)
    | some (.fifo fifoNum) =>
      match readAllFifo os.symbolic fifoNum with
      | none => (os, .inr none)
      | some (sym', s) => ({ os with symbolic := sym' }, .inr (some s))
    | some (.path _) => (os, .inr none)


  osReadLineFd os _fd _escMode := (os, ("", "", .hitEof))

  osCloseFd os fd :=
    { os with symbolic :=
      { os.symbolic with shFds := os.symbolic.shFds.filter (fun (f, _) => f != fd) } }

  osPipe os :=
    let r := symbolicFreshFd os.symbolic.shFds
    let w := r + 1
    let newFifo := ""
    let fifoIdx := os.symbolic.fifos.length
    let sym' := { os.symbolic with
      shFds := os.symbolic.shFds ++ [(r, .fifo fifoIdx), (w, .fifo fifoIdx)],
      fifos := os.symbolic.fifos ++ [newFifo] }
    .inr ({ os with symbolic := sym' }, r, w)

  osOpenFileForRedir os _ty ss :=
    match tryConcrete ss with
    | none => (os, .inl "symbolic: open_file_for_redir: non-concrete path")
    | some path =>
      -- If writing, create empty file or truncate
      let fs' := match symbolicFsWrite os.symbolic.fsRoot path "" false with
        | some fs => fs
        | none => os.symbolic.fsRoot -- Ignore failure? or fail?
      -- For now, just proceed with updated FS (or same if failed)
      -- Allocate FD
      let fd := symbolicFreshFd os.symbolic.shFds
      let sym' := { os.symbolic with
        fsRoot := fs',
        shFds := os.symbolic.shFds ++ [(fd, .path path)] }
      ( { os with symbolic := sym' }, .inr fd )
  osOpenHeredoc os s :=
    let fifoIdx := os.symbolic.fifos.length
    let fd := symbolicFreshFd os.symbolic.shFds
    let sym' := { os.symbolic with
      shFds := os.symbolic.shFds ++ [(fd, .fifo fifoIdx)],
      fifos := os.symbolic.fifos ++ [s] }
    .inr ({ os with symbolic := sym' }, fd)

  osCloseAndSaveFd os fd :=
    match os.symbolic.shFds.find? (fun (f, _) => f == fd) with
    | none => (os, .inl s!"bad fd {fd}")
    | some (_, _tgt) =>
      let os' := { os with symbolic :=
        { os.symbolic with shFds := os.symbolic.shFds.filter (fun (f, _) => f != fd) } }
      (os', .inr [(fd, .inl fd)])

  osRenumberFd os action origFd wantedFd :=
    let saved := os.symbolic.shFds.find? (fun (f, _) => f == wantedFd)
    let savedInfo : SavedFds := match saved with
      | none => [(wantedFd, .inr ())]
      | some (_, _) => [(wantedFd, .inl wantedFd)]
    let origTgt := os.symbolic.shFds.find? (fun (f, _) => f == origFd)
    match origTgt with
    | none => (os, .inl s!"bad fd {origFd}")
    | some (_, tgt) =>
      let fds' := os.symbolic.shFds.filter (fun (f, _) => f != wantedFd)
      let fds'' := if action.shouldClose then fds'.filter (fun (f, _) => f != origFd) else fds'
      let fds''' := (wantedFd, tgt) :: fds''
      let os' := { os with symbolic := { os.symbolic with shFds := fds''' } }
      (os', .inr savedInfo)

  osRestoreFd os fd info :=
    match info with
    | .inl savedFd =>
      -- restore the saved fd
      let origTgt := os.symbolic.shFds.find? (fun (f, _) => f == savedFd)
      match origTgt with
      | none => os
      | some (_, tgt) =>
        let fds' := os.symbolic.shFds.filter (fun (f, _) => f != fd)
        { os with symbolic := { os.symbolic with shFds := (fd, tgt) :: fds' } }
    | .inr () =>
      -- close the fd
      { os with symbolic := { os.symbolic with shFds := os.symbolic.shFds.filter (fun (f, _) => f != fd) } }
