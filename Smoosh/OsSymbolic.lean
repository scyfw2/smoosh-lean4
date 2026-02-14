/-
  Smoosh.OsSymbolic — Symbolic filesystem, processes, and OS instance
  Translated from os_symbolic.lem (866 lines)
-/
import Smoosh.Os

/-! # Symbolic filesystem -/

inductive SymbolicFs where
  | fsFile (contents : String)
  | fsDir (entries : List (String × SymbolicFs))
  deriving Repr

def symbolicFsSubdir (fs : SymbolicFs) (name : String) : Option SymbolicFs :=
  match fs with
  | .fsFile _ => none
  | .fsDir entries =>
    match entries.find? (fun (n, _) => n == name) with
    | some (_, subfs) => some subfs
    | none => none

def symbolicFsResolveComps (fs : SymbolicFs) : List String → Option (FileUnit)
  | [] => match fs with
    | .fsFile _ => some .file
    | .fsDir _ => some (.dir "")
  | dir :: comps' =>
    match symbolicFsSubdir fs dir with
    | some fs' => symbolicFsResolveComps fs' comps'
    | none => none

def symbolicFsResolvePath (fs : SymbolicFs) (path : String) : Option (FileUnit) :=
  let comps := splitStringOn false '/' path
  symbolicFsResolveComps fs comps

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

/-! # Process management functions -/

def procSetEc (os : OsState Symbolic) (pid : Pid) (ec : Nat) : OsState Symbolic :=
  match adjustNth os.symbolic.procs pid (fun _ => (.zombie ec, ())) with
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

def symbolicResolveFd (sym : Symbolic) (fd : Fd) : Option FifoNum :=
  match sym.shFds.find? (fun (f, _) => f == fd) with
  | some (_, .fifo n) => some n
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
  | some fifoNum =>
    match adjustNth os.symbolic.fifos fifoNum (fun contents => (contents ++ s, ())) with
    | none => none
    | some (newFifos, ()) =>
      some { os with symbolic := { os.symbolic with fifos := newFifos } }

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
    let newPid := os.symbolic.curpid + 1
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

  osWaitpid _stepFun os _pid := (os, none)
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

  osFileTypeFollow os path :=
    match symbolicFsResolvePath os.symbolic.fsRoot path with
    | some .file => some .fileRegular
    | some (.dir _) => some .fileDirectory
    | none => none
  osFileSize _os _path := none
  osFilePerms _os _path := none
  osFileMtime _os _path := none
  osFileNumber _os _path := none
  osIsTty _os _fd := false
  osIsReadable _os _path := false
  osIsWriteable _os _path := false
  osIsExecutable _os _path := false

  osWriteFd os fd s := symbolicWriteFd os fd s

  osReadAllFd _stepFun os fd :=
    match symbolicResolveFd os.symbolic fd with
    | none => (os, .inr none)
    | some fifoNum =>
      match readAllFifo os.symbolic fifoNum with
      | none => (os, .inr none)
      | some (sym', s) => ({ os with symbolic := sym' }, .inr (some s))

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

  osOpenFileForRedir os _ty _ss := (os, .inl "symbolic: open_file_for_redir unimplemented")
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
