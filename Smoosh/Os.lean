/-
  Smoosh.Os — OS state, OS typeclass, parameters, logging, jobs, redirects
  Translated from `os.lem` (1476 lines).

  Defines the `OS` typeclass (the interface for filesystem and process operations),
  `OsState` (the concrete state threaded through evaluation), and operations for:
  - Parameter lookup/set, variable/function management
  - Job control, pipes, and process management
  - Redirections and FD management
  - Traps and signal handling
  - Logging and tracing
-/
import Smoosh.Prelude

/-! # File types -/

inductive FileType where
  | fileRegular | fileDirectory | fileSymlink | filePipe | fileSocket
  | fileBlock | fileChar | fileUnknown
  deriving Repr, BEq

/-! # File type for directories -/

inductive FileUnit where
  | file
  | dir (path : Path)
  deriving Repr, BEq

/-! # Escape mode for read -/

inductive EscapeMode where
  | escapeOn | escapeOff
  deriving Repr, BEq

/-! # Read results -/

inductive ReadEof where | hitEof | noEof
  deriving Repr, BEq

def ReadResult (α : Type) := α × α × ReadEof

/-! # Signal behavior state -/

inductive SigBeh where
  | sigBehDefault
  | sigBehIgnore
  | sigBehTerminate
  | sigBehStop
  | sigBehContinue
  deriving Repr, BEq

def signalDefaultBeh (sig : Signal) : SigBeh :=
  match sig.defaultBehavior with
  | .terminate _ => .sigBehTerminate
  | .ignore => .sigBehIgnore
  | .stop => .sigBehStop
  | .continue_ => .sigBehContinue

/-! # Log entries -/

inductive LogEntry where
  | logStmt (stmt : Stmt)
  | logExpansion (step : ExpansionStep)
  | logEvaluation (step : EvaluationStep)
  | logMsg (msg : String)

/-! # OS state -/

structure OsState (α : Type) where
  sh : ShellState
  symbolic : α
  fuel : Option Nat
  log : List LogEntry

/-! # Step function type -/

def StepFun (α : Type) := OsState α → Stmt → OsState α × Sum (EvaluationStep × Stmt) (Option Nat)

/-! # Parameter helpers -/

def lookupStringParam (os : OsState α) (x : String) : Option SymbolicString :=
  -- Handle positional params: pure numeric strings
  match readNat x.toList with
  | .ok n =>
    let rec getAt : Nat → List SymbolicString → Option SymbolicString
      | _, [] => none
      | 0, x :: _ => some x
      | n+1, _ :: xs => getAt n xs
    getAt n os.sh.positionalParams
  | .error _ =>
  -- Handle special parameters
  match x with
  | "$" => some (symbolicStringOfString (toString os.sh.rootpid))
  | "?" => some (symbolicStringOfString (toString os.sh.exitCode))
  | "#" =>
    let nParams := match os.sh.positionalParams with
      | [] => 0
      | _ :: rest => rest.length
    some (symbolicStringOfString (toString nParams))
  | "-" =>
    let optChars := os.sh.opts.filterMap ShOpt.charOfShOpt
    some (symbolicStringOfString (String.ofList optChars))
  | "!" => os.sh.lastPid.map (fun pid => symbolicStringOfString (toString pid))
  | "@" => none  -- handled specially in expandParam
  | "*" => none  -- handled specially in expandParam
  | _ =>
    -- Check locals first, then env
    match os.sh.locals.findSome? (fun frame => frame.findSome? (fun (y, v) => if x == y then v.1 else none)) with
    | some v => some v
    | none =>
      match os.sh.env.find? (fun (y, _) => x == y) with
      | some (_, v) => some v
      | none => none

def lookupConcreteParam (os : OsState α) (x : String) : Option String :=
  match lookupStringParam os x with
  | some ss => tryConcrete ss
  | none => none

def isSetParam (os : OsState α) (x : String) : Bool :=
  (lookupStringParam os x).isSome

/-- Search through local scopes to update opts on a variable (OCaml: set_local_param_opts_loop) -/
def setLocalParamOptsLoop (x : String) (upd : LocalOpts → LocalOpts) : List LocalEnv → Option (List LocalEnv)
  | [] => none
  | frame :: rest =>
    match frame.find? (fun (y, _) => x == y) with
    | none =>
      match setLocalParamOptsLoop x upd rest with
      | none => none
      | some rest' => some (frame :: rest')
    | some (_, (v, opts)) =>
      let frame' := (x, (v, upd opts)) :: frame.filter (fun (y, _) => x != y)
      some (frame' :: rest)

/-- Update opts on a local variable if found (OCaml: set_local_param_opts) -/
def setLocalParamOpts (os : OsState α) (x : String) (upd : LocalOpts → LocalOpts) : OsState α × Bool :=
  match setLocalParamOptsLoop x upd os.sh.locals with
  | none => (os, false)
  | some locals' => ({ os with sh := { os.sh with locals := locals' } }, true)

/-- Search through local scopes to set a variable value (OCaml: set_local_param_loop) -/
def setLocalParamLoop (x : String) (mv : Option SymbolicString) : List LocalEnv → Option (List LocalEnv)
  | [] => none
  | frame :: rest =>
    match frame.find? (fun (y, _) => x == y) with
    | none =>
      match setLocalParamLoop x mv rest with
      | none => none
      | some rest' => some (frame :: rest')
    | some (_, (_, opts)) =>
      let frame' := (x, (mv, opts)) :: frame.filter (fun (y, _) => x != y)
      some (frame' :: rest)

/-- Set a local variable value if found (OCaml: set_local_param) -/
def setLocalParamBool (os : OsState α) (x : String) (mv : Option SymbolicString) : OsState α × Bool :=
  match setLocalParamLoop x mv os.sh.locals with
  | none => (os, false)
  | some locals' => ({ os with sh := { os.sh with locals := locals' } }, true)

/-- Mark a variable as exported, checking local scopes first (OCaml: set_exported) -/
def setExported (os : OsState α) (x : String) : OsState α :=
  let (os1, foundLocal) := setLocalParamOpts os x (fun opts => { opts with localExported := true })
  if foundLocal then os1
  else { os1 with sh := { os1.sh with export_ := if os1.sh.export_.any (· == x) then os1.sh.export_ else x :: os1.sh.export_ } }

/-- Mark a variable as readonly, checking local scopes first (OCaml: set_readonly) -/
def setReadonly (os : OsState α) (x : String) : OsState α :=
  let (os1, foundLocal) := setLocalParamOpts os x (fun opts => { opts with localReadonly := true })
  if foundLocal then os1
  else { os1 with sh := { os1.sh with readonly := if os1.sh.readonly.any (· == x) then os1.sh.readonly else x :: os1.sh.readonly } }

/-- Collect variables matching a selector across globals and local scopes (OCaml: collect_vars) -/
def collectVars (getGlobals : OsState α → List String) (selectLocal : LocalOpts → Bool) (os : OsState α) :
    List (String × Option SymbolicString) :=
  -- Start with globals
  let globals := (getGlobals os).map (fun x => (x, lookupStringParam os x))
  -- Then layer in locals (foldr so more recent scopes override)
  let addLocal (frame : LocalEnv) (env : List (String × Option SymbolicString)) : List (String × Option SymbolicString) :=
    let selected := frame.filterMap (fun (x, (mv, opts)) =>
      if selectLocal opts then some (x, mv) else none)
    -- override bindings in env with the local ones
    let env' := env.filter (fun (x, _) => !selected.any (fun (y, _) => x == y))
    selected ++ env'
  os.sh.locals.foldr addLocal globals

/-- Get exported variables (OCaml: exported_vars) -/
def exportedVars (os : OsState α) : List (String × Option SymbolicString) :=
  collectVars (fun os => os.sh.export_) (fun opts => opts.localExported) os

/-- Get readonly variables (OCaml: readonly_vars) -/
def readonlyVars (os : OsState α) : List (String × Option SymbolicString) :=
  collectVars (fun os => os.sh.readonly) (fun opts => opts.localReadonly) os

/-- Get exported variables that are set (OCaml: exported_set_vars) -/
def exportedSetVars (os : OsState α) : Env :=
  (exportedVars os).filterMap (fun (x, mv) => match mv with | some v => some (x, v) | none => none)

/-- Set a variable value, checking local scopes first (OCaml: internal_set_param) -/
def internalSetParam (x : String) (v : SymbolicString) (os : OsState α) : OsState α :=
  let (os1, foundLocal) := setLocalParamBool os x (some v)
  if foundLocal then os1
  else
    let env' := (x, v) :: os.sh.env.filter (fun (y, _) => x != y)
    { os with sh := { os.sh with env := env' } }

def setLocalParam (x : String) (v : Option SymbolicString) (opts : LocalOpts) (os : OsState α) : OsState α :=
  match os.sh.locals with
  | [] => os  -- no scope to set local in
  | frame :: rest =>
    let frame' := (x, (v, opts)) :: frame.filter (fun (y, _) => x != y)
    { os with sh := { os.sh with locals := frame' :: rest } }

/-- Unset a variable, checking local scopes first (OCaml: unset_param) -/
def unsetParam (x : String) (os : OsState α) : Except String (OsState α) :=
  if os.sh.readonly.any (· == x) then
    .error s!"{x} is read-only"
  else
    let (os1, foundLocal) := setLocalParamBool os x none
    if foundLocal then .ok os1
    else
      let env' := os.sh.env.filter (fun (y, _) => x != y)
      .ok { os1 with sh := { os1.sh with
        env := env',
        readonly := os1.sh.readonly.filter (· != x),
        export_ := os1.sh.export_.filter (· != x) } }

/-! # Exit code helpers -/

def exitWith (ec : Nat) (os : OsState α) : OsState α :=
  { os with sh := { os.sh with exitCode := ec } }

/-! # Shell option helpers -/

def isMonitoring (os : OsState α) : Bool :=
  os.sh.opts.any (· == .monitor)

def getPath (os : OsState α) : String :=
  match lookupConcreteParam os "PATH" with
  | some p => p
  | none => "/usr/local/bin:/usr/bin:/bin"

def getFunctionParams (os : OsState α) : List SymbolicString :=
  match os.sh.positionalParams with
  | [] => []
  | _ :: rest => rest

def ps4 (os : OsState α) : String :=
  match lookupConcreteParam os "PS4" with
  | some s =>
    match s.toList with
    | [] => "+ "
    | c :: _ => String.ofList (List.replicate 1 c)  -- just use first char
  | none => "+ "

/-! # Logging helpers -/

def logStep (step : EvaluationStep) (os : OsState α) : OsState α :=
  { os with log := .logEvaluation step :: os.log }

def logExpansion' (step : ExpansionStep) (os : OsState α) : OsState α :=
  { os with log := .logExpansion step :: os.log }

def addToHistory (linno : Nat) (stmt : Stmt) (os : OsState α) : OsState α :=
  { os with sh := { os.sh with history := (linno, stmt) :: os.sh.history } }

/-! # Hash table helpers -/

def hashLookup (os : OsState α) (name : String) : Option (Path × Nat) :=
  match os.sh.hashes.find? (fun (k, _) => k == name) with
  | some (_, v) => some v
  | none => none

def hashInsert (os : OsState α) (name : String) (path : Path) : OsState α :=
  let hashes' := (name, (path, 0)) :: os.sh.hashes.filter (fun (k, _) => k != name)
  { os with sh := { os.sh with hashes := hashes' } }

def clearHash (os : OsState α) : OsState α :=
  { os with sh := { os.sh with hashes := [] } }

/-! # Job control helpers -/

def ecOfJobStatus (status : JobStatus) : Option Nat :=
  match status with
  | .jobDone ec => some ec
  | .jobTerminated sig => some (128 + sig.platformInt)
  | _ => none

def findJobWithPid (os : OsState α) (pid : Pid) : Option JobInfo :=
  os.sh.jobs.find? (fun j => j.pid == pid)

def deleteJob (os : OsState α) (jobId : Nat) : OsState α :=
  { os with sh := { os.sh with jobs := os.sh.jobs.filter (fun j => j.id != jobId) } }



def jobStatusOfEc (ec : Nat) : JobStatus :=
  .jobDone ec

/-! # Trap helpers -/

def checkParam (x : String) (os : OsState α) : Option String :=
  if os.sh.readonly.any (· == x) then
    some s!"{x}: is read only"
  else none

def updateTrap (sig : Signal) (handler : Option SymbolicString) (os : OsState α) : OsState α :=
  match handler with
  | none =>
    let traps' := os.sh.traps.filter (fun (s, _) => s != sig)
    { os with sh := { os.sh with traps := traps' } }
  | some h =>
    let traps' := (sig, h) :: os.sh.traps.filter (fun (s, _) => s != sig)
    { os with sh := { os.sh with traps := traps' } }

def exitTrap (os : OsState α) : OsState α × Option SymbolicString :=
  match os.sh.traps.find? (fun (s, _) => s == .EXIT) with
  | some (_, h) =>
    -- Remove EXIT trap after retrieval (OCaml: update_trap s0 EXIT Nothing)
    let traps' := os.sh.traps.filter (fun (s, _) => s != .EXIT)
    ({ os with sh := { os.sh with traps := traps' } }, some h)
  | none => (os, none)

def clearTrapsForSubshell (os : OsState α) : OsState α × List Signal :=
  -- Partition traps into ignored (empty handler) and handled (non-empty)
  let ignored := os.sh.traps.filter (fun (_, h) => h.isEmpty)
  let handled := os.sh.traps.filter (fun (_, h) => !h.isEmpty)
  -- Save original traps as supershell_traps; keep only ignored
  ({ os with sh := { os.sh with
      traps := ignored,
      supershellTraps := some os.sh.traps } },
   handled.map (fun (sig, _) => sig))

def clearSupershellTraps (os : OsState α) : OsState α :=
  { os with sh := { os.sh with supershellTraps := none } }

/-! # Concretize helpers -/

def concretize (os : OsState α) (ss : SymbolicString) : OsState α × SymbolicString × String :=
  match tryConcrete ss with
  | some s => (os, ss, s)
  | none => (os, ss, "")  -- unsound fallback

def concretizeMany (os : OsState α) (sss : Fields) : OsState α × Fields × List String :=
  let rec go (os : OsState α) (acc : Fields × List String) : List SymbolicString → OsState α × Fields × List String
    | [] => (os, acc.1.reverse, acc.2.reverse)
    | ss :: sss' =>
      let (os', ss', s) := concretize os ss
      go os' (ss' :: acc.1, s :: acc.2) sss'
  go os ([], []) sss

/-! # Function and positional param management -/

/-- Look up a function definition by name -/
def lookupFunction (os : OsState α) (name : String) : Option Stmt :=
  match os.sh.funcs.find? (fun (n, _) => n == name) with
  | some (_, body) => some body
  | none => none

/-- Set function params: preserves $0, replaces $1+ with argv, sets loopNest -/
def setFunctionParams (ln : Nat) (argv : Fields) (os : OsState α) : OsState α :=
  let newParams := match os.sh.positionalParams with
    | [] => [] :: argv  -- no $0, use empty
    | arg0 :: _ => arg0 :: argv
  { os with sh := { os.sh with loopNest := ln, positionalParams := newParams } }



/-! # Env building -/

def lookupParam (os : OsState α) (x : String) : Option SymbolicString :=
  lookupStringParam os x

def getEnv (os : OsState α) : Env :=
  -- collect exported vars
  let exported := os.sh.export_
  os.sh.env.filter (fun (x, _) => exported.any (· == x))

/-! # Redirection helpers -/

/-! # Subshell prep -/

def prepareSubshell (os : OsState α) : OsState α :=
  let (os1, _clearedSignals) := clearTrapsForSubshell os
  { os1 with sh :=
    { os1.sh with
      outermost := false,
      jobs := [],
      loopNest := 0 } }

/-! # OS Typeclass -/

class OS (α : Type) where
  -- initialization
  osInit : InteractivityMode → ShellLevel → OsState α
  osTick : OsState α → OsState α

  -- parsing
  osSetPs1 : OsState α → SymbolicString → OsState α
  osSetPs2 : OsState α → SymbolicString → OsState α

  -- process management
  osExecve : OsState α → SymbolicString → OsState α
  osForkAndSubshell : OsState α → Stmt → BgMode → Option Pid → Bool → OsState α × Pid
  osExit : OsState α → OsState α
  osGetpwnam : OsState α → String → Option String

  -- wait
  osWaitpid : StepFun α → OsState α → Pid → OsState α × Option (Sum EvaluationStep Nat)
  osWaitchild : OsState α → OsState α × Option (Pid × JobStatus)

  -- signals
  osHandleSignal : OsState α → Signal → Option SymbolicString → OsState α
  osSignalPid : OsState α → Signal → Pid → Bool → OsState α × Bool
  osPendingSignal : OsState α → OsState α × Option Signal

  -- terminal control
  osTcSetfg : OsState α → Pid → OsState α × Bool
  osSetJobControl : OsState α → Bool → OsState α

  -- times
  osTimes : OsState α → String × String × String × String

  -- umask
  osGetUmask : OsState α → Perms
  osSetUmask : OsState α → Perms → OsState α

  -- file system
  osPhysicalCwd : OsState α → String
  osChdir : OsState α → Path → OsState α × Option String
  osReaddir : OsState α → Path → List (Path × FileUnit)
  osFileExists : OsState α → Path → Bool

  -- stat calls
  osFileType : OsState α → Path → Option FileType
  osFileTypeFollow : OsState α → Path → Option FileType
  osFileSize : OsState α → Path → Option Nat
  osFilePerms : OsState α → Path → Option Perms
  osFileMtime : OsState α → Path → Option Float
  osFileNumber : OsState α → Path → Option (Int × Int)
  osIsTty : OsState α → Fd → Bool
  osIsReadable : OsState α → Path → Bool
  osIsWriteable : OsState α → Path → Bool
  osIsExecutable : OsState α → Path → Bool
  osReadFile : OsState α → Path → Option String := fun _ _ => none

  -- directory/file management (non-standard, for symbolic test mode)
  osMkdir : OsState α → Path → Bool → OsState α × Bool := fun os _ _ => (os, true)
  osRmFile : OsState α → Path → Bool → OsState α × Bool := fun os _ _ => (os, true)

  -- fd operations
  osWriteFd : OsState α → Fd → String → Option (OsState α)
  osReadAllFd : StepFun α → OsState α → Fd → OsState α × Sum EvaluationStep (Option String)
  osReadLineFd : OsState α → Fd → EscapeMode → OsState α × ReadResult String
  osCloseFd : OsState α → Fd → OsState α

  -- pipes
  osPipe : OsState α → Sum String (OsState α × Fd × Fd)

  -- redirects
  osOpenFileForRedir : OsState α → RedirType → SymbolicString → OsState α × Sum String Fd
  osOpenHeredoc : OsState α → String → Sum String (OsState α × Fd)
  osCloseAndSaveFd : OsState α → Fd → OsState α × Sum String SavedFds
  osRenumberFd : OsState α → OrigFdAction → Fd → Fd → OsState α × Sum String SavedFds
  osRestoreFd : OsState α → Fd → SavedFdInfo → OsState α

/-! # Logging wrapper functions -/

section OsWrappers
variable {α : Type} [OS α]

def logTraceWith (writeStderr : String → OsState α → OsState α) (tag : TraceTag) (msg : String) (os : OsState α) : OsState α :=
  if os.sh.opts.any (· == .trace tag) then
    writeStderr s!"smoosh [{tag.toString}]: {msg}\n" os
  else os

def unloggedWriteStderr (s : String) (os : OsState α) : OsState α :=
  match OS.osWriteFd os STDERR s with
  | some os' => os'
  | none => os

def logTrace (tag : TraceTag) (msg : String) (os : OsState α) : OsState α :=
  logTraceWith unloggedWriteStderr tag msg os

/-- wrapped syscalls -/
def tick (os : OsState α) : OsState α :=
  let os' := OS.osTick os
  { os' with fuel := os'.fuel.map (fun n => if n > 0 then n - 1 else 0) }

def writeStdout (msg : String) (os : OsState α) : OsState α :=
  match OS.osWriteFd os STDOUT msg with
  | some os' => os'
  | none => os

def writeStderr (msg : String) (os : OsState α) : OsState α :=
  unloggedWriteStderr msg os

def tryWriteFd (fd : Fd) (s : String) (os : OsState α) : OsState α × Bool :=
  match OS.osWriteFd os fd s with
  | some os' => (os', true)
  | none => (os, false)

def failWithCode (ec : Nat) (msg : String) (os : OsState α) : OsState α :=
  exitWith ec (writeStderr (msg ++ "\n") os)

def failWith (msg : String) (os : OsState α) : OsState α :=
  failWithCode 1 msg os

def safeWriteStdout (writer : String) (msg : String) (os : OsState α) : OsState α :=
  let (os', ok) := tryWriteFd STDOUT msg os
  if !ok then failWithCode 2 s!"smoosh: {writer}: I/O error" os'
  else os'

def safeWriteStderr (msg : String) (os : OsState α) : OsState α :=
  let (os', ok) := tryWriteFd STDERR msg os
  if !ok then exitWith 2 os'
  else os'

/-- FS and path manipulation -/
def dotdot (path : Path) : Path :=
  match path.toList.reverse.dropWhile (· != '/') with
  | [] => "/"
  | '/' :: [] => "/"
  | '/' :: rest => String.ofList rest.reverse
  | rest => String.ofList rest.reverse

def isDir (os : OsState α) (path : Path) : Bool :=
  OS.osFileType os path == some .fileDirectory

def canonicalizeSplitPath (os : OsState α) (path : Path) : List String → Option String
  | [] => some path
  | "" :: components' => canonicalizeSplitPath os path components'
  | "." :: components' => canonicalizeSplitPath os path components'
  | ".." :: components' =>
    if isDir os path then canonicalizeSplitPath os (dotdot path) components'
    else none
  | dir :: components' => canonicalizeSplitPath os (joinPath path dir) components'

def canonicalizePath (os : OsState α) (path : Path) : Option Path :=
  let chars := path.toList
  let (initial, path') :=
    match chars with
    | '/' :: '/' :: rest => ("//", String.ofList rest)
    | '/' :: rest => ("/", String.ofList rest)
    | _ => ("/", path)
  canonicalizeSplitPath os initial (splitStringOn false '/' path')

/-- Redirect execution -/
def redirect (os : OsState α) (er : ExpandedRedir) : OsState α × Sum String SavedFds :=
  match er with
  | .erFile ty wantedFd sfile =>
    match OS.osOpenFileForRedir os ty sfile with
    | (os1, .inl err) => (os1, .inl err)
    | (os1, .inr newFd) => OS.osRenumberFd os1 .closeOrig newFd wantedFd
  | .erDup _ _ origFd none =>
    OS.osCloseAndSaveFd os origFd
  | .erDup _ origAction origFd (some wantedFd) =>
    OS.osRenumberFd os origAction wantedFd origFd
  | .erHeredoc _ wantedFd ss =>
    let (os1, _, s) := concretize os ss
    match OS.osOpenHeredoc os1 s with
    | .inl err => (os1, .inl err)
    | .inr (os2, newFd) => OS.osRenumberFd os2 .closeOrig newFd wantedFd

def restoreFds (os : OsState α) (savedFds : SavedFds) : OsState α :=
  savedFds.foldr (fun (origFd, info) os' => OS.osRestoreFd os' origFd info) os

def reallyDoRedirs (os : OsState α) : List ExpandedRedir → OsState α × Sum String SavedFds
  | [] => (os, .inr [])
  | er :: ers' =>
    match redirect os er with
    | (os1, .inl err) => (os1, .inl err)
    | (os1, .inr saved) =>
      match reallyDoRedirs os1 ers' with
      | (os2, .inl err) => (os2, .inl err)
      | (os2, .inr saved') => (os2, .inr (saved ++ saved'))

def doRedirs (os : OsState α) (ers : List ExpandedRedir) : OsState α × Sum String SavedFds :=
  if os.sh.opts.any (· == .noexec)
  then (os, .inr [])
  else reallyDoRedirs os ers

/-- Pipe execution -/
def forkPipeSubshell (os : OsState α) (stmt : Stmt) (bgm : BgMode) (pgid : Option Pid) (last : Bool) (pipeline : PipelineInfo) : OsState α × PipelineInfo × Pid :=
  let (os1, pid) := OS.osForkAndSubshell os stmt bgm pgid last
  (os1, pipeline, pid)

/-- Set the last background PID -/
def setLastPid (pid : Pid) (os : OsState α) : OsState α :=
  { os with sh := { os.sh with lastPid := some pid } }

/-- Delete a job by PID -/
def deleteJobWithPid (os : OsState α) (pid : Pid) : OsState α :=
  { os with sh := { os.sh with jobs := os.sh.jobs.filter (fun j => j.pid != pid) } }

/-- Add a job to the job list -/
def addJob (os : OsState α) (pipeline : PipelineInfo) (pid : Pid) (cmd : Stmt) (bgm : BgMode) (status : JobStatus) : OsState α × JobInfo :=
  let highestId := match os.sh.jobs with
    | [] => 0
    | jobs => jobs.foldl (fun acc j => max acc j.id) 0
  let newJob : JobInfo := {
    id := highestId + 1,
    pid := pid,
    cmd := cmd,
    status := status,
    pipeline := pipeline
  }
  ({ os with sh := { os.sh with jobs := newJob :: os.sh.jobs } }, newJob)

/-- Check if bg mode -/
def isBg : BgMode → Bool
  | .bg => true
  | .fg => false

/-- Check if running interactively -/
def isInteractive (os : OsState α) : Bool :=
  os.sh.opts.any (· == .interactive)


/-- Parameter management -/
def xtrace (msg : String) (os : OsState α) : OsState α :=
  if os.sh.opts.any (· == .xtrace) && msg != "" then
    writeStderr (ps4 os ++ msg ++ "\n") os
  else os

def checkedSetParam (x : String) (v : SymbolicString) (os : OsState α) : OsState α :=
  let os1 := internalSetParam x v os
  let os2 :=
    if os1.sh.opts.any (· == .allexport) then
      { os1 with sh := { os1.sh with export_ := if os1.sh.export_.any (· == x) then os1.sh.export_ else x :: os1.sh.export_ } }
    else os1
  if x == "OPTIND" then
    { os2 with sh := { os2.sh with optoff := none } }
  else if x == "PATH" then
    clearHash os2
  else os2

def setParam (x : String) (v : SymbolicString) (os : OsState α) : Sum String (OsState α) :=
  match checkParam x os with
  | some err => .inl err
  | none => .inr (checkedSetParam x v os)

/-- Pop the topmost local scope, returning bindings -/
def popLocals (os : OsState α) : OsState α × List (String × Option SymbolicString) :=
  match os.sh.locals with
  | [] => (os, [])  -- shouldn't happen
  | frame :: rest =>
    let bindings := frame.map (fun (x, (v, _opts)) => (x, v))
    ({ os with sh := { os.sh with locals := rest } }, bindings)

/-- Push a new local scope from env -/
def pushLocals (os : OsState α) (env : Env) : OsState α :=
  let frame := env.map (fun (x, v) => (x, (some v, localOptsDefault)))
  { os with sh := { os.sh with locals := frame :: os.sh.locals } }

/-- Push a new empty local scope — for command assignment expansion -/
def newLocalScope (os : OsState α) : OsState α :=
  { os with sh := { os.sh with locals := [] :: os.sh.locals } }

/-- Write to topmost local scope (returns error for readonly) -/
def forceLocalParam (os : OsState α) (x : String) (v : SymbolicString) : Sum String (OsState α) :=
  match os.sh.locals with
  | [] => .inl "force_local_param: no local scope"
  | frame :: rest =>
    match checkParam x os with
    | some err => .inl err
    | none =>
      let frame' := (x, (some v, localOptsDefault)) :: frame.filter (fun (y, _) => x != y)
      .inr { os with sh := { os.sh with locals := frame' :: rest } }

/-- Close a file descriptor -/
def closeFd (os : OsState α) (fd : Fd) : OsState α :=
  OS.osCloseFd os fd

/-- Run a pipe loop — connects processes with pipe FDs -/
def runPipeLoop (os : OsState α) (stmts : List Stmt) (fdPrev : Fd) (bgm : BgMode) (pgid : Option Pid) (pipeline : PipelineInfo) :
    Sum String (OsState α × PipelineInfo × Pid) :=
  match stmts with
  | [] =>
    .inr (forkPipeSubshell os .done bgm pgid true pipeline)
  | [stmt] =>
    let (os1, pipeline', lastPid) := forkPipeSubshell os
      (withRedirs (tryAvoidFork stmt) [.erDup .toFD .closeOrig STDIN (some fdPrev)])
      bgm pgid true pipeline
    let os2 := closeFd os1 fdPrev
    .inr (os2, ((lastPid, stmt) :: pipeline').reverse, lastPid)
  | stmt :: stmts' =>
    match OS.osPipe os with
    | .inl err => .inl err
    | .inr (os1, fdNext, fdWrite) =>
      let (os2, pipeline', pid) := forkPipeSubshell os1
        (withRedirs (closeFdAndThen fdNext stmt)
          [.erDup .toFD .closeOrig STDIN (some fdPrev),
           .erDup .toFD .closeOrig STDOUT (some fdWrite)])
        bgm pgid false pipeline
      let os3 := closeFd os2 fdPrev
      let os4 := closeFd os3 fdWrite
      runPipeLoop os4 stmts' fdNext bgm (some pid) ((pid, stmt) :: pipeline')

/-- Run a pipeline — entry point -/
def runPipe (os : OsState α) (stmts : List Stmt) (bgm : BgMode) :
    Sum String (OsState α × PipelineInfo × Pid) :=
  match stmts with
  | [] => .inr (forkPipeSubshell os .done bgm none true [])
  | [stmt] => .inr (forkPipeSubshell os stmt bgm none true [])
  | stmt :: stmts' =>
    match OS.osPipe os with
    | .inl err => .inl err
    | .inr (os1, fdNext, fdWrite) =>
      let (os2, pipeline, pid) := forkPipeSubshell os1
        (withRedirs (closeFdAndThen fdNext stmt)
          [.erDup .toFD .closeOrig STDOUT (some fdWrite)])
        bgm none false []
      let os3 := closeFd os2 fdWrite
      runPipeLoop os3 stmts' fdNext bgm (some pid) ((pid, stmt) :: pipeline)

/-- Shell option management -/
def setShOpt (os : OsState α) (opt : ShOpt) : OsState α :=
  let os1 :=
    if opt == .monitor then
      let os0 := OS.osSetJobControl os true
      let os1 := OS.osHandleSignal os0 .SIGTTOU (some [])
      let os2 := OS.osHandleSignal os1 .SIGTTIN (some [])
      OS.osHandleSignal os2 .SIGTSTP (some [])
    else os
  { os1 with sh := { os1.sh with opts := if os1.sh.opts.any (· == opt) then os1.sh.opts else opt :: os1.sh.opts } }

def unsetShOpt (os : OsState α) (opt : ShOpt) : OsState α :=
  let os1 :=
    if opt == .monitor then
      let os0 := OS.osSetJobControl os false
      let os1 := OS.osHandleSignal os0 .SIGTTOU none
      let os2 := OS.osHandleSignal os1 .SIGTTIN none
      OS.osHandleSignal os2 .SIGTSTP none
    else os
  { os1 with sh := { os1.sh with opts := os1.sh.opts.filter (· != opt) } }

/-- Wait helpers -/
def waitpidOrLookup (stepEval : StepFun α) (os : OsState α) (pid : Pid) :
    OsState α × Option (Sum EvaluationStep Nat) :=
  match OS.osWaitpid stepEval os pid with
  | (os1, none) =>
    match findJobWithPid os1 pid with
    | none => (os1, none)
    | some job =>
      match ecOfJobStatus job.status with
      | none => (os1, none)
      | some code =>
        let os2 := deleteJob os1 job.id
        (os2, some (.inr code))
  | (os1, some (.inl step)) => (os1, some (.inl step))
  | (os1, some (.inr code)) =>
    (os1, some (.inr code))

def waitForJob (stepEval : StepFun α) (os : OsState α) (_job : JobInfo) :
    List (Pid × Stmt) → Pid → Option Nat → OsState α × Option (Sum EvaluationStep Nat)
  | [], _, none => waitpidOrLookup stepEval os _job.pid
  | [], _, some ec => (os, some (.inr ec))
  | (pid, _) :: pipeline', tgtPid, mec =>
    match waitpidOrLookup stepEval os pid with
    | (os1, none) => (os1, none)
    | (os1, some (.inl step)) => (os1, some (.inl step))
    | (os1, some (.inr ec)) =>
      waitForJob stepEval os1 _job pipeline' tgtPid (if pid == tgtPid then some ec else mec)

def waitForPid (stepEval : StepFun α) (os : OsState α) (pid : Pid) :
    OsState α × Option (Sum EvaluationStep Nat) :=
  match findJobWithPid os pid with
  | none => waitpidOrLookup stepEval os pid
  | some job => waitForJob stepEval os job job.pipeline.reverse pid none

end OsWrappers
