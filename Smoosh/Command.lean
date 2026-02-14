/-
  Smoosh.Command — Builtins, path resolution, command execution
  Translated from command.lem (2816 lines)
-/
import Smoosh.Semantics
import Smoosh.Test

/-! # Non-builtin utility list -/

def nonBuiltinUtilities : List String :=
  ["basename", "cat", "chgrp", "chmod", "chown", "cmp", "comm",
   "cp", "cut", "diff", "dirname", "ed", "env", "expand", "expr",
   "find", "fold", "fuser", "grep", "head", "id", "join", "ln",
   "ls", "mkdir", "mkfifo", "mv", "nl", "od", "paste", "pathchk",
   "rm", "rmdir", "sed", "sleep", "sort", "strings", "stty", "tail",
   "tee", "touch", "tr", "tsort", "tty", "unexpand", "uniq", "wc",
   "xargs"]

def nonBuiltinSpecialUtilities : List String :=
  ["awk", "bc", "getopts", "hash", "help", "jobs", "kill", "newgrp", "printf",
   "pwd", "read", "test", "true", "type", "ulimit", "umask", "unalias",
   "wait"]

/-! # Builtin names -/

def builtinNames : List String :=
  [".", ":", "[", "alias", "bg", "break", "cd", "command", "continue",
   "echo", "eval", "exec", "exit", "export", "false", "fc", "fg",
   "getopts", "hash", "history", "jobs", "kill", "local", "printf",
   "pwd", "read", "readonly", "return", "set", "shift", "source",
   "test", "times", "trap", "true", "type", "ulimit", "umask",
   "unalias", "unset", "wait"]

def specialBuiltinNames : List String :=
  [".", ":", "break", "continue", "eval", "exec", "exit", "export",
   "readonly", "return", "set", "shift", "source", "times", "trap", "unset"]

def isSpecialBuiltin (name : String) : Bool := name ∈ specialBuiltinNames
def isBuiltin (name : String) : Bool := name ∈ builtinNames

/-! # Path resolution -/

section Commands
variable {α : Type} [OS α]

def resolvePathWith (ok : Path → Bool) (paths : List Path) (name : String) : Option Path :=
  let attempt (path' : String) : Option Path :=
    let altered := path' ++ "/" ++ name
    if ok altered then some altered else none
  paths.findSome? attempt

def resolveCommandNameInPath (s : OsState α) (path : String) (prog : String) : OsState α × Option String :=
  if prog.toList.any (· == '/') then
    (s, some prog)
  else
    match hashLookup s prog with
    | none =>
      let paths := splitStringOn false ':' path
      let mPath := resolvePathWith (fun p => OS.osIsExecutable s p) paths prog
      let s' := match mPath with
        | none => s
        | some p => hashInsert s prog p
      (s', mPath)
    | some (p, _) => (s, some p)

def resolveCommandName (s : OsState α) (prog : String) : OsState α × Option String :=
  resolveCommandNameInPath s (getPath s) prog

/-! # Builtin implementations -/

-- Each builtin: (os_state, argv, env) → Sum (os_state × String) (os_state × Stmt × Bool)
-- Left = error, Right = (new state, continuation, is_special_builtin)

def builtinColon (s : OsState α) (_argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  .inr (exitWith 0 s, .done, true)

def builtinTrue (s : OsState α) (_argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  .inr (exitWith 0 s, .done, false)

def builtinFalse (s : OsState α) (_argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  .inr (exitWith 1 s, .done, false)

def builtinBreak (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  match argv with
  | [] | [_] => .inr (s, .break_ 1, true)
  | [_, n] =>
    match tryConcrete n with
    | some ns =>
      match readNat ns.toList with
      | .ok n => .inr (s, .break_ n, true)
      | .error _ => .inl (s, ns ++ ": positive argument required")
    | none => .inl (s, "symbolic argument")
  | _ => .inl (s, "too many arguments")

def builtinContinue (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  match argv with
  | [] | [_] => .inr (s, .continue_ 1, true)
  | [_, n] =>
    match tryConcrete n with
    | some ns =>
      match readNat ns.toList with
      | .ok n => .inr (s, .continue_ n, true)
      | .error _ => .inl (s, ns ++ ": positive argument required")
    | none => .inl (s, "symbolic argument")
  | _ => .inl (s, "too many arguments")

def builtinExit (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let ec := match argv with
    | [] | [_] => s.sh.exitCode
    | [_, n] =>
      match tryConcrete n with
      | some ns =>
        match readNat ns.toList with
        | .ok code => code % 256
        | .error _ => 2
      | none => 2
    | _ => 2
  .inr (exitWith ec s, .exit_, true)

def builtinReturn (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let ec := match argv with
    | [] | [_] => s.sh.exitCode
    | [_, n] =>
      match tryConcrete n with
      | some ns =>
        match readNat ns.toList with
        | .ok code => code % 256
        | .error _ => 2
      | none => 2
    | _ => 2
  .inr (exitWith ec s, .return_, true)

def builtinCd (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let dir := match argv with
    | [] | [_] =>
      match lookupConcreteParam s "HOME" with
      | some d => d
      | none => "/"
    | [_, d] =>
      match tryConcrete d with
      | some d' => d'
      | none => "/"
    | _ => "/"
  let (s', err) := OS.osChdir s dir
  match err with
  | none =>
    let s'' := { s' with sh := { s'.sh with cwd := dir } }
    .inr (exitWith 0 s'', .done, false)
  | some msg => .inl (s', "cd: " ++ msg)

def builtinPwd (s : OsState α) (_argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let cwd := s.sh.cwd
  let s' := writeStdout (cwd ++ "\n") s
  .inr (exitWith 0 s', .done, false)

def builtinEcho (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let args := match argv with
    | [] => []
    | _ :: rest => rest
  let strs := args.filterMap tryConcrete
  let msg := String.intercalate " " strs ++ "\n"
  let s' := writeStdout msg s
  .inr (exitWith 0 s', .done, false)

def builtinExport (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let args := match argv with
    | [] => []
    | _ :: rest => rest
  let s' := args.foldl (fun os arg =>
    match tryConcrete arg with
    | some astr =>
      let parts := splitStringOn false '=' astr
      match parts with
      | [name] =>
        { os with sh := { os.sh with export_ :=
          if name ∈ os.sh.export_ then os.sh.export_ else name :: os.sh.export_ } }
      | name :: valParts =>
        let val := String.intercalate "=" valParts
        let os' := internalSetParam name (symbolicStringOfString val) os
        { os' with sh := { os'.sh with export_ :=
          if name ∈ os'.sh.export_ then os'.sh.export_ else name :: os'.sh.export_ } }
      | _ => os
    | none => os) s
  .inr (exitWith 0 s', .done, true)

def builtinUnset (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let args := match argv with
    | [] => []
    | _ :: rest => rest
  let s' := args.foldl (fun os arg =>
    match tryConcrete arg with
    | some name =>
      match unsetParam name os with
      | .ok os' => os'
      | .error _ => os
    | none => os) s
  .inr (exitWith 0 s', .done, true)

def builtinSet (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  match argv with
  | [] | [_] =>
    -- Print all variables (simplified)
    .inr (exitWith 0 s, .done, true)
  | _ :: args =>
    -- Set options or positional params
    let s' := args.foldl (fun os arg =>
      match tryConcrete arg with
      | some astr =>
        match astr.toList with
        | '-' :: opts =>
          opts.foldl (fun os' c =>
            match ShOpt.ofShortopt c with
            | some opt => setShOpt os' opt
            | none => os') os
        | '+' :: opts =>
          opts.foldl (fun os' c =>
            match ShOpt.ofShortopt c with
            | some opt => unsetShOpt os' opt
            | none => os') os
        | _ => os
      | none => os) s
    .inr (exitWith 0 s', .done, true)

def builtinShift (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let n := match argv with
    | [] | [_] => 1
    | [_, ns] =>
      match tryConcrete ns with
      | some s => match readNat s.toList with | .ok n => n | .error _ => 1
      | none => 1
    | _ => 1
  let params := s.sh.positionalParams
  let shifted := match params with
    | [] => []
    | prog :: rest => prog :: rest.drop n
  .inr (exitWith 0 { s with sh := { s.sh with positionalParams := shifted } }, .done, true)

def builtinTrap (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  match argv with
  | [] | [_] =>
    -- List traps
    .inr (exitWith 0 s, .done, true)
  | [_, handler, sigName] =>
    match tryConcrete handler, tryConcrete sigName with
    | some h, some sn =>
      match Signal.ofString sn with
      | some sig =>
        let s' := if h == "" || h == "-" then
          updateTrap sig none s
        else
          updateTrap sig (some (symbolicStringOfString h)) s
        .inr (exitWith 0 s', .done, true)
      | none => .inl (s, "trap: " ++ sn ++ ": invalid signal specification")
    | _, _ => .inl (s, "trap: symbolic arguments")
  | _ =>
    -- Multiple signals
    .inr (exitWith 0 s, .done, true)

def builtinReadonly (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let args := match argv with
    | [] => []
    | _ :: rest => rest
  let s' := args.foldl (fun os arg =>
    match tryConcrete arg with
    | some name =>
      { os with sh := { os.sh with readonly :=
        if name ∈ os.sh.readonly then os.sh.readonly else name :: os.sh.readonly } }
    | none => os) s
  .inr (exitWith 0 s', .done, true)

def builtinAlias (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  match argv with
  | [] | [_] =>
    -- List aliases
    .inr (exitWith 0 s, .done, false)
  | _ :: args =>
    let s' := args.foldl (fun os arg =>
      match tryConcrete arg with
      | some astr =>
        let parts := splitStringOn false '=' astr
        match parts with
        | [name, val] =>
          { os with sh := { os.sh with aliases :=
            (name, val) :: os.sh.aliases.filter (fun (n, _) => n != name) } }
        | _ => os
      | none => os) s
    .inr (exitWith 0 s', .done, false)

def builtinUnalias (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let args := match argv with
    | [] => []
    | _ :: rest => rest
  let s' := args.foldl (fun os arg =>
    match tryConcrete arg with
    | some name =>
      { os with sh := { os.sh with aliases := os.sh.aliases.filter (fun (n, _) => n != name) } }
    | none => os) s
  .inr (exitWith 0 s', .done, false)

def builtinTest (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let args := match argv with
    | [] => []
    | _ :: rest => rest
  -- Strip trailing "]" for [ command
  let args' := match argv with
    | [] => args
    | cmd :: _ =>
      match tryConcrete cmd with
      | some "[" =>
        if args.isEmpty then args
        else
          match args.getLast? with
          | some last =>
            if tryConcrete last == some "]" then args.dropLast
            else args
          | none => args
      | _ => args
  let strs := args'.filterMap tryConcrete
  if strs.isEmpty then
    .inr (exitWith 1 s, .done, false)  -- empty test is false
  else
    match parseTestExpr strs with
    | .error err =>
      .inl (s, "test: " ++ err)
    | .ok expr =>
      let result := if evalTestExpr s expr then 0 else 1
      .inr (exitWith result s, .done, false)

def builtinType (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let args := match argv with
    | [] => []
    | _ :: rest => rest
  let (s', ec) := args.foldl (fun (os, ec) arg =>
    match tryConcrete arg with
    | some name =>
      if isBuiltin name then
        (writeStdout (name ++ " is a shell builtin\n") os, ec)
      else
        let (os', mpath) := resolveCommandName os name
        match mpath with
        | some path => (writeStdout (name ++ " is " ++ path ++ "\n") os', ec)
        | none => (writeStderr (name ++ ": not found\n") os', 1)
    | none => (os, ec)) (s, 0)
  .inr (exitWith ec s', .done, false)

def builtinUmask (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  match argv with
  | [] | [_] =>
    let umask := OS.osGetUmask s
    let s' := writeStdout (padLeftWith '0' (unboundedWriteOctal (Int.ofNat (natOfPerms umask))) 4 ++ "\n") s
    .inr (exitWith 0 s', .done, false)
  | [_, m] =>
    match tryConcrete m with
    | some ms =>
      match readNat ms.toList with
      | .ok n =>
        let s' := OS.osSetUmask s (permsOfNat n)
        .inr (exitWith 0 s', .done, false)
      | .error _ => .inl (s, "umask: " ++ ms ++ ": octal number expected")
    | none => .inl (s, "umask: symbolic argument")
  | _ => .inl (s, "umask: too many arguments")

def builtinEval (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let args := match argv with
    | [] => []
    | _ :: rest => rest
  let strs := args.filterMap tryConcrete
  let combined := String.intercalate " " strs
  if combined == "" then
    .inr (exitWith 0 s, .done, true)
  else
    .inr (s, .evalLoop 0 (none, none) (.parseString .parseEval combined) .noninteractive .subsidiary, true)

def builtinDot (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  match argv with
  | _ :: f :: _ =>
    match tryConcrete f with
    | some filename =>
      .inr (s, .evalLoop 0 (none, none) (.parseFile filename .noPushFile) .noninteractive .subsidiary, true)
    | none => .inl (s, ".: symbolic filename")
  | _ => .inl (s, ".: filename argument required")

def builtinWait (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  match argv with
  | [] | [_] =>
    -- Wait for all children
    .inr (exitWith 0 s, .done, false)
  | [_, pidArg] =>
    match tryConcrete pidArg with
    | some ps =>
      match readNat ps.toList with
      | .ok pid => .inr (s, .wait pid .unchecked none .waitCommand, false)
      | .error _ => .inl (s, "wait: " ++ ps ++ ": not a valid pid")
    | none => .inl (s, "wait: symbolic argument")
  | _ => .inl (s, "wait: too many arguments")

def builtinTimes (s : OsState α) (_argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let (ut, st, cut, cst) := OS.osTimes s
  let s' := writeStdout (ut ++ " " ++ st ++ "\n" ++ cut ++ " " ++ cst ++ "\n") s
  .inr (exitWith 0 s', .done, true)

/-! # Read builtin -/

def builtinRead (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let args := match argv with
    | [] => []
    | _ :: rest => rest
  -- parse -r flag
  let (rawMode, varArgs) := match args with
    | ss :: rest =>
      match tryConcrete ss with
      | some "-r" => (EscapeMode.escapeOff, rest)
      | _ => (.escapeOn, args)
    | _ => (.escapeOn, args)
  let varNames := varArgs.filterMap tryConcrete
  -- if no variable names, default to REPLY
  let varNames' := if varNames.isEmpty then ["REPLY"] else varNames
  -- read a line from stdin
  let (s1, (line, _rest, eof)) := OS.osReadLineFd s STDIN rawMode
  -- split line by IFS
  let ifsStr := match lookupConcreteParam s1 "IFS" with
    | some ifs => ifs
    | none => " \t\n"
  let parts := ifsStr.toList.head?.map (fun sep =>
    splitStringOn false sep line) |>.getD [line]
  -- assign to variables
  let s2 := assignToVars s1 varNames' parts
  let ec := match eof with | .hitEof => 1 | .noEof => 0
  .inr (exitWith ec s2, .done, false)
where
  assignToVars (s : OsState α) (vars : List String) (vals : List String) : OsState α :=
    match vars, vals with
    | [], _ => s
    | [v], rest => checkedSetParam v (symbolicStringOfString (String.intercalate " " rest)) s
    | _ :: _, [] => s
    | v :: vs, val :: rest => assignToVars (checkedSetParam v (symbolicStringOfString val) s) vs rest

/-! # Printf builtin -/

def builtinPrintf (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let args := match argv with
    | [] => []
    | _ :: rest => rest
  match args with
  | [] => .inl (s, "printf: usage: printf format [arguments]")
  | fmtSS :: rest =>
    match tryConcrete fmtSS with
    | none => .inl (s, "printf: symbolic format")
    | some fmt =>
      let restStrs := rest.filterMap tryConcrete
      -- simplified printf: handle %s, %d, \n, \t, \\, %%
      let result := simplePrintf fmt restStrs
      let s' := writeStdout result s
      .inr (exitWith 0 s', .done, false)
where
  simplePrintf (fmt : String) (args : List String) : String :=
    go fmt.toList args []
  go : List Char → List String → List Char → String
    | [], _, acc => String.ofList acc.reverse
    | '%' :: 's' :: rest, arg :: args', acc =>
      go rest args' (arg.toList.reverse ++ acc)
    | '%' :: 's' :: rest, [], acc =>
      go rest [] acc
    | '%' :: 'd' :: rest, arg :: args', acc =>
      go rest args' (arg.toList.reverse ++ acc)
    | '%' :: 'd' :: rest, [], acc =>
      go rest [] (('0' :: acc))
    | '%' :: '%' :: rest, args, acc =>
      go rest args ('%' :: acc)
    | '\\' :: 'n' :: rest, args, acc =>
      go rest args ('\n' :: acc)
    | '\\' :: 't' :: rest, args, acc =>
      go rest args ('\t' :: acc)
    | '\\' :: '\\' :: rest, args, acc =>
      go rest args ('\\' :: acc)
    | c :: rest, args, acc =>
      go rest args (c :: acc)

/-! # Getopts builtin -/

def builtinGetopts (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  match argv with
  | _ :: optstrSS :: varSS :: _ =>
    match tryConcrete optstrSS, tryConcrete varSS with
    | some optstring, some varname =>
      -- Get OPTIND
      let optind := match lookupConcreteParam s "OPTIND" with
        | some s => match readNat s.toList with | .ok n => n | .error _ => 1
        | none => 1
      -- Index into positional params
      let params := getFunctionParams s
      let idx := optind  -- 1-based
      if idx > params.length then
        -- No more arguments
        let s' := checkedSetParam varname (symbolicStringOfString "?") s
        .inr (exitWith 1 s', .done, false)
      else
        let paramAt := params.drop (idx - 1)
        match paramAt with
        | [] =>
          let s' := checkedSetParam varname (symbolicStringOfString "?") s
          .inr (exitWith 1 s', .done, false)
        | argSS :: _ =>
          match tryConcrete argSS with
          | none => .inl (s, "getopts: symbolic argument")
          | some arg =>
            match arg.toList with
            | '-' :: c :: _ =>
              if optstring.toList.contains c then
                let s1 := checkedSetParam varname (symbolicStringOfString (String.ofList [c])) s
                let s2 := checkedSetParam "OPTIND" (symbolicStringOfString (Nat.repr (optind + 1))) s1
                .inr (exitWith 0 s2, .done, false)
              else
                let s1 := checkedSetParam varname (symbolicStringOfString "?") s
                let s2 := checkedSetParam "OPTIND" (symbolicStringOfString (Nat.repr (optind + 1))) s1
                .inr (exitWith 0 s2, .done, false)
            | _ =>
              let s' := checkedSetParam varname (symbolicStringOfString "?") s
              .inr (exitWith 1 s', .done, false)
    | _, _ => .inl (s, "getopts: symbolic arguments")
  | _ => .inl (s, "getopts: usage: getopts optstring name [arg]")

/-! # Hash builtin -/

def builtinHash (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let args := match argv with
    | [] => []
    | _ :: rest => rest
  match args with
  | [] =>
    -- List all hashed commands
    let s' := s.sh.hashes.foldl (fun os (name, (path, _hits)) =>
      writeStdout (name ++ "=" ++ path ++ "\n") os) s
    .inr (exitWith 0 s', .done, false)
  | arg :: _ =>
    match tryConcrete arg with
    | some "-r" =>
      -- Clear hash table
      .inr (exitWith 0 (clearHash s), .done, false)
    | some name =>
      -- Hash a specific command
      let (s', _mpath) := resolveCommandName s name
      .inr (exitWith 0 s', .done, false)
    | none => .inl (s, "hash: symbolic argument")

/-! # Jobs builtin -/

def builtinJobs (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let args := match argv with
    | [] => []
    | _ :: rest => rest
  let mode := match args.head?.bind tryConcrete with
    | some "-l" => JobsMode.jobsLong
    | some "-p" => .jobsTerse
    | _ => .jobsNormal
  let cp := curPrevJobs s.sh.jobs
  let s' := s.sh.jobs.foldl (fun os job =>
    writeStdout (stringOfJob mode cp job) os) s
  .inr (exitWith 0 s', .done, false)

/-! # Fg builtin -/

def builtinFg (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let job := match argv with
    | _ :: arg :: _ =>
      match tryConcrete arg with
      | some "%" =>
        match s.sh.jobs with | [] => none | j :: _ => some j
      | some n =>
        match readNat n.toList with
        | .ok pid => s.sh.jobs.find? (fun j => j.pid == pid)
        | .error _ => none
      | none => none
    | _ => s.sh.jobs.head?
  match job with
  | none => .inl (s, "fg: no current job")
  | some j =>
    let cp := curPrevJobs s.sh.jobs
    let s' := writeStdout (stringOfJob .jobsFGCommand cp j) s
    .inr (s', .wait j.pid .unchecked none .waitCommand, false)

/-! # Bg builtin -/

def builtinBg (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let job := match argv with
    | _ :: arg :: _ =>
      match tryConcrete arg with
      | some n =>
        match readNat n.toList with
        | .ok pid => s.sh.jobs.find? (fun j => j.pid == pid)
        | .error _ => none
      | none => none
    | _ => s.sh.jobs.head?
  match job with
  | none => .inl (s, "bg: no current job")
  | some j =>
    let cp := curPrevJobs s.sh.jobs
    let s' := writeStdout (stringOfJob .jobsBGCommand cp j) s
    let (s'', _) := OS.osSignalPid s' .SIGCONT j.pid false
    .inr (exitWith 0 s'', .done, false)

/-! # Kill builtin -/

def builtinKill (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let args := match argv with
    | [] => []
    | _ :: rest => rest
  -- Parse -SIGNAL or -s SIGNAL
  let (signal, targets) := match args with
    | sigArg :: rest =>
      match tryConcrete sigArg with
      | some str =>
        if str.startsWith "-" then
          let sigName := (str.drop 1).toString
          match Signal.ofString sigName with
          | some sig => (sig, rest)
          | none => (.SIGTERM, args)
        else if str == "-s" then
          match rest with
          | sigSS :: rest' =>
            match tryConcrete sigSS with
            | some sn =>
              match Signal.ofString sn with
              | some sig => (sig, rest')
              | none => (.SIGTERM, args)
            | none => (.SIGTERM, args)
          | _ => (.SIGTERM, args)
        else (.SIGTERM, args)
      | none => (.SIGTERM, args)
    | _ => (.SIGTERM, args)
  if targets.isEmpty then
    .inl (s, "kill: usage: kill [-s sigspec | -n signum | -sigspec] pid | jobspec ...")
  else
    let s' := targets.foldl (fun os tgt =>
      match tryConcrete tgt with
      | some pidStr =>
        match readNat pidStr.toList with
        | .ok pid =>
          let (os', _) := OS.osSignalPid os signal pid false
          os'
        | .error _ => os
      | none => os) s
    .inr (exitWith 0 s', .done, false)

/-! # Exec builtin -/

def builtinExec (s : OsState α) (argv : List SymbolicString) (env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  match argv with
  | [] | [_] =>
    -- No command: just apply redirects (handled by calling code)
    .inr (exitWith 0 s, .done, false)
  | _ :: cmdSS :: args =>
    match tryConcrete cmdSS with
    | none => .inl (s, "exec: symbolic argument")
    | some cmd =>
      let (s', mpath) := resolveCommandName s cmd
      match mpath with
      | none => .inr (failWithCode 127 ("exec: " ++ cmd ++ ": not found") s', .done, true)
      | some path =>
        .inr (s', .exec (symbolicStringOfString path) cmdSS (args.map id) env .noBinSh, false)

/-! # Command builtin -/

def builtinCommand (s : OsState α) (argv : List SymbolicString) (env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  match argv with
  | [] | [_] => .inr (exitWith 0 s, .done, false)
  | _ :: arg :: rest =>
    match tryConcrete arg with
    | none => .inl (s, "command: symbolic argument")
    | some "-v" =>
      -- command -v: show path
      match rest with
      | [] => .inr (exitWith 0 s, .done, false)
      | cmdSS :: _ =>
        match tryConcrete cmdSS with
        | none => .inl (s, "command -v: symbolic argument")
        | some cmdName =>
          -- Check builtins first
          if isBuiltin cmdName then
            .inr (exitWith 0 (writeStdout (cmdName ++ "\n") s), .done, false)
          else
            let (s', mpath) := resolveCommandName s cmdName
            match mpath with
            | none => .inr (exitWith 1 s', .done, false)
            | some path => .inr (exitWith 0 (writeStdout (path ++ "\n") s'), .done, false)
    | some cmdName =>
      -- Run command without function lookup, as simple command
      -- Dispatch as external command (skip function and builtin lookup)
      let (s', mpath) := resolveCommandName s cmdName
      match mpath with
      | none =>
        .inl (s', cmdName ++ ": command not found")
      | some path =>
        let cmdSS' := symbolicStringOfString cmdName
        let ss := symbolicStringOfString path
        .inr (s', .exec ss cmdSS' (rest.map id) env .tryBinSh, false)

/-! # Local builtin -/

def builtinLocal (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  match s.sh.locals with
  | [] => .inl (s, "local: not in a function")
  | frame :: frames =>
    let localArgs := match argv with
      | [] => []
      | _ :: argRest => argRest
    let newFrame := localArgs.foldl (fun f arg =>
      let (var, mval) := trySplitAssign arg
      (var, (mval, localOptsDefault)) :: f.filter (fun (n, _) => n != var)
    ) frame
    .inr (exitWith 0 { s with sh := { s.sh with locals := newFrame :: frames } }, .done, true)

/-! # History builtin (simplified) -/

def builtinHistory (s : OsState α) (_argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let (s', _) := s.sh.history.foldl (fun (os, i) (linno, _stmt) =>
    (writeStdout (s!"  {i+1}  {linno}\n") os, i + 1)) (s, 0)
  .inr (exitWith 0 s', .done, false)

/-! # Command dispatch -/

def lookupBuiltin (name : String) : Option (OsState α → List SymbolicString → Env →
    Sum (OsState α × String) (OsState α × Stmt × Bool)) :=
  match name with
  | ":" => some builtinColon
  | "true" => some builtinTrue
  | "false" => some builtinFalse
  | "break" => some builtinBreak
  | "continue" => some builtinContinue
  | "exit" => some builtinExit
  | "return" => some builtinReturn
  | "cd" => some builtinCd
  | "pwd" => some builtinPwd
  | "echo" => some builtinEcho
  | "export" => some builtinExport
  | "unset" => some builtinUnset
  | "set" => some builtinSet
  | "shift" => some builtinShift
  | "trap" => some builtinTrap
  | "readonly" => some builtinReadonly
  | "alias" => some builtinAlias
  | "unalias" => some builtinUnalias
  | "test" | "[" => some builtinTest
  | "type" => some builtinType
  | "umask" => some builtinUmask
  | "eval" => some builtinEval
  | "." | "source" => some builtinDot
  | "wait" => some builtinWait
  | "times" => some builtinTimes
  | "read" => some builtinRead
  | "printf" => some builtinPrintf
  | "getopts" => some builtinGetopts
  | "hash" => some builtinHash
  | "jobs" => some builtinJobs
  | "fg" => some builtinFg
  | "bg" => some builtinBg
  | "kill" => some builtinKill
  | "exec" => some builtinExec
  | "command" => some builtinCommand
  | "local" => some builtinLocal
  | "history" => some builtinHistory
  | _ => none

/-- Main run_command entry point -/
def runCommand (s : OsState α) (_opts : CommandOpts) (_check : CheckingMode) (cmdSS : SymbolicString)
    (args : Fields) (env : Env) (_savedFds : SavedFds) :
    EvaluationStep × OsState α × Stmt :=
  match tryConcrete cmdSS with
  | none => (.xsSimple "symbolic-command", s, .done)
  | some cmdName =>
    -- Check for function
    match s.sh.funcs.find? (fun (n, _) => n == cmdName) with
    | some (_, body) =>
      let outerLoopNest := s.sh.loopNest
      let outerParams := s.sh.positionalParams
      let newParams := cmdSS :: args.map (fun ss => ss)
      let s' := { s with sh := { s.sh with
        positionalParams := newParams,
        loopNest := 0,
        locals := [] :: s.sh.locals } }
      (.xsSimple "function-call", s', .call outerLoopNest outerParams cmdName body body)
    | none =>
      -- Check for builtin
      match lookupBuiltin cmdName with
      | some builtin =>
        let argv := cmdSS :: args.map id
        match builtin s argv env with
        | .inl (s', err) =>
          let s'' := failWith (cmdName ++ ": " ++ err) s'
          (.xsSimple "builtin-error", s'', .done)
        | .inr (s', cont, _isSpecial) =>
          (.xsSimple "builtin", s', cont)
      | none =>
        -- External command
        let (s', mpath) := resolveCommandName s cmdName
        match mpath with
        | none =>
          (.xsSimple "not-found", failWithCode 127 (cmdName ++ ": command not found") s', .done)
        | some path =>
          let ss := symbolicStringOfString path
          (.xsSimple "exec", s', .exec ss cmdSS (args.map id) env .tryBinSh)

end Commands
