/-
  Smoosh.Command — Builtins, path resolution, command execution
  Translated from `command.lem` (2816 lines).

  Contains all shell builtin implementations (`echo`, `cd`, `export`, `trap`, `printf`, etc.),
  command name resolution (PATH lookup, special/regular builtins, functions),
  and the `runCommand` dispatch function. Also handles `getopts`, `fc`, and `set`.
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
def isShellKeyword (name : String) : Bool :=
  name ∈ ["!", "{", "}", "case", "do", "done", "elif", "else", "esac", "fi",
          "for", "if", "in", "then", "until", "while"]

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


/-- Strip leading "--" argument from argv (after command name) -/
def stripDoubleDash (argv : List SymbolicString) : List SymbolicString :=
  match argv with
  | dd :: rest =>
    match tryConcrete dd with
    | some "--" => rest
    | _ => argv
  | _ => argv

def builtinBreak (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let nonlexical := s.sh.opts.any (· == .nonlexicalctrl)
  let tryBreak (wantedN : Nat) :=
    -- Clamp to loop_nest unless nonlexicalctrl is set
    let n := if wantedN <= s.sh.loopNest || nonlexical then wantedN else s.sh.loopNest
    if n <= 0 then
      -- Outside any loop: silently succeed (POSIX: unspecified, smoosh returns Done)
      .inr (exitWith 0 s, Stmt.done, true)
    else
      .inr (exitWith 0 s, .break_ n, true)
  match stripDoubleDash (argv.drop 1) with
  | [] => tryBreak 1
  | [n] =>
    match tryConcrete n with
    | some ns =>
      match readNat ns.toList with
      | .ok 0 => .inl (s, ns ++ ": loop count out of range")
      | .ok n => tryBreak n
      | .error _ => .inl (s, ns ++ ": positive argument required")
    | none => .inl (s, "symbolic argument")
  | _ => .inl (s, "too many arguments")

def builtinContinue (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let nonlexical := s.sh.opts.any (· == .nonlexicalctrl)
  let tryContinue (wantedN : Nat) :=
    let n := if wantedN <= s.sh.loopNest || nonlexical then wantedN else s.sh.loopNest
    if n <= 0 then
      .inr (exitWith 0 s, Stmt.done, true)
    else
      .inr (exitWith 0 s, .continue_ n, true)
  match stripDoubleDash (argv.drop 1) with
  | [] => tryContinue 1
  | [n] =>
    match tryConcrete n with
    | some ns =>
      match readNat ns.toList with
      | .ok 0 => .inl (s, ns ++ ": loop count out of range")
      | .ok n => tryContinue n
      | .error _ => .inl (s, ns ++ ": positive numeric argument required")
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
  -- OCaml: do_cd step 7 — prepend PWD for relative paths
  let curpath := if dir.startsWith "/" then dir
                 else joinPath s.sh.cwd dir
  -- OCaml: do_cd step 8 — canonicalize the path
  let absDir := match canonicalizePath s curpath with
    | some p => p
    | none => curpath
  let old := s.sh.cwd
  let (s', err) := OS.osChdir s absDir
  match err with
  | none =>
    -- Set PWD and OLDPWD
    let s'' := match setParam "PWD" (symbolicStringOfString s'.sh.cwd) s' with
      | .inr os => os
      | .inl _ => s'
    let s''' := internalSetParam "OLDPWD" (symbolicStringOfString old) s''
    .inr (exitWith 0 s''', .done, true)
  | some msg => .inl (s', "cd: " ++ msg)

def builtinPwd (s : OsState α) (_argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let cwd := s.sh.cwd
  let s' := writeStdout (cwd ++ "\n") s
  .inr (exitWith 0 s', .done, true)

def builtinEcho (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let args := match argv with
    | [] => []
    | _ :: rest => rest
  -- Handle -n flag
  let (noNewline, printArgs) := match args with
    | first :: rest =>
      match tryConcrete first with
      | some "-n" => (true, rest)
      | _ => (false, args)
    | _ => (false, args)
  let strs := printArgs.map (fun ss => (tryConcrete ss).getD "")
  let msg := String.intercalate " " strs ++ (if noNewline then "" else "\n")
  let (s', ok) := tryWriteFd STDOUT msg s
  if ok then
    .inr (exitWith 0 s', .done, true)
  else
    .inr (exitWith 1 (writeStderr "echo: write error\n" s'), .done, true)

/-- Show variable list for export/readonly -p using collectVars output -/
def showVarlist' (s : OsState α) (cmd : String) (vars : List (String × Option SymbolicString)) : OsState α :=
  let sorted := vars.mergeSort (fun a b => a.1 < b.1)
  sorted.foldl (fun s (v, mv) =>
    let valStr := match mv with
      | some ss => "=" ++ quote' (stringOfSymbolicString ss)
      | none => ""
    let msg := cmd ++ " " ++ v ++ valStr ++ "\n"
    writeStdout msg s) s

/-- Update variable list for export/readonly -/
def updateVarlist (s : OsState α) (_cmd : String) (setter : OsState α → String → OsState α)
    (args : List SymbolicString) : Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let rec loop (os : OsState α) (args : List SymbolicString) :=
    match args with
    | [] => .inr (exitWith 0 os, .done, true)
    | arg :: args' =>
      match tryConcrete arg with
      | some astr =>
        let parts := splitStringOn false '=' astr
        match parts with
        | [name] => loop (setter os name) args'
        | name :: valParts =>
          let val := String.intercalate "=" valParts
          match setParam name (symbolicStringOfString val) os with
          | .inl err => .inl (os, err)
          | .inr os' => loop (setter os' name) args'
        | _ => loop os args'
      | none => loop os args'
  loop s args

def unsetFunction (name : String) (s : OsState α) : OsState α :=
  { s with sh := { s.sh with funcs := s.sh.funcs.filter (fun (n, _) => n != name) } }

partial def getOpts (allowed : List Char) (argv : List SymbolicString) :
    List Char × List SymbolicString :=
  match argv with
  | [] => ([], [])
  | arg :: rest =>
    match tryConcrete arg with
    | some s =>
      if s.startsWith "-" && s != "-" && s != "--" then
        let chars := s.toList.drop 1
        if chars.all (allowed.contains ·) then
          let (opts, args) := getOpts allowed rest
          (chars ++ opts, args)
        else
          ([], argv)
      else if s == "--" then
        ([], rest)
      else
        ([], argv)
    | none => ([], argv)

def builtinExport (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let s1 := exitWith 0 s
  let (opts, args) := getOpts ['p'] argv
  if opts.contains 'p' || args.isEmpty then
    let vars := exportedVars s1
    .inr (showVarlist' s1 "export" vars, .done, true)
  else
    updateVarlist s1 "export" setExported args

def builtinUnset (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let (opts, args) := getOpts ['f', 'v'] argv
  let unsetFuncs := opts.contains 'f'
  let unsetVars := opts.contains 'v' || !unsetFuncs

  let rec loop (os : OsState α) (ec : Nat) (args : List SymbolicString) :=
    match args with
    | [] => .inr (exitWith ec os, .done, true)
    | arg :: args' =>
      match tryConcrete arg with
      | some name =>
        let os1 := if unsetFuncs then unsetFunction name os else os
        if unsetVars then
          match unsetParam name os1 with
          | .ok os' => loop os' ec args'
          | .error err => .inl (os1, err)
        else
          loop os1 ec args'
      | none => .inl (os, "unset: symbolic argument")
  loop s 0 args

def builtinSet (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let s0 := exitWith 0 s
  match argv with
  | [] | [_] =>
    -- Print all variables (simplified)
    .inr (s0, .done, true)
  | _ :: args =>
    -- Check for -- (set positional params)
    let setPositionalParams (rest : List SymbolicString) : OsState α :=
      let prog := match s0.sh.positionalParams with
        | p :: _ => p
        | [] => symbolicStringOfString ""
      { s0 with sh := { s0.sh with positionalParams := prog :: rest } }
    -- Parse options using OCaml's set_getopts algorithm
    -- Processes: -o optname, +o optname, -chars (short opts), +chars (unset short opts), --, args
    let rec parseOpts (os : OsState α) (args : List SymbolicString) (setParams : Bool) :
        Sum (OsState α × String) (OsState α × Stmt × Bool) :=
      match args with
      | [] =>
        if setParams then
          .inr (setPositionalParams [] |> exitWith 0, .done, true)
        else
          .inr (os, .done, true)
      | arg :: rest =>
        match tryConcrete arg with
        | none => .inr (exitWith 0 (setPositionalParams args), .done, true)
        | some s =>
          match s.toList with
          | ['-', '-'] =>
            -- "--" means set positional params from rest
            .inr (exitWith 0 (setPositionalParams rest), .done, true)
          | ['-', 'o'] =>
            -- "-o" followed by optname: turn ON
            match rest with
            | [] => .inr (os, .done, true) -- "set -o" with nothing: print opts (simplified)
            | optName :: rest' =>
              match tryConcrete optName with
              | some name =>
                match ShOpt.ofLongopt name with
                | some opt => parseOpts (setShOpt os opt) rest' setParams
                | none => .inr (failWith s!"set: illegal option -o {name}" os, .done, true)
              | none => .inr (os, .done, true)
          | ['+', 'o'] =>
            -- "-o" followed by optname: turn OFF
            match rest with
            | [] => .inr (os, .done, true)
            | optName :: rest' =>
              match tryConcrete optName with
              | some name =>
                match ShOpt.ofLongopt name with
                | some opt => parseOpts (unsetShOpt os opt) rest' setParams
                | none => .inr (failWith s!"set: illegal option +o {name}" os, .done, true)
              | none => .inr (os, .done, true)
          | '-' :: opts =>
            -- Short options: -abc means set a, b, c
            let os' := opts.foldl (fun os' c =>
              match ShOpt.ofShortopt c with
              | some opt => setShOpt os' opt
              | none => os') os
            parseOpts os' rest setParams
          | '+' :: opts =>
            -- Unset short options: +abc means unset a, b, c
            let os' := opts.foldl (fun os' c =>
              match ShOpt.ofShortopt c with
              | some opt => unsetShOpt os' opt
              | none => os') os
            parseOpts os' rest setParams
          | _ =>
            -- Non-option arg: treat all remaining as positional params
            .inr (exitWith 0 (setPositionalParams (arg :: rest)), .done, true)
    parseOpts s0 args false

def builtinShift (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  match argv with
  | [] =>
    if s.sh.positionalParams.length < 1 then
      .inl (s, "shift: shift count must be <= $#")
    else
      let params' := s.sh.positionalParams.drop 1
      .inr (exitWith 0 { s with sh := { s.sh with positionalParams := params' } }, .done, true)
  | [arg] =>
    match tryConcrete arg with
    | some nStr =>
      match nStr.toNat? with
      | some n =>
        if n > s.sh.positionalParams.length then
          .inl (s, "shift: shift count must be <= $#")
        else
          let params' := s.sh.positionalParams.drop n
          .inr (exitWith 0 { s with sh := { s.sh with positionalParams := params' } }, .done, true)
      | none => .inl (s, "shift: numeric argument required")
    | none => .inl (s, "shift: symbolic argument")
  | _ => .inl (s, "shift: too many arguments")


def builtinTrap (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let args := match argv with
    | [] => []
    | _ :: rest => rest

  -- Parse flags
  let (printSignals, printTraps, args') := match args with
    | ss :: rest =>
      match tryConcrete ss with
      | some "-l" => (true, false, rest)
      | some "-p" => (false, true, rest)
      | _ => (false, false, args)
    | [] => (false, false, [])

  if printSignals then
    -- trap -l: list signals
    let s' := Signal.allSignals.foldl (fun os sig =>
      let name := sig.toString
      -- Attempt to match column format roughly (not strict)
      writeStdout (s!" {sig.platformInt}) {name}") os
    ) s
    let s'' := writeStdout "\n" s'
    .inr (exitWith 0 s'', .done, true)

  else if printTraps || args'.isEmpty then
    -- trap -p or just trap: print traps
    -- In a subshell, use parent's traps (supershellTraps) for display
    -- If args present, print specific signals
    let sigsToPrint :=
      if args'.isEmpty then Signal.allSignals
      else args'.filterMap (fun ss => tryConcrete ss >>= Signal.ofString)

    -- Use supershellTraps if available (in subshell), otherwise current traps
    let trapsToDisplay :=
      match s.sh.supershellTraps with
      | some superTraps => superTraps
      | none => s.sh.traps

    let s' := sigsToPrint.foldl (fun os sig =>
      match trapsToDisplay.find? (fun (S, _) => S == sig) with
      | some (_, handler) =>
        let hStr := match tryConcrete handler with | some h => h | none => ""
        writeStdout (s!"trap -- '{hStr}' {sig.toString}\n") os
      | none => os
    ) s
    .inr (exitWith 0 s', .done, true)

  else
    -- Set traps
    -- First arg is handler, rest are signals
    -- UNLESS first arg is a signal (implies reset) -- but standards say:
    -- trap action condition...
    -- If action is -, reset.
    -- If action is integer, it's a signal and we assume reset (if valid int/sig).
    -- Simplified logic matching smoosh semantics.lem somewhat:
    -- Clear supershell traps when modifying traps (matching OCaml behavior)
    let s := clearSupershellTraps s
    match args' with
    | [] => .inl (s, "trap: missing arguments")
    | handlerSS :: sigsSS =>
       let (handler, sigsSS') :=
         match tryConcrete handlerSS with
         | some "-" => (none, sigsSS) -- reset
         | some h =>
            -- Check if h is actually a signal?
            -- POSIX: check if first operand is a valid signal. If so, and multiple operands, do what?
            -- Smoosh OCaml logic: check if first arg is signal.
            match Signal.ofString h with
            | some _ => (none, handlerSS :: sigsSS) -- first arg was signal, implies reset
            | none =>
              -- Check if integer
              match h.toNat? with
              | some _ => (none, handlerSS :: sigsSS) -- numeric signal, reset
              | none => (some handlerSS, sigsSS) -- handler string
         | none => (some handlerSS, sigsSS) -- symbolic handler?? fallback to handler

       let s' := sigsSS'.foldl (fun os sigSS =>
         match tryConcrete sigSS with
         | some sn =>
           match Signal.ofString sn with
           | some sig => updateTrap sig handler os
           | none =>
              -- Try numeric signal
              -- (Symbolic mapping not fully implemented, simplify)
              os
         | none => os
       ) s
       .inr (exitWith 0 s', .done, true)


def builtinReadonly (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let s1 := exitWith 0 s
  let (opts, args) := getOpts ['p'] argv
  if opts.contains 'p' || args.isEmpty then
    let vars := readonlyVars s1
    .inr (showVarlist' s1 "readonly" vars, .done, true)
  else
    updateVarlist s1 "readonly" setReadonly args

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
        -- Split on first '=' to get name and value
        -- Use String.splitOn which preserves empty trailing parts
        -- Only treat as assignment if '=' is present
        if astr.contains '=' then
          match astr.splitOn "=" with
          | name :: valParts =>
            let val := String.intercalate "=" valParts
            { os with sh := { os.sh with aliases :=
              (name, val) :: os.sh.aliases.filter (fun (n, _) => n != name) } }
          | _ => os
        else os
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
      if isShellKeyword name then
        (writeStdout (name ++ " is a shell keyword\n") os, ec)
      else if isBuiltin name then
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




def builtinDot (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  -- argv[0] is the program name (. or source), argv[1:] are args
  -- Ref: command.lem:builtin_source — strips --, extracts filename, resolves via PATH
  let args := stripDoubleDash (argv.drop 1)
  match args with
  | [] => .inl (s, "filename argument required")
  | sfile :: _ =>
    match tryConcrete sfile with
    | none => .inl (s, "couldn't handle symbolic argument " ++ stringOfSymbolicString sfile)
    | some file =>
       -- Per POSIX: if file contains '/', search it directly; otherwise search PATH
       let mpath :=
         if file.toList.contains '/' then
           if OS.osFileExists s file then
             if OS.osIsReadable s file then Sum.inr file
             else Sum.inl "unreadable"
           else Sum.inl "not found"
         else
           match lookupConcreteParam s "PATH" with
           | none => Sum.inl "not found"
           | some pathvar =>
             let paths := splitStringOn true ':' pathvar
             match resolvePathWith (fun p => OS.osIsReadable s p) paths file with
             | none => Sum.inl "not found"
             | some path => Sum.inr path
      match mpath with
      | .inl msg => .inl (s, file ++ ": " ++ msg)
      | .inr path =>
        -- Read file content from the OS (real or symbolic filesystem)
        match OS.osReadFile s path with
        | some content =>
          -- Parse and execute the file content, like builtinEval does
          let stmt := Stmt.evalLoop 1 (none, none) (.parseString .parseDot content) .noninteractive .subsidiary
          .inr (s, stmt, true)
        | none =>
          .inl (s, file ++ ": cannot read file")

def builtinEval (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  -- Note: Lean's runCommand passes progName :: args for special builtins,
  -- so we need to skip argv[0] ("eval")
  let args := argv.drop 1
  if args.isEmpty then
    .inr (exitWith 0 s, .done, true)
  else
    -- Strip leading "--" if present (OCaml: strip_double_dash)
    let args' := match args with
      | arg :: rest => match tryConcrete arg with
        | some "--" => rest
        | _ => args
      | _ => args
    -- Join args with spaces to get the command string (OCaml: string_of_fields)
    let cmdStr := String.intercalate " " (args'.map stringOfSymbolicString)
    -- Create EvalLoop statement (OCaml: EvalLoop 1 (sstr, Just (stack_init ())) src Noninteractive Subsidiary)
    let stmt := Stmt.evalLoop 1 (none, none) (.parseString .parseEval cmdStr) .noninteractive .subsidiary
    .inr (s, stmt, true)


def builtinWait (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  match argv with
  | [] | [_] =>
    -- Wait for all children (OCaml: active_jobs + sequence of Wait)
    let activeJobs := s.sh.jobs.filter fun j =>
      match j.status with
      | .jobRunning => true
      | .jobStopped _ => true
      | _ => false

    let waits := activeJobs.map fun j =>
      Stmt.wait j.pid .unchecked none .waitCommand
    -- Sequence all waits, ending with skip to return 0
    let stmt := match waits with
      | [] => Stmt.done
      | ws => ws.foldr (fun w acc => Stmt.semi w acc) Stmt.done
    .inr (s, stmt, false)
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

/-- Process escape sequences in a string (for %b) -/
partial def printfProcessEscapes : List Char → List Char → List Char
  | [], acc => acc.reverse
  | '\\' :: 'n' :: rest, acc => printfProcessEscapes rest ('\n' :: acc)
  | '\\' :: 't' :: rest, acc => printfProcessEscapes rest ('\t' :: acc)
  | '\\' :: 'r' :: rest, acc => printfProcessEscapes rest ('\r' :: acc)
  | '\\' :: 'a' :: rest, acc => printfProcessEscapes rest ('\x07' :: acc)
  | '\\' :: 'b' :: rest, acc => printfProcessEscapes rest ('\x08' :: acc)
  | '\\' :: 'f' :: rest, acc => printfProcessEscapes rest ('\x0C' :: acc)
  | '\\' :: 'v' :: rest, acc => printfProcessEscapes rest ('\x0B' :: acc)
  | '\\' :: '\\' :: rest, acc => printfProcessEscapes rest ('\\' :: acc)
  | '\\' :: '0' :: rest, acc =>
    let (digits, rest') := rest.span (fun c => c >= '0' && c <= '7')
    let val := digits.foldl (fun n c => n * 8 + (c.toNat - '0'.toNat)) 0
    printfProcessEscapes rest' (Char.ofNat val :: acc)
  | c :: rest, acc => printfProcessEscapes rest (c :: acc)

/-- Apply format string once, consuming some arguments and returning remainder -/
partial def printfGoFmt : List Char → List String → List Char → String × List String
  | [], args, acc => (String.ofList acc.reverse, args)
  | '%' :: 's' :: rest, arg :: args', acc =>
    printfGoFmt rest args' (arg.toList.reverse ++ acc)
  | '%' :: 's' :: rest, [], acc =>
    printfGoFmt rest [] acc
  | '%' :: 'b' :: rest, arg :: args', acc =>
    let processed := printfProcessEscapes arg.toList []
    printfGoFmt rest args' (processed.reverse ++ acc)
  | '%' :: 'b' :: rest, [], acc =>
    printfGoFmt rest [] acc
  | '%' :: 'c' :: rest, arg :: args', acc =>
    match arg.toList with
    | c :: _ => printfGoFmt rest args' (c :: acc)
    | [] => printfGoFmt rest args' acc
  | '%' :: 'c' :: rest, [], acc =>
    printfGoFmt rest [] acc
  | '%' :: 'd' :: rest, arg :: args', acc =>
    printfGoFmt rest args' (arg.toList.reverse ++ acc)
  | '%' :: 'd' :: rest, [], acc =>
    printfGoFmt rest [] ('0' :: acc)
  | '%' :: '%' :: rest, args, acc =>
    printfGoFmt rest args ('%' :: acc)
  | '\\' :: 'n' :: rest, args, acc =>
    printfGoFmt rest args ('\n' :: acc)
  | '\\' :: 't' :: rest, args, acc =>
    printfGoFmt rest args ('\t' :: acc)
  | '\\' :: '\\' :: rest, args, acc =>
    printfGoFmt rest args ('\\' :: acc)
  | c :: rest, args, acc =>
    printfGoFmt rest args (c :: acc)

/-- Repeat format string while arguments remain -/
partial def printfRepeat (fmt : String) (args : List String) (acc : String) : String :=
  if args.isEmpty then
    let (result, _) := printfGoFmt fmt.toList [] []
    acc ++ result
  else
    let (result, remaining) := printfGoFmt fmt.toList args []
    let acc' := acc ++ result
    if remaining.isEmpty then acc'
    else printfRepeat fmt remaining acc'

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
      let result := printfRepeat fmt restStrs ""
      let s' := writeStdout result s
      .inr (exitWith 0 s', .done, true)


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
        .inr (exitWith 1 s', .done, true)
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
        if str == "-s" then
          match rest with
          | sigSS :: rest' =>
            match tryConcrete sigSS with
            | some sn =>
              match Signal.ofString sn with
              | some sig => (sig, rest')
              | none => (.SIGTERM, args)
            | none => (.SIGTERM, args)
          | _ => (.SIGTERM, args)
        else if str.startsWith "-" then
          let sigName := (str.drop 1).toString
          match Signal.ofString sigName with
          | some sig => (sig, rest)
          | none => (.SIGTERM, args)
        else (.SIGTERM, args)
      | none => (.SIGTERM, args)
    | _ => (.SIGTERM, args)
  if targets.isEmpty then
    .inl (s, "kill: usage: kill [-s sigspec | -n signum | -sigspec] pid | jobspec ...")
  else
    let (s', allOk) := targets.foldl (fun (os, ok) tgt =>
      match tryConcrete tgt with
      | some pidStr =>
        match readNat pidStr.toList with
        | .ok pid =>
          let (os', success) := OS.osSignalPid os signal pid false
          if success then (os', ok)
          else
            let os'' := writeStderr (s!"kill: ({pidStr}) - No such process\n") os'
            (os'', false)
        | .error _ =>
          let os' := writeStderr (s!"kill: {pidStr}: invalid signal specification\n") os
          (os', false)
      | none => (os, ok)) (s, true)
    .inr (exitWith (if allOk then 0 else 1) s', .done, false)

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
      -- Handle common builtins inline to avoid forward-reference issues
      match cmd with
      | "true" | ":" => .inr (exitWith 0 s, .exit_, false)
      | "false" => .inr (exitWith 1 s, .exit_, false)
      | _ =>
        -- External command
        let (s', mpath) := resolveCommandName s cmd
        match mpath with
        | none => .inr (failWithCode 127 ("exec: " ++ cmd ++ ": not found") s', .done, true)
        | some path =>
          .inr (s', .exec (symbolicStringOfString path) cmdSS (args.map id) env .tryBinSh, false)



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
          -- Check keywords first, then builtins, then path
          if isShellKeyword cmdName then
            .inr (exitWith 0 (writeStdout (cmdName ++ "\n") s), .done, false)
          else if isBuiltin cmdName then
            .inr (exitWith 0 (writeStdout (cmdName ++ "\n") s), .done, false)
          else
            let (s', mpath) := resolveCommandName s cmdName
            match mpath with
            | none => .inr (exitWith 1 s', .done, false)
            | some path => .inr (exitWith 0 (writeStdout (path ++ "\n") s'), .done, false)
    | some "-V" =>
      -- command -V: verbose description
      match rest with
      | [] => .inr (exitWith 0 s, .done, false)
      | cmdSS :: _ =>
        match tryConcrete cmdSS with
        | none => .inl (s, "command -V: symbolic argument")
        | some cmdName =>
          if isShellKeyword cmdName then
            .inr (exitWith 0 (writeStdout (cmdName ++ " is a shell keyword\n") s), .done, false)
          else if cmdName ∈ ["break", ":", "continue", ".", "eval", "exec", "exit",
                       "export", "readonly", "return", "set", "shift", "times",
                       "trap", "unset"] then
            .inr (exitWith 0 (writeStdout (cmdName ++ " is a special shell builtin\n") s), .done, false)
          else if isBuiltin cmdName then
            .inr (exitWith 0 (writeStdout (cmdName ++ " is a shell builtin\n") s), .done, false)
          else
            let (s', mpath) := resolveCommandName s cmdName
            match mpath with
            | none => .inr (exitWith 1 (writeStderr (cmdName ++ ": not found\n") s'), .done, false)
            | some path => .inr (exitWith 0 (writeStdout (cmdName ++ " is " ++ path ++ "\n") s'), .done, false)
    | some "-p" =>
      -- command -p: use default PATH — just dispatch normally for now
      match rest with
      | [] => .inr (exitWith 0 s, .done, false)
      | cmdSS :: rest' =>
        let assignsList := env.map id
        let opts' : CommandOpts := { shouldFork := false, ranCmdSubst := false, forceSimpleCommand := true }
        .inr (s, .commandReady assignsList cmdSS rest' [] opts', false)
    | some cmdName =>
      -- command <name>: run without function lookup, dispatching through CommandReady
      let cmdSS := symbolicStringOfString cmdName
      let assignsList := env.map id
      let opts' : CommandOpts := { shouldFork := false, ranCmdSubst := false, forceSimpleCommand := true }
      .inr (s, .commandReady assignsList cmdSS (rest.map id) [] opts', false)

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


def builtinMkdir (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let args := match argv with | [] => [] | _ :: rest => rest
  -- Parse -p flag
  let (mkdirP, paths) := match args with
    | flag :: rest => match tryConcrete flag with
      | some "-p" => (true, rest)
      | _ => (false, args)
    | _ => (false, args)
  let s' := paths.foldl (fun os arg =>
    match tryConcrete arg with
    | some path => (OS.osMkdir os path mkdirP).1
    | none => os) s
  .inr (exitWith 0 s', .done, false)

def builtinSleep (s : OsState α) (_argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  -- Stub: always succeed
  .inr (exitWith 0 s, .done, false)
def builtinTouch (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  match argv with
  | [] => .inl (s, "touch: missing operand")
  | _ :: args =>
    let s' := args.foldl (fun os arg =>
      match tryConcrete arg with
      | some path =>
        -- Create/touch the file by writing empty content through the OS
        -- This ensures the file appears in fsRoot for glob expansion
        let (os1, fdResult) := OS.osOpenFileForRedir os RedirType.to (symbolicStringOfString path)
        match fdResult with
        | .inr fd =>
          -- Write empty string to ensure file is created in fsRoot
          let os2 := match OS.osWriteFd os1 fd "" with
            | some os' => os'
            | none => os1
          OS.osCloseFd os2 fd
        | .inl _ => os1
      | none => os) s
    .inr (exitWith 0 s', .done, false)

def builtinChmod (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  -- Mock: just succeed
  .inr (s, .done, false)

def builtinLn (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  -- Mock: just succeed
  .inr (s, .done, false)

def builtinRm (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let args := match argv with | [] => [] | _ :: rest => rest
  -- Parse -r/-rf/-f flags
  let (recursive, paths) := args.foldl (fun (r, ps) arg =>
    match tryConcrete arg with
    | some "-r" | some "-rf" | some "-fr" => (true, ps)
    | some "-f" => (r, ps)
    | _ => (r, arg :: ps)) (false, [])
  let paths := paths.reverse
  let s' := paths.foldl (fun os arg =>
    match tryConcrete arg with
    | some path => (OS.osRmFile os path recursive).1
    | none => os) s
  .inr (exitWith 0 s', .done, false)

/-- Read all content from stdin and write to stdout, line by line,
    used by builtinCat when called without file arguments. -/
partial def catReadStdin (s : OsState α) : OsState α :=
  let (s1, (line, _rest, eof)) := OS.osReadLineFd s STDIN .escapeOff
  match eof with
  | .hitEof =>
    if line.isEmpty then s1
    else writeStdout line s1
  | .noEof =>
    let s2 := writeStdout (line ++ "\n") s1
    catReadStdin s2

def builtinCat (s : OsState α) (argv : List SymbolicString) (_env : Env) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  let args := match argv with | [] => [] | _ :: rest => rest
  if args.isEmpty then
    -- No file arguments: read stdin and write to stdout (like real cat)
    let s' := catReadStdin s
    .inr (exitWith 0 s', .done, false)
  else
    let (s'', failed) := args.foldl (fun (acc : OsState α × Bool) arg =>
      let (os, failed) := acc
      match tryConcrete arg with
      | some path =>
        match OS.osReadFile os path with
        | some content =>
          (writeStdout content os, failed)
        | none =>
          (writeStderr ("cat: " ++ path ++ ": No such file or directory\n") os, true)
      | none => (os, true)) (s, false)
    .inr (exitWith (if failed then 1 else 0) s'', .done, false)

/-- Lookup special builtins: . : break continue eval exec exit export local
    readonly return shift source set times trap unset
    These are run WITHOUT push/pop of local scope (env already applied in CommandReady).
    Return type: Sum (OsState × String) (OsState × Stmt × Bool)
    The Bool is the 'restore' flag (whether to restore redirects). -/
def lookupSpecialBuiltin (name : String) : Option (OsState α → List SymbolicString → Env → Sum (OsState α × String) (OsState α × Stmt × Bool)) :=
  match name with
  | "." | "source" => some builtinDot
  | ":" => some builtinColon
  | "break" => some builtinBreak
  | "continue" => some builtinContinue
  | "eval" => some builtinEval
  | "exec" => some builtinExec
  | "exit" => some builtinExit
  | "export" => some builtinExport
  | "local" => some builtinLocal
  | "readonly" => some builtinReadonly
  | "return" => some builtinReturn
  | "shift" => some builtinShift
  | "set" => some builtinSet
  | "times" => some builtinTimes
  | "trap" => some builtinTrap
  | "unset" => some builtinUnset
  | _ => none

/-- Lookup regular builtins: [ alias bg cd command echo false fc fg getopts
    hash help history jobs kill printf pwd read test true type ulimit umask
    unalias wait.
    These are run WITH push/pop of local scope.
    Return type: Sum (OsState × String) (OsState × Stmt)
    Note: no Bool restore flag — always restore for regular builtins. -/
def lookupRegularBuiltin (name : String) : Option (OsState α → List SymbolicString → Env → Sum (OsState α × String) (OsState α × Stmt)) :=
  -- Wrap the existing builtins that return (OsState × Stmt × Bool) to strip the Bool
  -- For now, regular builtins use the same implementations but we strip the Bool
  let wrap (f : OsState α → List SymbolicString → Env → Sum (OsState α × String) (OsState α × Stmt × Bool)) :
      OsState α → List SymbolicString → Env → Sum (OsState α × String) (OsState α × Stmt) :=
    fun s argv env => match f s argv env with
      | .inl err => .inl err
      | .inr (s', stmt, _) => .inr (s', stmt)
  match name with
  | "[" | "test" => some (wrap builtinTest)
  | "alias" => some (wrap builtinAlias)
  | "bg" => some (wrap builtinBg)
  | "cd" => some (wrap builtinCd)
  | "command" => some (wrap builtinCommand)
  | "echo" => some (wrap builtinEcho)
  | "false" => some (wrap builtinFalse)
  | "fg" => some (wrap builtinFg)
  | "getopts" => some (wrap builtinGetopts)
  | "hash" => some (wrap builtinHash)
  | "history" => some (wrap builtinHistory)
  | "jobs" => some (wrap builtinJobs)
  | "kill" => some (wrap builtinKill)
  | "printf" => some (wrap builtinPrintf)
  | "pwd" => some (wrap builtinPwd)
  | "read" => some (wrap builtinRead)
  | "true" => some (wrap builtinTrue)
  | "type" => some (wrap builtinType)
  | "umask" => some (wrap builtinUmask)
  | "unalias" => some (wrap builtinUnalias)
  | "wait" => some (wrap builtinWait)
  -- Non-standard builtins (for symbolic mode)
  | "touch" => some (wrap builtinTouch)
  | "mkdir" => some (wrap builtinMkdir)
  | "sleep" => some (wrap builtinSleep)
  | "chmod" => some (wrap builtinChmod)
  | "ln" => some (wrap builtinLn)
  | "rm" => some (wrap builtinRm)
  | "cat" => some (wrap builtinCat)
  | _ => none

/-- Combined lookup for isBuiltin checks -/
def lookupBuiltin (name : String) : Bool :=
  (lookupSpecialBuiltin (α := α) name).isSome || (lookupRegularBuiltin (α := α) name).isSome

/-- Main run_command entry point.
    Follows OCaml's 4-step dispatch:
    1. Special builtin lookup → run directly (no local scope)
    2. Function lookup (unless forceSimpleCommand) → pushLocals, setFunctionParams, return .call
    3. Regular builtin lookup → pushLocals, run, popLocals
    4. External command → checkExecve → fork/exec
    Returns: (EvaluationStep, OsState, Stmt, Bool)
    The Bool 'restore' flag indicates whether to restore redirects via pushredir. -/
def runCommand (s : OsState α) (opts : CommandOpts) (checked : CheckingMode) (progName : SymbolicString)
    (argv : Fields) (env : Env) (savedFds : SavedFds) :
    Sum (OsState α × String) (OsState α × Stmt × Bool) :=
  match tryConcrete progName with
  | none => .inl (s, "can't run symbolic command")
  | some prog =>
    -- Step 1: Special builtin lookup
    match lookupSpecialBuiltin prog with
    | some fn =>
      -- No local scope push for special builtins.
      -- Env was already applied in CommandReady.
      let fullArgv := progName :: argv
      fn s fullArgv env
    | none =>
      -- Step 2: Function lookup (unless forceSimpleCommand)
      match (opts.forceSimpleCommand, lookupFunction s prog) with
      | (false, some body) =>
        let s2 := pushLocals s env
        let s3 := setFunctionParams 0 argv s2
        .inr (s3, .call s.sh.loopNest (getFunctionParams s) prog body body, true)
      | _ =>
        -- Step 3: Regular builtin lookup
        match lookupRegularBuiltin prog with
        | some fn =>
          let s2 := pushLocals s env
          let fullArgv := progName :: argv
          match fn s2 fullArgv env with
          | .inl (s2', err) =>
            let (s3, _) := popLocals s2'
            .inl (s3, err)
          | .inr (s2', stmt1) =>
            -- Compute restore flag (false only for 'exec' without args special case)
            let restore := match stmt1 with
              | .commandReady _ cmd [] [] _ =>
                match tryConcrete cmd with
                | some "exec" => false
                | _ => true
              | _ => true
            let (s3, _) := popLocals s2'
            .inr (s3, stmt1, restore)
        | none =>
          -- Step 4: Alias lookup
          match s.sh.aliases.find? (fun (n, _) => n == prog) with
          | some (_, expansion) =>
            if expansion.isEmpty then
              -- Empty alias: no-op (e.g., alias empty='')
              .inr (exitWith 0 s, .done, true)
            else
              -- Non-empty alias: treat expansion as command
              -- Re-parse the expansion string and run it
              let stmt := parseTrapString expansion
              .inr (s, stmt, true)
          | none =>
          -- Step 5: External command
          let (s1, mpath) := resolveCommandName s prog
          match mpath with
          | none =>
            -- Command not found: write error and set exit code 127
            let s2 := writeStderr (prog ++ ": command not found\n") s1
            .inr (exitWith 127 s2, .done, true)
          | some executable =>
            let cmd1 := symbolicStringOfString executable
            let exported := getEnv s1
            let execEnv := env.foldl (fun acc (k, v) => (k, v) :: acc.filter (fun (k', _) => k' != k)) exported
            let exec := Stmt.exec cmd1 progName argv execEnv .tryBinSh
            if opts.shouldFork then
              let (s2, pid) := OS.osForkAndSubshell s1 exec .fg none true
              let stmtForJob := Stmt.commandExpRedirs [] (progName :: argv) ([], none, []) defaultCmdOpts
              let (s3, _) := addJob s2 [(pid, stmtForJob)] pid stmtForJob .fg .jobRunning
              .inr (s3, .wait pid checked none .waitInternal, true)
            else
              .inr (s1, exec, true)

instance [OS α] : Shell α where
  runCommand := runCommand
end Commands
