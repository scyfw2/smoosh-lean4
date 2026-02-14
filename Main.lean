/-
  Main — Symbolic test runner for smoosh-lean
  Reads a shell script and runs it symbolically, printing stdout/stderr/ec.
-/
import Smoosh

/-! # Simple line-based shell parser -/

/-- Strip comments from a line (respecting quotes) -/
partial def stripComment (line : String) : String :=
  let rec go (chars : List Char) (inSQ inDQ : Bool) (acc : List Char) : String :=
    match chars with
    | [] => String.ofList acc.reverse
    | '#' :: _ =>
      if inSQ || inDQ then
        match chars with
        | _ :: rest => go rest inSQ inDQ ('#' :: acc)
        | _ => String.ofList acc.reverse -- unreachable
      else String.ofList acc.reverse
    | '\'' :: rest =>
      if inDQ then go rest inSQ inDQ ('\'' :: acc)
      else go rest (!inSQ) inDQ ('\'' :: acc)
    | '"' :: rest =>
      if inSQ then go rest inSQ inDQ ('"' :: acc)
      else go rest inSQ (!inDQ) ('"' :: acc)
    | '\\' :: c :: rest =>
      if inSQ then go (c :: rest) inSQ inDQ ('\\' :: acc)
      else go rest inSQ inDQ (c :: '\\' :: acc)
    | c :: rest => go rest inSQ inDQ (c :: acc)
  go line.toList false false []

/-- Simple tokenizer: split a command line into words -/
partial def tokenize (s : String) : List String :=
  let rec go (chars : List Char) (inSQ inDQ : Bool) (cur : List Char) (acc : List String) : List String :=
    match chars with
    | [] =>
      if cur.isEmpty then acc.reverse
      else (String.ofList cur.reverse :: acc).reverse
    | ' ' :: rest =>
      if inSQ || inDQ then go rest inSQ inDQ (' ' :: cur) acc
      else if cur.isEmpty then go rest false false [] acc
      else go rest false false [] (String.ofList cur.reverse :: acc)
    | '\t' :: rest =>
      if inSQ || inDQ then go rest inSQ inDQ ('\t' :: cur) acc
      else if cur.isEmpty then go rest false false [] acc
      else go rest false false [] (String.ofList cur.reverse :: acc)
    | '\'' :: rest =>
      if inDQ then go rest inSQ inDQ ('\'' :: cur) acc
      else go rest (!inSQ) inDQ cur acc
    | '"' :: rest =>
      if inSQ then go rest inSQ inDQ ('"' :: cur) acc
      else go rest inSQ (!inDQ) cur acc
    | '\\' :: c :: rest =>
      if inSQ then go (c :: rest) inSQ inDQ ('\\' :: cur) acc
      else go rest inSQ inDQ (c :: cur) acc
    | c :: rest => go rest inSQ inDQ (c :: cur) acc
  go s.toList false false [] []

/-! # Symbolic stepper -/

/-- Step evaluation with command dispatch — intercepts .exec results from stepEval
    and dispatches them through runCommand for builtin support -/
partial def fullStep (os : OsState Symbolic) (stmt : Stmt)
    : EvaluationStep × OsState Symbolic × Stmt :=
  match stmt with
  | .exec _cmdPath cmdName args env _binsh =>
    let opts : CommandOpts := { shouldFork := false, ranCmdSubst := false, forceSimpleCommand := false }
    runCommand os opts .unchecked cmdName (args.map id) env []
  | _ =>
    let (step, os', stmt') := stepEval os stmt
    -- If stepEval produced an .exec continuation, immediately dispatch it
    match stmt' with
    | .exec _cmdPath cmdName args env _binsh =>
      let opts : CommandOpts := { shouldFork := false, ranCmdSubst := false, forceSimpleCommand := false }
      let (step2, os'', stmt'') := runCommand os' opts .unchecked cmdName (args.map id) env []
      (step2, os'', stmt'')
    | _ => (step, os', stmt')

/-- Run the shell state machine to completion -/
partial def runToCompletion (os : OsState Symbolic) (stmt : Stmt) (maxSteps : Nat := 100000) : OsState Symbolic :=
  match maxSteps with
  | 0 => os
  | n + 1 =>
    match stmt with
    | .done => os
    | .exit_ => os
    | _ =>
      let (_, os', stmt') := fullStep os stmt
      runToCompletion os' stmt' n

/-- Convert a line of shell script into a Stmt -/
def lineToStmt (line : String) : Option Stmt :=
  let trimmed := line.trimAscii.toString
  if trimmed.isEmpty || trimmed.startsWith "#" then
    none
  else
    -- Simple command parsing: split by words
    let tokens := tokenize trimmed
    match tokens with
    | [] => none
    | _ =>
      let entries := tokens.map (fun t => Entry.s t)
      some (.command [] entries [] { shouldFork := true, ranCmdSubst := false, forceSimpleCommand := false })

/-- Parse a simple script from lines into a sequenced Stmt -/
def parseSimpleScript (lines : List String) : Stmt :=
  -- Join continuation lines and remove comments
  let processedLines := lines.map (fun l => (stripComment l).trimAscii.toString)
  let nonEmpty := processedLines.filter (fun l => !l.isEmpty && !l.startsWith "#")
  -- Convert each line to a Stmt
  let stmts := nonEmpty.filterMap lineToStmt
  -- Sequence them all
  match stmts with
  | [] => .done
  | s :: rest => rest.foldl (fun acc st => .semi acc st) s

/-! # Test runner -/

/-- Read stdout from symbolic OS -/
def getSymbolicStdout (os : OsState Symbolic) : String :=
  -- STDOUT is fifo 1
  match os.symbolic.fifos.drop 1 with
  | s :: _ => s
  | [] => ""

/-- Read stderr from symbolic OS -/
def getSymbolicStderr (os : OsState Symbolic) : String :=
  -- STDERR is fifo 2
  match os.symbolic.fifos.drop 2 with
  | s :: _ => s
  | [] => ""

/-- Run a single test -/
def runTest (testFile : String) : IO (String × String × Nat) := do
  let content ← IO.FS.readFile ⟨testFile⟩
  let lines := content.splitOn "\n"
  let stmt := parseSimpleScript lines
  let initOs := (OS.osInit (α := Symbolic) .noninteractive .toplevel)
  let finalOs := runToCompletion initOs stmt
  let stdout := getSymbolicStdout finalOs
  let stderr := getSymbolicStderr finalOs
  let ec := finalOs.sh.exitCode
  return (stdout, stderr, ec)

/-- Compare actual vs expected -/
def compareOutput (actual expected : String) : Bool :=
  actual.trimAscii.toString == expected.trimAscii.toString

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    IO.eprintln "Usage: smoosh-test <test-file> [--compare <expected-out>]"
    IO.eprintln "       smoosh-test --run-all <test-dir>"
    return 1

  | ["--run-all", testDir] =>
    -- Run all .test files in the directory
    let entries ← System.FilePath.readDir ⟨testDir⟩
    let testFiles := entries.toList.filter (fun e =>
      e.fileName.endsWith ".test")
    let mut passed := 0
    let mut failed := 0
    let mut errors := 0
    for entry in testFiles do
      let testPath := s!"{testDir}/{entry.fileName}"
      let baseName := (entry.fileName.dropEnd 5).toString  -- remove .test
      let outPath := s!"{testDir}/{baseName}.out"
      try
        let (stdout, _stderr, _ec) ← runTest testPath
        let hasExpected ← try
          let _ ← IO.FS.readFile ⟨outPath⟩
          pure true
        catch _ => pure false
        if hasExpected then
          let expected ← IO.FS.readFile ⟨outPath⟩
          if compareOutput stdout expected then
            passed := passed + 1
            IO.println s!"PASS: {baseName}"
          else
            failed := failed + 1
            IO.println s!"FAIL: {baseName}"
            IO.println s!"  Expected: {expected.trimAscii.toString.take 80}"
            IO.println s!"  Got:      {stdout.trimAscii.toString.take 80}"
        else
          IO.println s!"SKIP: {baseName} (no expected output)"
      catch e =>
        errors := errors + 1
        IO.println s!"ERROR: {baseName}: {e}"

    IO.println ""
    IO.println s!"Results: {passed} passed, {failed} failed, {errors} errors"
    return if failed > 0 then 1 else 0

  | [testFile] =>
    let (stdout, stderr, ec) ← runTest testFile
    unless stdout.isEmpty do
      IO.print stdout
    unless stderr.isEmpty do
      IO.eprint stderr
    return ec.toUInt32

  | [testFile, "--compare", expectedOut] =>
    let (stdout, _stderr, _ec) ← runTest testFile
    let expected ← IO.FS.readFile ⟨expectedOut⟩
    if compareOutput stdout expected then
      IO.println s!"PASS"
      return 0
    else
      IO.println s!"FAIL"
      IO.println s!"Expected:\n{expected}"
      IO.println s!"Got:\n{stdout}"
      return 1

  | _ =>
    IO.eprintln "Invalid arguments"
    return 1
