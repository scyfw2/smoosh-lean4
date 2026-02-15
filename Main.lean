/-
  Main — Symbolic test runner for smoosh-lean
  Reads a JSON AST (produced by OCaml dump_ast) and runs it symbolically, printing stdout/stderr/ec.
-/
import Smoosh
import Smoosh.FromJson

/-! # Symbolic stepper -/

/-- Run full_evaluation: step until Done (matching OCaml's full_evaluation) -/
partial def fullEvaluation (os : OsState Symbolic) (stmt : Stmt) (maxSteps : Nat := 500000) : OsState Symbolic :=
  match maxSteps with
  | 0 => os
  | n + 1 =>
    match stmt with
    | .done => os
    | _ =>
      -- OCaml: eval calls tick before stepping (clears stepped flags, decrements fuel)
      let os0 := OS.osTick os
      let (_step, os', stmt') := stepEval os0 stmt
      fullEvaluation os' stmt' n

/-- Run the shell to completion, matching OCaml's eval function:
    1. Run full_evaluation on the statement until Done
    2. Run full_evaluation on Exit to process exit traps -/
partial def runToCompletion (os : OsState Symbolic) (stmt : Stmt) (maxSteps : Nat := 500000) : OsState Symbolic :=
  let os1 := fullEvaluation os stmt maxSteps
  let os2 := fullEvaluation os1 .exit_ maxSteps
  os2

/-! # Test runner -/

/-- Read stdout from symbolic OS -/
def getSymbolicStdout (os : OsState Symbolic) : String :=
  -- STDOUT fd 1 → fifo 1
  match os.symbolic.fifos[1]? with
  | some s => s
  | none => ""

/-- Read stderr from symbolic OS -/
def getSymbolicStderr (os : OsState Symbolic) : String :=
  -- STDERR fd 2 → fifo 2
  match os.symbolic.fifos[2]? with
  | some s => s
  | none => ""

/-- Run a test from a JSON AST file -/
def runTestFromJson (jsonFile : String) : IO (String × String × Nat) := do
  let content ← IO.FS.readFile ⟨jsonFile⟩
  match Smoosh.FromJson.parseAst content with
  | some stmt =>
    let initOs := (OS.osInit (α := Symbolic) .noninteractive .toplevel)
    let finalOs := runToCompletion initOs stmt
    let stdout := getSymbolicStdout finalOs
    let stderr := getSymbolicStderr finalOs
    let ec := finalOs.sh.exitCode
    return (stdout, stderr, ec)
  | none =>
    IO.eprintln s!"Failed to parse JSON AST from {jsonFile}"
    return ("", "", 1)

/-- Compare actual vs expected (trim trailing whitespace) -/
def compareOutput (actual expected : String) : Bool :=
  actual.trimAsciiEnd.toString == expected.trimAsciiEnd.toString

/-- Check if a test uses builtin eval (requires re-parsing, must be skipped) -/
def isEvalTest (baseName : String) : Bool :=
  baseName.startsWith "builtin.eval" ||
  baseName.startsWith "semantics.eval"

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    IO.eprintln "Usage: smoosh-test <json-file>"
    IO.eprintln "       smoosh-test --run-all <json-dir> <test-dir>"
    return 1

  | ["--run-all", jsonDir, testDir] =>
    -- Run all .json files in the JSON AST directory, comparing against test dir
    let entries ← System.FilePath.readDir ⟨jsonDir⟩
    let jsonFiles := entries.toList.filter (fun e =>
      e.fileName.endsWith ".json")
    let sortedFiles := jsonFiles.mergeSort (fun a b => a.fileName < b.fileName)
    let mut passed := 0
    let mut failed := 0
    let mut errors := 0
    let mut skipped := 0
    let mut evalSkipped := 0
    let mut failedTests : Array String := #[]
    for entry in sortedFiles do
      let jsonPath := s!"{jsonDir}/{entry.fileName}"
      let baseName := (entry.fileName.dropEnd 5).toString  -- remove .json
      let outPath := s!"{testDir}/{baseName}.out"
      let ecPath := s!"{testDir}/{baseName}.ec"
      let errPath := s!"{testDir}/{baseName}.err"

      -- Skip eval tests (require re-parsing)
      if isEvalTest baseName then
        evalSkipped := evalSkipped + 1
        continue

      try
        let (stdout, stderr, ec) ← runTestFromJson jsonPath

        -- Read expected files
        let expectedOut ← try
          some <$> IO.FS.readFile ⟨outPath⟩
        catch _ => pure none

        let expectedEc ← try do
          let ecStr ← IO.FS.readFile ⟨ecPath⟩
          pure (ecStr.trimAscii.toString.toNat?)
        catch _ => pure none

        let _expectedErr ← try
          some <$> IO.FS.readFile ⟨errPath⟩
        catch _ => pure none

        -- If no expected output file, default expected is empty string
        let expOut := expectedOut.getD ""
        let expEc := expectedEc.getD 0  -- default exit code is 0

        let outMatch := compareOutput stdout expOut
        let ecMatch := ec == expEc

        if outMatch && ecMatch then
          passed := passed + 1
        else
          failed := failed + 1
          failedTests := failedTests.push baseName
          IO.println s!"FAIL: {baseName}"
          unless outMatch do
            IO.println s!"  stdout expected: {(expOut.take 200)}"
            IO.println s!"  stdout got:      {(stdout.take 200)}"
          unless ecMatch do
            IO.println s!"  ec expected: {expEc}, got: {ec}"
          unless stderr.isEmpty do
            IO.println s!"  stderr: {(stderr.take 200)}"
      catch e =>
        errors := errors + 1
        IO.println s!"ERROR: {baseName}: {e}"

    IO.println ""
    IO.println s!"Results: {passed} passed, {failed} failed, {errors} errors, {skipped} skipped, {evalSkipped} eval-skipped out of {sortedFiles.length}"
    if evalSkipped > 0 then
      IO.println s!"Note: {evalSkipped} tests skipped because they use builtin eval (requires re-parsing)"
    unless failedTests.isEmpty do
      IO.println s!"Failed tests: {failedTests.toList}"
    return if failed > 0 || errors > 0 then 1 else 0

  | [jsonFile] =>
    let (stdout, stderr, ec) ← runTestFromJson jsonFile
    unless stdout.isEmpty do
      IO.print stdout
    unless stderr.isEmpty do
      IO.eprint stderr
    return ec.toUInt32

  | [jsonFile, "--compare", expectedOut] =>
    let (stdout, _stderr, _ec) ← runTestFromJson jsonFile
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
