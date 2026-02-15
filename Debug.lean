import Smoosh
import Smoosh.FromJson

open Shell in
partial def traceRun (os : OsState Symbolic) (stmt : Stmt) (n : Nat := 10000) : IO (String × String × Nat) := do
  if n == 0 then
    IO.eprintln "OUT OF STEPS!"
    return ("", "", os.sh.exitCode)
  match stmt with
  | .done =>
    let stdout := match os.symbolic.fifos[1]? with
      | some s => s
      | none => ""
    let stderr := match os.symbolic.fifos[2]? with
      | some s => s
      | none => ""
    IO.eprintln s!"DONE ec={os.sh.exitCode}"
    return (stdout, stderr, os.sh.exitCode)
  | .exit_ =>
    -- Handle exit: run fullEvaluation on Exit to process exit traps
    let os' := Semantics.fullEvaluation os .exit_
    let stdout := match os'.symbolic.fifos[1]? with
      | some s => s
      | none => ""
    let stderr := match os'.symbolic.fifos[2]? with
      | some s => s
      | none => ""
    IO.eprintln s!"EXIT ec={os'.sh.exitCode}"
    return (stdout, stderr, os'.sh.exitCode)
  | _ =>
    let (_, os', stmt') := stepEval os stmt
    let stmtTag := match stmt' with
      | .done => "Done"
      | .exit_ => "Exit"
      | .semi .. => "Semi"
      | .and_ .. => "And"
      | .or_ .. => "Or"
      | .not_ .. => "Not"
      | .command .. => "Command"
      | .commandExpArgs .. => "CommandExpArgs"
      | .commandExpRedirs .. => "CommandExpRedirs"
      | .commandExpAssign .. => "CommandExpAssign"
      | .commandReady .. => "CommandReady"
      | .if_ .. => "If"
      | .whileCond .. => "WhileCond"
      | .whileRunning .. => "WhileRunning"
      | .while_ .. => "While"
      | .for_ .. => "For"
      | .forExpArgs .. => "ForExpArgs"
      | .forExpanded .. => "ForExpanded"
      | .forRunning .. => "ForRunning"
      | .case_ .. => "Case"
      | .pipe .. => "Pipe"
      | .background .. => "Background"
      | .wait .. => "Wait"
      | .subshell .. => "Subshell"
      | .defun .. => "Defun"
      | .call .. => "Call"
      | .redir .. => "Redir"
      | .pushredir .. => "Pushredir"
      | .checkedExit .. => "CheckedExit"
      | .trapped .. => "Trapped"
      | _ => "Other"
    IO.eprintln s!"  step → {stmtTag}"
    traceRun os' stmt' (n - 1)

def main (args : List String) : IO UInt32 := do
  let file := args.headD "/workspaces/smoosh/smoosh/tests/shell_json/semantics.assign.visible.json"
  let content ← IO.FS.readFile ⟨file⟩
  match Smoosh.FromJson.parseAst content with
  | some stmt =>
    IO.eprintln s!"Parsed OK"
    let initOs := (OS.osInit (α := Symbolic) .noninteractive .toplevel)
    let (stdout, stderr, ec) ← traceRun initOs stmt
    IO.println s!"stdout: [{stdout}]"
    IO.println s!"stderr: [{stderr}]"
    IO.println s!"ec: {ec}"
    return 0
  | none =>
    IO.eprintln "Parse failed"
    return 1
