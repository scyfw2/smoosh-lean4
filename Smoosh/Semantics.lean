/-
  Smoosh.Semantics — Expansion stepping, evaluation stepping, trap management
  Translated from semantics.lem (1679 lines)
-/
import Smoosh.Fields
import Smoosh.Arith

-- Many `step` variables are intentionally unused in the current simplified
-- implementation and will be wired in as the translation is completed.
set_option linter.unusedVariables false

/-! # Quoting mode -/

inductive QuotingMode where | quoted | unquoted
  deriving Repr, BEq

/-! # Trap management -/

class Shell (α : Type) [OS α] where
  runCommand : OsState α → CommandOpts → CheckingMode → SymbolicString → List SymbolicString → Env → List (Fd × Sum Fd Unit) → Sum (OsState α × String) (OsState α × Stmt × Bool)

section Semantics
variable {α : Type} [OS α] [Shell α]

/-- Check if a command name is a POSIX special builtin -/
private def isSpecialBuiltinName (name : String) : Bool :=
  name ∈ ["break", ":", "continue", ".", "eval", "exec", "exit",
           "export", "local", "readonly", "return", "set", "shift",
           "source", "times", "trap", "unset"]

/-- Check for pending signals and run trap handlers -/
partial def internalCheckTraps (step : EvaluationStep) (s : OsState α) (c : Stmt)
    : EvaluationStep × OsState α × Stmt :=
  match OS.osPendingSignal s with
  | (s1, none) => (step, s1, c)
  | (s1, some signal) =>
    match s1.sh.traps.find? (fun (sig, _) => sig == signal) with
    | none => internalCheckTraps step s1 c
    | some (_, handler) =>
      let ssHandler := handler
      match tryConcrete ssHandler with
      | none => internalCheckTraps step s1 c
      | some "" => internalCheckTraps step s1 c  -- ignore trap
      | some _ =>
        -- Parse and execute the handler, then continue with c
        let step' := .xsTrap signal "trap handler"
        let c' := .trapped signal s1.sh.exitCode
                    (.evalLoop 0 (none, none) (.parseString .parseTrap (String.join (ssHandler.filterMap (fun c => match c with | .c ch => some (String.ofList [ch]) | .q ch => some (String.ofList [ch]) | .sym _ => none)))) .noninteractive .subsidiary) c
        (step', s1, c')

/-- Check traps wrapper — matches OCaml check_traps: skips Exit -/
def checkTraps (res : EvaluationStep × OsState α × Stmt)
    : EvaluationStep × OsState α × Stmt :=
  match res with
  | (_, _, .exit_) => res  -- don't check traps on Exit
  | (step0, s0, c0) =>
    let s1 := logTrace .traps "checked traps" s0
    internalCheckTraps step0 s1 c0

/-! # Expansion stepping -/

-- StringMode for expansion (user vs generated)
inductive StringMode where | userString | generatedString
  deriving Repr, BEq

-- Quoting suppresses variable name shadowing warning
set_option linter.constructorNameAsVariable false

/-- Expand a parameter reference — translated from expand_param (semantics.lem:108-201) -/
def expandParam (s0 : OsState α) (split : SplittingMode) (q : QuotingMode) (str : String) (f : Format)
    : OsState α × ExpandedWords × Words :=
  -- Handle $* specially when quoted or unsplit
  let (s1, value) :=
    if str == "*" && (q == .quoted || !split.shouldSplit)
    then
      let sep := match lookupStringParam s0 "IFS" with
        | none => [SymbolicChar.c ' ']
        | some ss =>
          match ss with
          | [] => []
          | c :: _ => [c]
      (s0, some [symbolicStringOfFieldsSep sep (getFunctionParams s0)])
    else if str == "*" || str == "@"
    then
      -- Unquoted $* or $@: return positional params as fields
      let params := getFunctionParams s0
      if params.isEmpty then (s0, none)
      else (s0, some params)
    else
      (s0, (lookupParam s0 str).map (fun ss => [ss]))
  let cstr (sv : String) := (s1, [ExpandedWord.expS sv], ([] : Words))
  let ewfs (fs : Fields) :=
    if q == .quoted then
      (s1, fs.map (fun ss => ExpandedWord.dquo (ss.map fun | .c c => .q c | x => x)), ([] : Words))
    else
      (s1, expandedWordsOfFields fs, ([] : Words))
  let wrds (w : Words) := (s1, ([] : ExpandedWords), w)
  let null_ := (s1, ([] : ExpandedWords), ([] : Words))
  let ctrl (k : Control) := (s1, ([] : ExpandedWords), [Entry.k k])
  let unst (o : OsState α × ExpandedWords × Words) :=
    if str != "@" && str != "*" && s0.sh.opts.any (· == .nounset)
    then ctrl (.lerror str [.expS "parameter not set"] [])
    else o
  match value, f with
  -- NORMAL
  | none,    .normal     => unst null_
  | some fs, .normal     => ewfs fs
  -- DEFAULT
  | none,    .default_ w => wrds w
  | some fs, .default_ _ => ewfs fs
  | none,    .ndefault w => wrds w
  | some fs, .ndefault w =>
    match nullFields fs with
    | none       => (s1, expandedWordsOfFields fs, [])
    | some true  => wrds w
    | some false => ewfs fs
  -- ASSIGN
  | none,    .assign w  => ctrl (.lassign str [] w)
  | some fs, .assign _  => ewfs fs
  | none,    .nassign w => ctrl (.lassign str [] w)
  | some fs, .nassign w =>
    match nullFields fs with
    | none       => ewfs fs
    | some true  => ctrl (.lassign str [] w)
    | some false => ewfs fs
  -- ERROR
  | none,    .error w   => ctrl (.lerror str [] w)
  | some fs, .error _   => ewfs fs
  | none,    .nerror w  => ctrl (.lerror str [] w)
  | some fs, .nerror w  =>
    match nullFields fs with
    | none       => (s1, expandedWordsOfFields fs, [])
    | some true  => ctrl (.lerror str [] w)
    | some false => ewfs fs
  -- LENGTH
  | none,    .length_    => unst (cstr "0")
  | some fs, .length_    =>
    match tryConcretFieldsList fs with
    | none      => cstr "0"
    | some strs => cstr (Nat.repr (String.length (String.join strs)))
  -- ALT
  | none,    .alt _      => null_
  | some _,  .alt w      => wrds w
  | none,    .nalt _     => null_
  | some fs, .nalt w     =>
    match nullFields fs with
    | none       => (s1, ([] : ExpandedWords), w)
    | some true  => null_
    | some false => wrds w
  -- SUBSTRING (prefix/suffix matching)
  | none,    .substring _ _ _ => unst (cstr "")
  | some fs, .substring side mode w => ctrl (.lmatch fs side mode [] w)

/-- Try match and extract substring — stub for pattern matching -/
def tryMatchSubstring (lc : Locale) (side : SubstringSide) (mode : SubstringMode)
    (pat str : SymbolicString) : SymbolicString :=
  -- OCaml: parse the pattern, then try splitting the string at each position.
  -- For prefix removal (#/##): match pattern against str[0..n], keep str[n..].
  -- For suffix removal (%/%%): match pattern against str[n..], keep str[0..n].
  -- Shortest/longest is controlled by the order we try the split sizes.
  let parsedPat := parsePattern (pat.filter fun | .sym _ => false | _ => true)
  match parsedPat with
  | .error _ => str
  | .ok pattern1 =>
    let len := str.length
    let sizes := List.range (len + 1)  -- [0, 1, ..., len]
    let orderedSizes := match mode, side with
      | .shortest, .prefix_ => sizes           -- try smallest prefix first
      | .longest,  .suffix_ => sizes           -- try smallest kept portion first = largest suffix
      | .longest,  .prefix_ => sizes.reverse   -- try largest prefix first
      | .shortest, .suffix_ => sizes.reverse   -- try largest kept portion first = smallest suffix
    let rec tryLoop : List Nat → SymbolicString
      | [] => str  -- no match: return original
      | size :: rest =>
        let first := str.take size
        let restStr := str.drop size
        let (substr, keep) := match side with
          | .prefix_ => (first, restStr)
          | .suffix_ => (restStr, first)
        match matchExactPattern lc pattern1 substr with
        | .match_ _ => keep
        | .symbolic => str  -- can't concretize: return original
        | .noMatch => tryLoop rest
    tryLoop orderedSizes

-- Result types for expand_control / expand_words
-- Left = error:  (step, os, expanded_words)
-- Right = continue: (step, os, expanded_words, words)
abbrev ExpCtrlResult (α : Type) :=
  Sum (ExpansionStep × OsState α × ExpandedWords)
      (ExpansionStep × OsState α × ExpandedWords × Words)

instance : Nonempty (ExpCtrlResult α) := ⟨Sum.inl (.esStep "", sorry, [])⟩

def enterLoop (os : OsState α) : OsState α :=
  { os with sh := { os.sh with loopNest := os.sh.loopNest + 1 } }

def exitLoop (os : OsState α) : OsState α :=
  { os with sh := { os.sh with loopNest := os.sh.loopNest - 1 } }

mutual

/-- Expand a control node — translated from expand_control (semantics.lem:203-467) -/
partial def expandControl (stepFun : StepFun α) (s0 : OsState α) (split : SplittingMode) (q : QuotingMode) (k : Control)
    : ExpCtrlResult α :=
  match k with
  | .tilde pfx =>
    if pfx == ""
    then
      match lookupConcreteParam s0 "HOME" with
      | none => Sum.inr (.esTilde "", s0, [.expS "~"], [])
      | some dir => Sum.inr (.esTilde "", s0, [.dquo (symbolicStringOfString dir)], [])
    else
      match OS.osGetpwnam s0 pfx with
      | none => Sum.inr (.esTilde "", s0, [.expS ("~" ++ pfx)], [])
      | some path => Sum.inr (.esTilde "", s0, [.expS path], [])
  | .param str f =>
    if str == "@" && q == .quoted
    then
      let paramVars := getFunctionParams s0
      let buildAt (v : Fields) := Sum.inr (.esParam "expanding @", s0, [.at_ v], ([] : Words))
      match f with
      | .default_ _ => buildAt paramVars
      | .ndefault w =>
        if paramVars.isEmpty then expandWords stepFun s0 split q .generatedString [] w
        else buildAt paramVars
      | .assign _ => buildAt paramVars
      | .nassign _ =>
        if paramVars.isEmpty
        then expandWords stepFun s0 split q .generatedString [] [.k (.lerror "@" [.expS "bad variable name"] [])]
        else buildAt paramVars
      | .error _ => buildAt paramVars
      | .nerror w =>
        if paramVars.isEmpty
        then expandWords stepFun s0 split q .generatedString [] [.k (.lerror "@" [] w)]
        else buildAt paramVars
      | .length_ => expandWords stepFun s0 split q .generatedString [] [.k (.param "*" .length_)]
      | .alt w => expandWords stepFun s0 split q .generatedString [] w
      | .nalt w =>
        if paramVars.isEmpty then buildAt paramVars
        else expandWords stepFun s0 split q .generatedString [] w
      | .substring .prefix_ mode w =>
        match paramVars with
        | v1 :: vars =>
          let v1' := Entry.k (.quote [] [.k (.lmatch [v1] .prefix_ mode [] w)])
          expandWords stepFun s0 split q .generatedString [] (v1' :: wordsOfFields vars)
        | _ => buildAt []
      | .substring .suffix_ mode w =>
        match destInit paramVars with
        | some (vars', vn) =>
          let vn' := Entry.k (.quote [] [.k (.lmatch [vn] .suffix_ mode [] w)])
          expandWords stepFun s0 split q .generatedString [] (wordsOfFields vars' ++ [vn'])
        | none => buildAt []
      | _ => buildAt paramVars
    else
      let (s1, ew, w) := expandParam s0 split q str f
      expandWords stepFun s1 split q .generatedString ew w
  | .lassign str f [] =>
    match setParam str (concatExpanded f) s0 with
    | .inl err => Sum.inl (.esParam "bad or readonly variable", s0, .expS err :: f)
    | .inr s1 => Sum.inr (.esParam "finished assignment", s1, f, [])
  | .lassign str f w =>
    match expandWords stepFun s0 .noSplit q .generatedString [] w with
    | Sum.inr (step, s1, f1, w1) =>
      Sum.inr (.esNested (.esParam "assignment") step, s1, [], [.k (.lassign str (f ++ f1) w1)])
    | Sum.inl err => Sum.inl err
  | .lmatch str side mode f [] =>
    let sympat := symbolicStringOfExpandedWords true f
    let symstr := symbolicStringOfFields str
    let matched := tryMatchSubstring s0.sh.locale side mode sympat symstr
    Sum.inr (.esParam "finished match", s0, [], wordsOfSymbolicString matched)
  | .lmatch str side mode f w =>
    match expandWords stepFun s0 .noSplit .unquoted .generatedString [] w with
    | Sum.inr (step, s1, f1, w1) =>
      Sum.inr (.esNested (.esParam "match") step, s1, [], [.k (.lmatch str side mode (f ++ f1) w1)])
    | Sum.inl err => Sum.inl err
  | .lerror str f [] =>
    Sum.inl (.esParam "raising requested error", s0, .expS (str ++ ": ") :: f)
  | .lerror str f w =>
    match expandWords stepFun s0 .noSplit q .generatedString [] w with
    | Sum.inr (step, s1, f1, w1) =>
      Sum.inr (.esNested (.esParam "error") step, s1, [], [.k (.lerror str (f ++ f1) w1)])
    | Sum.inl err => Sum.inl err
  | .backtick c =>
    -- Command substitution: create a pipe, fork subshell with stdout → pipe
    match OS.osPipe s0 with
    | .inl err =>
      Sum.inl (.esCommand s!"failed to set up pipe: {err}", s0, [])
    | .inr (s1, fdRead, fdWrite) =>
      let redirs : List ExpandedRedir := [.erDup .toFD .closeOrig STDOUT (some fdWrite),
                                           .erDup .toFD .closeOrig fdRead none]
      match doRedirs s1 redirs with
      | (s2, .inl _) =>
        Sum.inl (.esCommand "failed to set up subshell", s2, [])
      | (s2, .inr savedFds) =>
        let (s3, pid) := OS.osForkAndSubshell s2 c .fg none false
        let s4 := restoreFds s3 savedFds
        let s5 := closeFd s4 fdWrite
        Sum.inr (.esCommand "initializing subshell", s5, [],
                 [.k (.lbacktick c pid fdRead)])
  | .lbacktick corig pid fdRead =>
    match OS.osReadAllFd stepFun s0 fdRead with
    | (s1, .inl step) =>
      Sum.inr (.esEval (.esCommand s!"process with pid {pid} stepped") step,
               s1, [], [.k (.lbacktick corig pid fdRead)])
    | (s1, .inr none) =>
      Sum.inl (.esCommand "broken pipe", s1, [])
    | (s1, .inr (some str)) =>
      let s2 := closeFd s1 fdRead
      let sTrimmed := trimrNewlines str
      Sum.inr (.esCommand "command exited successfully, waiting",
               s2, [], [.k (.lbacktickWait corig pid sTrimmed)])
  | .lbacktickWait _corig pid sOut =>
    match waitForPid stepFun s0 pid with
    | (s1, none) =>
      Sum.inr (.esCommand "command process vanished", s1, [.expS sOut], [])
    | (s1, some (.inl step)) =>
      Sum.inr (.esEval (.esCommand "command process stepped") step,
               s1, [], [.k (.lbacktickWait _corig pid sOut)])
    | (s1, some (.inr code)) =>
      Sum.inr (.esCommand "command process terminated",
               exitWith code s1, [.expS sOut], [])
  | .arith f [] =>
    -- Simplified arithmetic: parse and evaluate
    let arithStr := String.join (f.filterMap (fun ew => match ew with | .expS s => some s | .usrS s => some s | _ => none))
    match parseArith arithStr with
    | .error e => Sum.inl (.esArith ("arithmetic error: " ++ e), s0, [.expS "0"])
    | .ok e =>
      let get (st : OsState α) (n : String) : Int :=
        match lookupStringParam st n with
        | none => 0
        | some ss =>
          match tryConcrete ss with
          | some s => match readSignedInteger 10 s.toList with | .ok i => i | .error _ => 0
          | none => 0
      let set (st : OsState α) (n : String) (v : Int) : Except String (OsState α) :=
        match setParam n (symbolicStringOfString (toString v)) st with
        | .inl err => .error err
        | .inr st' => Except.ok st'

      match evalArith get set e s0 with
      | Except.ok (res, s1) => Sum.inr (.esArith "computed arithmetic result", s1, [.expS (toString res)], [])
      | Except.error msg => Sum.inl (.esArith ("arithmetic evaluation error: " ++ msg), s0, [.expS "0"])
  | .arith f w =>
    match expandWords stepFun s0 split q .generatedString [] w with
    | Sum.inr (step, s1, f1, w1) =>
      Sum.inr (.esNested (.esArith "before arithmetic parsing") step, s1, [], [.k (.arith (f ++ f1) w1)])
    | Sum.inl err => Sum.inl err
  | .quote f [] =>
    Sum.inr (.esQuote "finished quote expansion", s0, collapseQuoted f, [])
  | .quote f w =>
    match expandWords stepFun s0 split .quoted .generatedString [] w with
    | Sum.inr (step, s1, [], w1) =>
      Sum.inr (step, s1, [], [.k (.quote (f ++ [.dquo []]) w1)])
    | Sum.inr (step, s1, f1, w1) =>
      Sum.inr (step, s1, [], [.k (.quote (f ++ f1) w1)])
    | Sum.inl err => Sum.inl err
  | .escape c =>
    Sum.inr (.esEscape "", s0, [.dquo [.q c]], [])

/-- Expand a word list — translated from expand_words (semantics.lem:469-487) -/
partial def expandWords (stepFun : StepFun α) (s0 : OsState α) (split : SplittingMode) (q : QuotingMode) (sm : StringMode)
    (f : ExpandedWords) : Words → ExpCtrlResult α
  | [] => Sum.inr (.esStep "done", s0, f, [])
  | .f :: ws => Sum.inr (.esStep "user field separator", s0, f ++ [.usrF], ws)
  | .s "" :: ws => expandWords stepFun s0 split q sm f ws
  | .s str :: ws =>
    let f1 := match q, sm with
      | .quoted, _ => [ExpandedWord.dquo (quotedSymbolicStringOfString str)]
      | .unquoted, .userString => [.usrS str]
      | .unquoted, .generatedString => [.expS str]
    Sum.inr (.esStep "plain string", s0, f ++ f1, ws)
  | .k k :: ws =>
    match expandControl stepFun s0 split q k with
    | Sum.inr (step, s1, f1, w1) => Sum.inr (step, s1, f ++ f1, w1 ++ ws)
    | Sum.inl err => Sum.inl err
  | .esym sym :: ws =>
    Sum.inr (.esStep "skipping symbolic result", s0, f ++ [.ewSym sym], ws)

end

/-- Step expansion state machine — translated from step_expansion (semantics.lem:515-541) -/
def stepExpansion (stepFun : StepFun α) (s : OsState α) : ExpansionState →
    ExpansionStep × OsState α × ExpansionState
  | .expStart opts w =>
    match expandWords stepFun s opts.splitting .unquoted .userString [] w with
    | Sum.inr (step, s1, f1, w1) => (step, s1, .expExpand opts f1 w1)
    | Sum.inl (step, s1, f1) => (step, s1, .expError (fieldsOfExpandedWords f1))
  | .expExpand opts f0 [] =>
    if opts.splitting.shouldSplit
    then (.esSplit "starting field splitting", s, .expSplit opts f0)
    else (.esSplit "skipping field splitting", s, .expPath opts (skipFieldSplitting f0))
  | .expExpand opts f0 w0 =>
    match expandWords stepFun s opts.splitting .unquoted .userString f0 w0 with
    | Sum.inr (step, s1, f1, w1) => (step, s1, .expExpand opts f1 w1)
    | Sum.inl (step, s1, f1) => (step, s1, .expError (fieldsOfExpandedWords f1))
  | .expSplit opts f0 =>
    (.esSplit "", s, .expPath opts (fieldSplitting s f0))
  | .expPath opts ifs0 =>
    if s.sh.opts.any (· == .noglob) || !opts.globbing
    then (.esPath "skipping pathname expansion", s,
          .expQuote opts (unescapeIntermediateFields ifs0))
    else (.esPath "", s, .expQuote opts (pathnameExpansion s ifs0))
  | .expQuote _opts ifs0 =>
    (.esQuote "", s, .expDone (quoteRemoval ifs0))
  | .expError fs => (.esStep "done in error state", s, .expError fs)
  | .expDone fs => (.esStep "done in success state", s, .expDone fs)




/-! # Redirect stepping -/

inductive RedirExpResult (α : Type) where
  | redirExpStep (step : ExpansionStep) (os : α) (er : ExpandingRedir)
  | redirExpDone (os : α) (er : ExpandedRedir)
  | redirExpError (msg : String)

def stepRedir (stepFun : StepFun α) (s : OsState α) : ExpandingRedir → RedirExpResult (OsState α)
  | .xrFile ty fd es =>
    let (step, s', es') := stepExpansion stepFun s es
    match es' with
    | .expDone fs =>
      match fs with
      | [ss] => .redirExpDone s' (.erFile ty fd ss)
      | _ => .redirExpError "ambiguous redirect"
    | _ => .redirExpStep step s' (.xrFile ty fd es')
  | .xrDup ty fd es =>
    let (step, s', es') := stepExpansion stepFun s es
    match es' with
    | .expDone fs =>
      match fs with
      | [ss] =>
        match tryConcrete ss with
        | some "-" => .redirExpDone s' (.erDup ty .closeOrig fd none)
        | some s =>
          match readNat s.toList with
          | .ok n => .redirExpDone s' (.erDup ty .leaveOrig fd (some n))
          | .error _ => .redirExpError s!"bad file descriptor: {s}"
        | none => .redirExpError "symbolic fd target"
      | _ => .redirExpError "ambiguous redirect"
    | _ => .redirExpStep step s' (.xrDup ty fd es')
  | .xrHeredoc ty fd es =>
    let (step, s', es') := stepExpansion stepFun s es
    match es' with
    | .expDone fs =>
      let ss := fs.flatMap id
      .redirExpDone s' (.erHeredoc ty fd ss)
    | _ => .redirExpStep step s' (.xrHeredoc ty fd es')

/-! # Evaluation stepping -/

/-- Handle expansion errors — translated from expansion_error (semantics.ml:89-95) -/
def expansionError (mayExit : Bool) (s0 : OsState α) (evalStep : EvaluationStep) (expStep : ExpansionStep) (err : Fields)
    : EvaluationStep × OsState α × Stmt :=
  let msg := stringOfSymbolicString (symbolicStringOfFields err)
  let s1 := failWith msg s0
  internalCheckTraps (.xsExpand evalStep expStep) s1
    (if mayExit && isInteractive s1 then .done else .exit_)

/-- Main evaluation stepper — this is the heart of the semantics -/
instance : Nonempty (EvaluationStep × OsState α × Stmt) := ⟨sorry⟩
/-- Minimal shell string parser for trap handlers and eval strings.
    Splits by ';' for semicolons, then by whitespace for words.
    Handles simple commands like "echo bye; echo foo". -/
def isValidVarNameChar (c : Char) : Bool :=
  c.isAlpha || c.isDigit || c == '_'

def isAssignment (w : String) : Option (String × String) :=
  match w.splitOn "=" with
  | [name, value] =>
    if name.isEmpty then none
    else if name.all isValidVarNameChar && (name.front.isAlpha || name.front == '_')
    then some (name, value)
    else none
  | name :: value :: rest =>
    -- handle VAR=val=ue (value can contain =)
    if name.isEmpty then none
    else if name.all isValidVarNameChar && (name.front.isAlpha || name.front == '_')
    then some (name, "=".intercalate (value :: rest))
    else none
  | _ => none

-- Parse a word that may contain $VAR, $?, $#, $$ references
-- Returns a list of Entry (Words elements)
private partial def parseTrapWordGo (cs : List Char) (acc : String) (result : Words) : Words :=
  match cs with
  | [] =>
    if acc.isEmpty then result
    else result ++ [.s acc]
  | '$' :: '?' :: rest =>
    let r := if acc.isEmpty then result else result ++ [.s acc]
    parseTrapWordGo rest "" (r ++ [.k (.param "?" (.default_ []))])
  | '$' :: '#' :: rest =>
    let r := if acc.isEmpty then result else result ++ [.s acc]
    parseTrapWordGo rest "" (r ++ [.k (.param "#" (.default_ []))])
  | '$' :: '$' :: rest =>
    let r := if acc.isEmpty then result else result ++ [.s acc]
    parseTrapWordGo rest "" (r ++ [.k (.param "$" (.default_ []))])
  | '$' :: c :: rest =>
    if c.isDigit then
      let r := if acc.isEmpty then result else result ++ [.s acc]
      parseTrapWordGo rest "" (r ++ [.k (.param (String.ofList [c]) (.default_ []))])
    else if c.isAlpha || c == '_' then
      -- Read variable name
      let (varChars, remaining) := rest.span (fun ch => ch.isAlpha || ch.isDigit || ch == '_')
      let varName := String.ofList (c :: varChars)
      let r := if acc.isEmpty then result else result ++ [.s acc]
      parseTrapWordGo remaining "" (r ++ [.k (.param varName (.default_ []))])
    else
      parseTrapWordGo (c :: rest) (acc ++ "$") result
  | c :: rest =>
    parseTrapWordGo rest (acc.push c) result

def parseTrapWord (w : String) : Words :=
  parseTrapWordGo w.toList "" []

-- Parse a list of words into a Stmt.command
private def parseTrapCommandWords (trimmed : String) : Stmt :=
  let words := trimmed.splitOn " " |>.filter (· != "")
  match words with
  | [] => .done
  | [single] =>
    match isAssignment single with
    | some (name, value) =>
      let rhs : Words := if value.isEmpty then [] else [.s value]
      Stmt.command [(name, rhs)] [] [] defaultCmdOpts
    | none =>
      let entries := parseTrapWord single
      Stmt.command [] entries [] defaultCmdOpts
  | _ =>
    -- Check for leading assignments
    let (assigns, cmdWords) := words.span (fun w => isAssignment w |>.isSome)
    if !assigns.isEmpty then
      let assignList : List (String × Words) := assigns.filterMap fun w =>
        match isAssignment w with
        | some (name, value) =>
          some (name, if value.isEmpty then [] else [.s value])
        | none => none
      if cmdWords.isEmpty then
        Stmt.command assignList [] [] defaultCmdOpts
      else
        let cmdEntries : Words := cmdWords.foldl (fun acc w =>
          let wordEntries := parseTrapWord w
          match acc with
          | [] => wordEntries
          | _ => acc ++ [.f] ++ wordEntries) []
        Stmt.command assignList cmdEntries [] defaultCmdOpts
    else
      -- Build entries with F separators, handling $var in each
      let entries : Words := words.foldl (fun acc w =>
        let wordEntries := parseTrapWord w
        match acc with
        | [] => wordEntries
        | _ => acc ++ [.f] ++ wordEntries) []
      Stmt.command [] entries [] defaultCmdOpts

-- Parse a simple command string (no ; && ||)
-- Handles subshell (cmd) and negation ! cmd (one level deep)
def parseTrapSimpleCmd (s : String) : Stmt :=
  let trimmed := s.trimAscii.toString
  if trimmed.isEmpty then .done
  -- Check for subshell: (cmd)
  else if trimmed.front == '(' && trimmed.back == ')' then
    let inner := ((trimmed.drop 1).dropEnd 1).toString
    .subshell (parseTrapCommandWords inner) ([], none, [])
  -- Check for negation: ! cmd
  else if trimmed.startsWith "! " then
    let rest := (trimmed.drop 2).trimAscii.toString
    .not_ (parseTrapCommandWords rest)
  else
    parseTrapCommandWords trimmed

def parseTrapString (s : String) : Stmt :=
  -- Split by ';' to get individual statement groups
  let semiParts := s.splitOn ";"
  let stmts := semiParts.filterMap fun part =>
    let trimmed := part.trimAscii.toString
    if trimmed.isEmpty then none
    else
      -- Split by '&&' and '||' to get And/Or chains
      -- Check for &&
      match trimmed.splitOn " && " with
      | [single] =>
        -- No &&, check for ||
        match single.splitOn " || " with
        | [single2] => some (parseTrapSimpleCmd single2)
        | first :: rest =>
          let firstStmt := parseTrapSimpleCmd first
          some (rest.foldl (fun acc part => .or_ acc (parseTrapSimpleCmd part)) firstStmt)
        | [] => some .done
      | first :: rest =>
        let firstStmt := parseTrapSimpleCmd first
        some (rest.foldl (fun acc part =>
          -- Each part after && may contain ||
          match part.splitOn " || " with
          | [single2] => .and_ acc (parseTrapSimpleCmd single2)
          | first2 :: rest2 =>
            let andRight := parseTrapSimpleCmd first2
            let orChain := rest2.foldl (fun a p => .or_ a (parseTrapSimpleCmd p)) andRight
            .and_ acc orChain
          | [] => acc) firstStmt)
      | [] => some .done
  -- Join with Semi
  match stmts with
  | [] => .done
  | [c] => c
  | c :: rest => rest.foldl (fun acc s => .semi acc s) c

partial def stepEval (s : OsState α) (c : Stmt) (checked : CheckingMode := .unchecked)
    : EvaluationStep × OsState α × Stmt :=
  match c with
  | .done => checkTraps (.xsSimple "done", s, .done)

  -- Command with args to expand
  | .command assigns args redirs opts =>
    let es := ExpansionState.expStart
      { splitting := .split, globbing := true }
      args
    (.xsSimple "command-expand-args", s, .commandExpArgs assigns es redirs opts)

  -- Expanding args
  | .commandExpArgs assigns es redirs opts =>
    let (step, s', es') := stepExpansion (stepEval' s) s es
    match es' with
    | .expDone fs =>
      let rs := ([], none, redirs)
      (.xsExpand (.xsSimple "args fully expanded") step, s', .commandExpRedirs assigns fs rs opts)
    | .expError err =>
      expansionError true s' (.xsSimple "arg expansion") step err
    | _ =>
      (.xsExpand (.xsSimple "argument expansion step") step, s', .commandExpArgs assigns es' redirs opts)

  -- Expanding redirects
  -- First, handle the case where a redirect is currently being expanded (mxr = some xr).
  -- This MUST come before the (ers, mxr, r :: rs) pattern to avoid discarding in-progress expansions.
  | .commandExpRedirs assigns fs (ers, some xr, rs) opts =>
    match stepRedir (stepEval' s) s xr with
    | .redirExpDone s' er =>
      (.xsRedir "expanding", s', .commandExpRedirs assigns fs (ers ++ [er], none, rs) opts)
    | .redirExpStep step s' xr' =>
      let opts' := { opts with ranCmdSubst := opts.ranCmdSubst || ranCommandSubstitution step }
      ((.xsExpand (.xsRedir "redirect") step), s', .commandExpRedirs assigns fs (ers, some xr', rs) opts')
    | .redirExpError msg =>
      -- Match OCaml: check if command is special builtin for error handling
      let (s2, mayExit) := match fs with
        | sProg :: _ =>
          let (s2, _, prog) := concretize s sProg
          (s2, isSpecialBuiltinName prog)
        | _ => (s, false)
      expansionError mayExit s2 (.xsSimple "error in redirect expansion") (.esStep "") [symbolicStringOfString msg]
  -- Start expanding a new redirect from the remaining list
  | .commandExpRedirs assigns fs (ers, none, r :: rs) opts =>
    let xr := match r with
      | .rfile ty fd w => ExpandingRedir.xrFile ty fd (.expStart { splitting := .noSplit, globbing := false } w)
      | .rdup ty fd w => ExpandingRedir.xrDup ty fd (.expStart { splitting := .noSplit, globbing := false } w)
      | .rheredoc ty fd w => ExpandingRedir.xrHeredoc ty fd (.expStart { splitting := .noSplit, globbing := false } w)
    (.xsRedir "starting", s, .commandExpRedirs assigns fs (ers, some xr, rs) opts)
  -- All redirects fully expanded and no more to process
  | .commandExpRedirs assigns fs (ers, none, []) opts =>
    -- All redirects expanded — match OCaml semantics.ml:716-753
    -- Determine if command is a special builtin (for error handling)
    let (s1, progSpecial) := match fs with
      | sProg :: _ =>
        let (s1, _, progName) := concretize s sProg
        (s1, isSpecialBuiltinName progName)
      | _ => (s, false)
    let catchingErrors := s1.sh.opts.any (· == .errexit)
    let exitOnError := catchingErrors ||
      (progSpecial && !opts.forceSimpleCommand && !isInteractive s1)
    match doRedirs s1 ers with
    | (s2, .inl msg) =>
      internalCheckTraps (.xsSimple ("error in redirection: " ++ msg)) (failWith msg s2)
        (if exitOnError then .exit_ else .done)
    | (s2, .inr savedFds) =>
      let expAssigns := assigns.map (fun (k, w) =>
        (k, ExpansionState.expStart { splitting := .noSplit, globbing := false } w))
      let s3 := newLocalScope s2
      (.xsSimple "redirected; expanding assignments", s3,
       .commandExpAssign expAssigns fs savedFds opts)

  -- Semi (sequencing)
  | .semi s1 s2 =>
    match s1 with
    | .done => checkTraps (.xsSemi "next", s, s2)
    | .exit_ => (.xsSimple "propagate-exit", s, .exit_)
    | .return_ => (.xsSimple "propagate-return", s, .return_)
    | .break_ n => (.xsSimple "propagate-break", s, .break_ n)
    | .continue_ n => (.xsSimple "propagate-continue", s, .continue_ n)
    | _ =>
      let (step, s', c') := stepEval s s1 checked
      match c' with
      | .done => checkTraps (.xsNested (.xsSemi "done LHS") step, s', s2)
      | .exit_ => (.xsNested (.xsSemi "propagate-exit") step, s', .exit_)
      | .return_ => (.xsNested (.xsSemi "propagate-return") step, s', .return_)
      | .break_ n => (.xsNested (.xsSemi "propagate-break") step, s', .break_ n)
      | .continue_ n => (.xsNested (.xsSemi "propagate-continue") step, s', .continue_ n)
      | _ => (.xsNested (.xsSemi "left") step, s', .semi c' s2)

  -- And
  | .and_ s1 s2 =>
    match s1 with
    | .done =>
      if s.sh.exitCode == 0 then checkTraps (.xsAnd "success-continue", s, s2)
      else checkTraps (.xsAnd "fail-skip", s, .done)
    | .exit_ => (.xsSimple "propagate-exit", s, .exit_)
    | .return_ => (.xsSimple "propagate-return", s, .return_)
    | .break_ n => (.xsSimple "propagate-break", s, .break_ n)
    | .continue_ n => (.xsSimple "propagate-continue", s, .continue_ n)
    | _ =>
      let (step, s', c') := stepEval s s1 .checked
      match c' with
      | .done =>
        if s'.sh.exitCode == 0 then checkTraps (.xsNested (.xsAnd "success-continue") step, s', s2)
        else checkTraps (.xsNested (.xsAnd "fail-skip") step, s', .done)
      | .exit_ => (.xsNested (.xsAnd "propagate-exit") step, s', .exit_)
      | .return_ => (.xsNested (.xsAnd "propagate-return") step, s', .return_)
      | .break_ n => (.xsNested (.xsAnd "propagate-break") step, s', .break_ n)
      | .continue_ n => (.xsNested (.xsAnd "propagate-continue") step, s', .continue_ n)
      | _ => (.xsNested (.xsAnd "left") step, s', .and_ c' s2)

  -- Or
  | .or_ s1 s2 =>
    match s1 with
    | .done =>
      if s.sh.exitCode != 0 then checkTraps (.xsOr "fail-continue", s, s2)
      else checkTraps (.xsOr "success-skip", s, .done)
    | .exit_ => (.xsSimple "propagate-exit", s, .exit_)
    | .return_ => (.xsSimple "propagate-return", s, .return_)
    | .break_ n => (.xsSimple "propagate-break", s, .break_ n)
    | .continue_ n => (.xsSimple "propagate-continue", s, .continue_ n)
    | _ =>
      let (step, s', c') := stepEval s s1 .checked
      match c' with
      | .done =>
        if s'.sh.exitCode != 0 then checkTraps (.xsNested (.xsOr "fail-continue") step, s', s2)
        else checkTraps (.xsNested (.xsOr "success-skip") step, s', .done)
      | .exit_ => (.xsNested (.xsOr "propagate-exit") step, s', .exit_)
      | .return_ => (.xsNested (.xsOr "propagate-return") step, s', .return_)
      | .break_ n => (.xsNested (.xsOr "propagate-break") step, s', .break_ n)
      | .continue_ n => (.xsNested (.xsOr "propagate-continue") step, s', .continue_ n)
      | _ => (.xsNested (.xsOr "left") step, s', .or_ c' s2)

  -- Not
  | .not_ s1 =>
    match s1 with
    | .done =>
      let ec := if s.sh.exitCode == 0 then 1 else 0
      checkTraps (.xsNot "negate", exitWith ec s, .done)
    | .exit_ => (.xsSimple "propagate-exit", s, .exit_)
    | .return_ => (.xsSimple "propagate-return", s, .return_)
    | .break_ n => (.xsSimple "propagate-break", s, .break_ n)
    | .continue_ n => (.xsSimple "propagate-continue", s, .continue_ n)
    | _ =>
      let (step, s', c') := stepEval s s1 .checked
      match c' with
      | .done =>
        let ec := if s'.sh.exitCode == 0 then 1 else 0
        checkTraps (.xsNested (.xsNot "negate") step, exitWith ec s', .done)
      | .exit_ => (.xsNested (.xsNot "propagate-exit") step, s', .exit_)
      | .return_ => (.xsNested (.xsNot "propagate-return") step, s', .return_)
      | .break_ n => (.xsNested (.xsNot "propagate-break") step, s', .break_ n)
      | .continue_ n => (.xsNested (.xsNot "propagate-continue") step, s', .continue_ n)
      | _ => (.xsNested (.xsNot "body") step, s', .not_ c')

  -- If
  | .if_ cond then_ else_ =>
    match cond with
    | .done =>
      if s.sh.exitCode == 0 then (.xsIf "then", s, then_)
      else (.xsIf "else", s, else_)
    | .exit_ => (.xsSimple "propagate-exit", s, .exit_)
    | .return_ => (.xsSimple "propagate-return", s, .return_)
    | .break_ n => (.xsSimple "propagate-break", s, .break_ n)
    | .continue_ n => (.xsSimple "propagate-continue", s, .continue_ n)
    | _ =>
      let (step, s', c') := stepEval s cond .checked
      match c' with
      | .done =>
        if s'.sh.exitCode == 0 then (.xsNested (.xsIf "then") step, s', then_)
        else (.xsNested (.xsIf "else") step, s', else_)
      | .exit_ => (.xsNested (.xsIf "propagate-exit") step, s', .exit_)
      | .return_ => (.xsNested (.xsIf "propagate-return") step, s', .return_)
      | .break_ n => (.xsNested (.xsIf "propagate-break") step, s', .break_ n)
      | .continue_ n => (.xsNested (.xsIf "propagate-continue") step, s', .continue_ n)
      | _ => (.xsNested (.xsIf "cond") step, s', .if_ c' then_ else_)

  -- While condition
  | .while_ cond body =>
    (.xsWhile "enter", enterLoop s, .whileCond cond cond body none)

  | .whileCond origCond curCond origBody savedEc =>
    let (step, s1, cur') := stepEval s curCond .checked
    match cur' with
    | .exit_ => (.xsNested (.xsWhile "exiting") step, s1, .exit_)
    | .return_ => (.xsNested (.xsWhile "returning") step, s1, .return_)
    | .break_ 1 => (.xsNested (.xsWhile "breaking") step, exitLoop s1, .done)
    | .break_ n => (.xsNested (.xsWhile "breaking to outer loop") step,
                     exitLoop s1, .break_ (n - 1))
    | .continue_ 1 => (.xsNested (.xsWhile "continuing loop") step,
                         s1, .whileCond origCond origCond origBody savedEc)
    | .continue_ n => (.xsNested (.xsWhile "continuing to outer loop") step,
                         exitLoop s1, .continue_ (n - 1))
    | .done =>
      checkTraps
        (if s1.sh.exitCode == 0
         then (.xsNested (.xsWhile "exit code was 0, running the loop body") step,
               s1, .whileRunning origCond origBody origBody)
         else
           let ec := match savedEc with | some ec => ec | none => 0
           (.xsNested (.xsWhile "exit code was non-zero, exiting loop") step,
            exitWith ec (exitLoop s1), .done))
    | _ => (.xsNested (.xsWhile "") step, s1, .whileCond origCond cur' origBody savedEc)

  | .whileRunning origCond origBody curBody =>
    let (step, s1, cur') := stepEval s curBody checked
    match cur' with
    | .exit_ => (.xsNested (.xsWhile "exiting") step, s1, .exit_)
    | .return_ => (.xsNested (.xsWhile "returning") step, s1, .return_)
    | .break_ 1 => (.xsNested (.xsWhile "breaking loop") step, exitLoop s1, .done)
    | .break_ n => (.xsNested (.xsWhile "breaking to outer loop") step, exitLoop s1, .break_ (n - 1))
    | .continue_ 1 => (.xsNested (.xsWhile "continuing loop") step,
                         s1, .whileCond origCond origCond origBody (some s1.sh.exitCode))
    | .continue_ n => (.xsNested (.xsWhile "continuing to outer loop") step, exitLoop s1, .continue_ (n - 1))
    | .done => checkTraps
        (.xsNested (.xsWhile "finished iteration, retesting condition") step,
         s1, .whileCond origCond origCond origBody (some s1.sh.exitCode))
    | _ => (.xsNested (.xsWhile "") step, s1, .whileRunning origCond origBody cur')

  -- For
  | .for_ var words body =>
    (.xsFor "expand", s, .forExpArgs var (.expStart { splitting := .split, globbing := true } words) body)

  | .forExpArgs var es body =>
    let (step, s', es') := stepExpansion (stepEval' s) s es
    match es' with
    | .expDone fs => (.xsFor "expanded", s', .forExpanded var fs body)
    | _ => (.xsFor "expanding", s', .forExpArgs var es' body)

  | .forExpanded var fs body =>
    match fs with
    | [] => checkTraps (.xsFor "no items, exit code is 0", exitWith 0 s, .done)
    | val :: fs' =>
      match setParam var val s with
      | .inr s1 =>
        (.xsFor "start", enterLoop s1, .forRunning var fs' body body)
      | .inl err =>
        (.xsFor err, failWith ("for: " ++ err) s,
         if isInteractive s then .done else .exit_)

  | .forRunning var fs origBody curBody =>
    -- Helper: advance to next iteration
    let continueLoop (s0 : OsState α) (step : EvaluationStep) (msg : String) (i : SymbolicString) (f' : Fields) :=
      match setParam var i s0 with
      | .inl err =>
        (.xsNested (.xsFor err) step,
         failWith ("for: " ++ err) s0,
         if isInteractive s0 then .done else .exit_)
      | .inr s1 =>
        (.xsNested (.xsFor (msg ++ " to next iteration")) step,
         s1, .forRunning var f' origBody origBody)
    let (step, s1, cur') := stepEval s curBody checked
    match cur' with
    | .exit_ => (.xsNested (.xsFor "exiting") step, s1, .exit_)
    | .return_ => (.xsNested (.xsFor "returning") step, s1, .return_)
    | .break_ 1 => (.xsNested (.xsFor "breaking loop") step, exitLoop s1, .done)
    | .break_ n => (.xsNested (.xsFor "breaking to outer loop") step, exitLoop s1, .break_ (n - 1))
    | .continue_ 1 =>
      match fs with
      | [] => (.xsNested (.xsFor "continued at last iteration") step, exitLoop s1, .done)
      | i :: f' => continueLoop s1 step "continuing" i f'
    | .continue_ n => (.xsNested (.xsFor "continuing to outer loop") step, s1, .continue_ (n - 1))
    | .done =>
      checkTraps
        (match fs with
         | [] => (.xsNested (.xsFor "finished last iteration") step, exitLoop s1, .done)
         | i :: f' => continueLoop s1 step "stepping" i f')
    | _ => (.xsNested (.xsFor "") step, s1, .forRunning var fs origBody cur')

  | .case_ w cases =>
    (.xsCase "expand", s, .caseExpArg (.expStart { splitting := .noSplit, globbing := false } w) cases)

  | .caseExpArg es cases =>
    let (step, s', es') := stepExpansion (stepEval' s) s es
    match es' with
    | .expExpand _opts f0 [] =>
      let ss := symbolicStringOfExpandedWords true f0
      (.xsCase "match", s', .caseMatch ss cases)
    | .expDone fs =>
      -- Fallback (should be unreachable if we catch expExpand)
      let ss := fs.flatMap id
      (.xsCase "match", s', .caseMatch ss cases)
    | _ => (.xsCase "expanding", s', .caseExpArg es' cases)

  | .caseMatch _ss [] => checkTraps (.xsCase "no-match", exitWith 0 s, .done)
  | .caseMatch ss ((pats, body) :: rest) =>
    match pats with
    | [] => (.xsCase "next-case", s, .caseMatch ss rest)
    | pat :: pats' =>
      let es := ExpansionState.expStart { splitting := .noSplit, globbing := false } pat
      (.xsCase "testing", s, .caseCheckMatch ss es body ((pats', body) :: rest))

  | .caseCheckMatch ss es body rest =>
    let (_step, s', es') := stepExpansion (stepEval' s) s es
    match es' with
    | .expExpand _opts f0 [] =>
      let pat := symbolicStringOfExpandedWords true f0
      match matchExact s'.sh.locale pat ss with
      | .match_ _ => checkTraps (.xsCase "matched", s', body)
      | .symbolic => (.xsCase "symbolic-match", s', .caseCheckMatch ss es body rest) -- Should not happen in concrete
      | .noMatch =>
        -- Try remaining patterns in this case
        match rest with
        | (pats', _body') :: rest' =>
          (.xsCase "no-match-pat", s', .caseMatch ss ((pats', body) :: rest'))
        | [] => (.xsCase "no-match-pat", s', .caseMatch ss [])
    | .expDone fs =>
      let pat := fs.flatMap id
      match matchExact s'.sh.locale pat ss with
      | .match_ _ => checkTraps (.xsCase "matched", s', body)
      | .symbolic => (.xsCase "symbolic-match", s', .caseCheckMatch ss es body rest)
      | .noMatch =>
        match rest with
        | (pats', _body') :: rest' =>
          (.xsCase "no-match-pat", s', .caseMatch ss ((pats', body) :: rest'))
        | [] => (.xsCase "no-match-pat", s', .caseMatch ss [])

    | _ => (.xsCase "expanding-pat", s', .caseCheckMatch ss es' body rest)

  -- Defun
  | .defun name body =>
    let s' := { s with sh := { s.sh with funcs := (name, body) :: s.sh.funcs.filter (fun (n, _) => n != name) } }
    checkTraps (.xsDefun "define", exitWith 0 s', .done)

  -- Call (function invocation)
  | .call outerLoopNest outerParams funcName _origBody curBody =>
    let cleanup (os : OsState α) : OsState α :=
      let (os', _) := popLocals os
      setFunctionParams outerLoopNest outerParams os'
    match curBody with
    | .done =>
      checkTraps (.xsStack funcName (.xsSimple "implicit return"), cleanup s, .done)
    | .return_ =>
      checkTraps (.xsStack funcName (.xsSimple "explicit return"), cleanup s, .done)
    | .exit_ =>
      (.xsStack funcName (.xsSimple "exit"), cleanup s, .exit_)
    | .break_ n =>
      (.xsStack funcName (.xsSimple "break"), cleanup s, .break_ n)
    | .continue_ n =>
      (.xsStack funcName (.xsSimple "continue"), cleanup s, .continue_ n)
    | _ =>
      let (step, s', c') := stepEval s curBody checked
      match c' with
      | .done =>
        (.xsStack (funcName ++ ": implicit return") step, cleanup s', .done)
      | .return_ =>
        (.xsStack (funcName ++ ": explicit return") step, cleanup s', .done)
      | .exit_ =>
        (.xsStack (funcName ++ ": exit") step, cleanup s', .exit_)
      | .break_ n =>
        (.xsStack (funcName ++ ": break") step, cleanup s', .break_ n)
      | .continue_ n =>
        (.xsStack (funcName ++ ": continue") step, cleanup s', .continue_ n)
      | _ =>
        (.xsStack funcName step, s', .call outerLoopNest outerParams funcName _origBody c')

  -- Pipe
  | .pipe bgMode cmds =>
    match runPipe s cmds bgMode with
    | .inl err =>
      (.xsPipe "couldn't start pipe",
       failWith s!"couldn't create pipeline: {err}" s,
       .done)
    | .inr (s1, pipeline, lastPid) =>
      let (s2, _job) := addJob s1 pipeline lastPid (.pipe bgMode cmds) bgMode .jobRunning
      if isBg bgMode
      then (.xsPipe "started pipe", setLastPid lastPid s2, .done)
      else (.xsPipe "started pipe", s2, .wait lastPid .unchecked none .waitInternal)

  -- Redir: all redirects expanded
  | .redir stmt' (ers, none, []) =>
    match doRedirs s ers with
    | (s1, .inl msg) =>
      (.xsRedir "error in redirection", failWith msg s1, .done)
    | (s1, .inr savedFds) =>
      (.xsRedir "running redirected command", s1, pushredir' stmt' savedFds)

  -- Redir: expanding redirects
  | .redir stmt' (ers, none, r :: rs) =>
    let xr := match r with
      | .rfile ty fd w => ExpandingRedir.xrFile ty fd (.expStart { splitting := .noSplit, globbing := false } w)
      | .rdup ty fd w => ExpandingRedir.xrDup ty fd (.expStart { splitting := .noSplit, globbing := false } w)
      | .rheredoc ty fd w => ExpandingRedir.xrHeredoc ty fd (.expStart { splitting := .noSplit, globbing := false } w)
    (.xsRedir "starting", s, .redir stmt' (ers, some xr, rs))

  -- Redir: stepping an expanding redirect
  | .redir stmt' (ers, some xr, rs) =>
    match stepRedir (stepEval' s) s xr with
    | .redirExpDone s' er =>
      (.xsRedir "expanding", s', .redir stmt' (ers ++ [er], none, rs))
    | .redirExpStep step s' xr' =>
      (.xsExpand (.xsRedir "redirect") step, s', .redir stmt' (ers, some xr', rs))
    | .redirExpError msg =>
      (.xsRedir "error in redirect expansion", failWith msg s, .done)

  -- Background: all redirects expanded
  | .background stmt' (ers, none, []) =>
    let redirState' : RedirState :=
      if !s.sh.opts.any (· == .monitor) && !ers.any expandedRedirHasStdinRedir
      then (.erFile .from_ 0 (symbolicStringOfString "/dev/null") :: ers, none, [])
      else (ers, none, [])
    let (s1, pid) := OS.osForkAndSubshell s (.redir stmt' redirState') .bg none true
    let (s2, _job) := addJob s1 [(pid, .background stmt' (ers, none, []))] pid (.background stmt' (ers, none, [])) .bg .jobRunning
    let s3 := setLastPid pid s2
    (.xsBackground s!"started background process with pid {pid}", s3, .done)

  -- Background: expanding redirects
  | .background stmt' (ers, none, r :: rs) =>
    let xr := match r with
      | .rfile ty fd w => ExpandingRedir.xrFile ty fd (.expStart { splitting := .noSplit, globbing := false } w)
      | .rdup ty fd w => ExpandingRedir.xrDup ty fd (.expStart { splitting := .noSplit, globbing := false } w)
      | .rheredoc ty fd w => ExpandingRedir.xrHeredoc ty fd (.expStart { splitting := .noSplit, globbing := false } w)
    (.xsBackground "starting redir", s, .background stmt' (ers, some xr, rs))

  | .background stmt' (ers, some xr, rs) =>
    match stepRedir (stepEval' s) s xr with
    | .redirExpDone s' er =>
      (.xsBackground "expanding", s', .background stmt' (ers ++ [er], none, rs))
    | .redirExpStep step s' xr' =>
      (.xsExpand (.xsBackground "redirect") step, s', .background stmt' (ers, some xr', rs))
    | .redirExpError msg =>
      (.xsBackground "error in redirect expansion", failWith msg s, .done)

  -- Subshell: all redirects expanded
  | .subshell stmt' (ers, none, []) =>
    match doRedirs s ers with
    | (s1, .inl msg) =>
      (.xsSubshell "error in redirection", failWith msg s1, .done)
    | (s1, .inr savedFds) =>
      -- OCaml: let checked_c = (if checked_exit checked then CheckedExit stmt' else stmt') in
      let checkedStmt := if checked.checkedExit then .checkedExit stmt' else stmt'
      let (s2, pid) := OS.osForkAndSubshell s1 checkedStmt .fg none true
      (.xsSubshell s!"started subshell with pid {pid}",
       restoreFds s2 savedFds,
       .wait pid checked none .waitInternal)

  -- Subshell: expanding redirects
  | .subshell stmt' (ers, none, r :: rs) =>
    let xr := match r with
      | .rfile ty fd w => ExpandingRedir.xrFile ty fd (.expStart { splitting := .noSplit, globbing := false } w)
      | .rdup ty fd w => ExpandingRedir.xrDup ty fd (.expStart { splitting := .noSplit, globbing := false } w)
      | .rheredoc ty fd w => ExpandingRedir.xrHeredoc ty fd (.expStart { splitting := .noSplit, globbing := false } w)
    (.xsSubshell "starting redir", s, .subshell stmt' (ers, some xr, rs))

  | .subshell stmt' (ers, some xr, rs) =>
    match stepRedir (stepEval' s) s xr with
    | .redirExpDone s' er =>
      (.xsSubshell "expanding", s', .subshell stmt' (ers ++ [er], none, rs))
    | .redirExpStep step s' xr' =>
      (.xsExpand (.xsSubshell "redirect") step, s', .subshell stmt' (ers, some xr', rs))
    | .redirExpError msg =>
      (.xsSubshell "error in redirect expansion", failWith msg s, .done)

  -- Break / continue — OCaml: bottom out to Done with check_traps
  | .break_ _n => checkTraps (.xsSimple "break bottomed out", s, .done)

  | .continue_ _n => checkTraps (.xsSimple "continue bottomed out", s, .done)

  -- Return — OCaml: bottom out to Done with check_traps
  | .return_ => checkTraps (.xsSimple "return bottomed out", s, .done)

  -- Exit — OCaml: run exit_trap, then exit
  | .exit_ =>
    let (s', trapOpt) := exitTrap s
    match trapOpt with
    | none => (.xsSimple "exited", OS.osExit s', .done)
    | some handler =>
      let sHandler := stringOfSymbolicString handler
      let cmd := Stmt.evalLoop 1 (none, none) (.parseString .parseTrap sHandler) .noninteractive .subsidiary
      (.xsSimple "trapped on exit", s', .semi cmd .exit_)

  -- Wait
  | .wait pid check _steps _mode =>
    match waitForPid (stepEval' s) s pid with
    | (s', none) => (.xsWait "no-child", s', .done)
    | (s', some (.inl _step)) => (.xsWait "step", s', .wait pid check _steps _mode)
    | (s', some (.inr code)) =>
      (.xsWait "done", exitWith code s', .done)

  -- Trapped
  | .trapped signal ec handler cont =>
    match handler with
    | .done =>
      (.xsTrap signal "done", exitWith ec s, cont)
    | .exit_ => (.xsTrap signal "propagate-exit", s, .exit_)
    | .return_ => (.xsTrap signal "propagate-return", s, .return_)
    | .break_ n => (.xsTrap signal "propagate-break", s, .break_ n)
    | .continue_ n => (.xsTrap signal "propagate-continue", s, .continue_ n)
    | _ =>
      let (_step, s', c') := stepEval s handler .unchecked
      match c' with
      | .done => checkTraps (.xsNested (.xsTrap signal "handler-done") _step, s', .trapped signal ec .done cont)
      | .exit_ => (.xsNested (.xsTrap signal "propagate-exit") _step, s', .exit_)
      | .return_ => (.xsNested (.xsTrap signal "propagate-return") _step, s', .return_)
      | .break_ n => (.xsNested (.xsTrap signal "propagate-break") _step, s', .break_ n)
      | .continue_ n => (.xsNested (.xsTrap signal "propagate-continue") _step, s', .continue_ n)
      | _ => (.xsTrap signal "handler", s', .trapped signal ec c' cont)

  -- Checked exit — OCaml: uses is_terminating_control, not just .done
  | .checkedExit stmt =>
    if isTerminatingControl stmt then
      checkTraps (.xsSubshell "", s, stmt)
    else
      let (_step, s', c') := stepEval s stmt .checked
      (.xsNested (.xsSubshell "disable errexit") _step, s', .checkedExit c')

  -- Pushredir — OCaml: uses is_terminating_control, not just .done
  | .pushredir stmt saved =>
    if isTerminatingControl stmt then
      checkTraps (.xsRedir "popping redirects", restoreFds s saved, stmt)
    else
      let (_step, s', c') := stepEval s stmt checked
      (.xsNested (.xsRedir "") _step, s', .pushredir c' saved)

  -- EvalLoop
  | .evalLoop linno _ctx src _mode _level =>
    -- Parse the source string into a Stmt and execute it
    match src with
    | .parseString _ cmdStr =>
      let stmt := parseTrapString cmdStr
      (.xsEval linno src "eval-loop-start", s, .evalLoopCmd linno _ctx src _mode _level stmt)
    | _ =>
      (.xsEval linno src "eval-loop-unknown-src", s, .done)

  | .evalLoopCmd linno _ctx src _mode _level cmd =>
    match cmd with
    | .done =>
      -- For parseString sources (trap/eval), the entire string is parsed at once,
      -- so when done, just finish (don't loop back to re-parse the same string)
      (.xsEval linno src "eval-done", s, .done)
    | .break_ n => (.xsEval linno src "eval-break", s, .break_ n)
    | .continue_ n => (.xsEval linno src "eval-continue", s, .continue_ n)
    | .return_ => (.xsEval linno src "eval-return", s, .return_)
    | .exit_ => (.xsEval linno src "eval-exit", s, .exit_)
    | _ =>
      let (_step, s', c') := stepEval s cmd .unchecked
      (.xsEval linno src "running", s', .evalLoopCmd linno _ctx src _mode _level c')


  -- Simple command execution (invoked via runCommand dispatch)
  | .exec _cmd prog _args _env _binsh =>
    -- In symbolic mode, execve doesn't actually work.
    -- OCaml: call execve, get error, fail.
    let s' := OS.osExecve s prog
    (.xsSimple "exec", failWith "symbolic execve unimplemented" s',
     if isInteractive s' then .done else .exit_)

  | .commandExpAssign ((x, es) :: assigns) args savedFds opts =>
    let (step, s', es') := stepExpansion (stepEval' s) s es
    -- OCaml semantics.ml:788-790: track ran_cmd_subst during assignment expansion
    let opts' := { opts with ranCmdSubst := opts.ranCmdSubst || ranCommandSubstitution step }
    match es' with
    | .expDone f =>
      match forceLocalParam s' x (symbolicStringOfFields f) with
      | Sum.inl err =>
        -- Match OCaml semantics.ml:796-817
        let specialOrAssign := match args with
          | cmd :: _ =>
            let (_, _, progName) := concretize s' cmd
            isSpecialBuiltinName progName && !opts'.forceSimpleCommand
          | [] => true
        let mayExit := s'.sh.opts.any (· == .errexit) || !isInteractive s'
        let s'' := safeWriteStderr (err ++ "\n") s'
        (.xsSimple "assignment error", exitWith 2 s'',
         if specialOrAssign && mayExit then .exit_ else .done)
      | Sum.inr s'' =>
        (.xsSimple ("assign " ++ x), s'', .commandExpAssign assigns args savedFds opts')
    | .expError err =>
      expansionError true s' (.xsSimple "assignment expansion") step err
    | _ =>
      (.xsExpand (.xsSimple "") step, s', .commandExpAssign ((x, es') :: assigns) args savedFds opts')

  -- CommandExpAssign: all assignments expanded, check for command
  | .commandExpAssign [] args savedFds opts =>
    let (s1, localBindings) := popLocals s
    let assigns : List (String × SymbolicString) := localBindings.filterMap (fun (x, mv) => match mv with | some v => some (x, v) | none => none)
    match args with
    | [] =>
      -- No command, just assignments. Restore FDs.
      let s2 := restoreFds s1 savedFds
      let s3 := if opts.ranCmdSubst then s2 else exitWith 0 s2
      let s4 := assigns.foldr (fun (x, v) os => checkedSetParam x v os) s3
      checkTraps (.xsSimple "finished assignments w/o command, popping redirects", s4, Stmt.done)
    | cmd :: argv =>
      (.xsSimple "assignments fully expanded", s1, .commandReady assigns cmd argv savedFds opts)

  -- CommandReady: dispatch command
  | .commandReady assigns prog args savedFds opts =>
    if s.sh.opts.any (· == .noexec) then
      checkTraps (.xsSimple "set -n: skipping command", s, Stmt.done)
    else
      let (s0, _concretizedSS, progName) := concretize s prog
      -- OCaml: `not concretized` means 'was already concrete' — for our concrete strings this is always true
      -- For special builtins, apply assignments to current environment
      let progSpecial := isSpecialBuiltinName progName
      let s1 :=
        if progSpecial && !opts.forceSimpleCommand
        then assigns.foldr (fun (x, v) os => checkedSetParam x v os) s0
        else s0
      -- catching_errors: not checked_exit && errexit is set (OCaml semantics.ml:942)
      let catchingErrors := !checked.checkedExit && s1.sh.opts.any (· == .errexit)
      -- exit_on_error: catching_errors || (special && !forceSimple && !interactive)
      let exitOnError := catchingErrors ||
        (progSpecial && !opts.forceSimpleCommand && !(s1.sh.opts.any (· == .interactive)))
      -- Build env from assignments
      let env1 := assigns.map id
      -- Dispatch through runCommand (handles special builtins, functions, regular builtins, external)
      match Shell.runCommand s1 opts checked prog args env1 savedFds with
      | .inr (s2, .done, restore) =>
        -- Command completed
        let stmt' :=
          if catchingErrors && s2.sh.exitCode != 0 then .exit_
          else if restore then pushredir' .done savedFds
          else .done
        checkTraps (.xsSimple ("done running " ++ stringOfSymbolicString prog), s2, stmt')
      | .inr (s2, cont, restore) =>
        -- Command returned continuation
        let stmt' := if restore then pushredir' cont savedFds else cont
        (.xsSimple ("running " ++ stringOfSymbolicString prog), s2, stmt')
      | .inl (s2, msg) =>
        -- Error from run_command
        checkTraps (.xsSimple "couldn't run command",
         failWith (stringOfSymbolicString prog ++ ": " ++ msg) s2,
         if exitOnError then .exit_
         else pushredir' .done savedFds)

where
  stepEval' (_s : OsState α) : StepFun α := fun os stmt =>
    let (_step, os', stmt') := stepEval os stmt .unchecked
    (os', match stmt' with | .done => .inr (some os'.sh.exitCode) | _ => .inl (_step, stmt'))

end Semantics
