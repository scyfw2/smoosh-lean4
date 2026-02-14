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
  runCommand : OsState α → CommandOpts → CheckingMode → SymbolicString → List SymbolicString → Env → List (Fd × Sum Fd Unit) → EvaluationStep × OsState α × Stmt

section Semantics
variable {α : Type} [OS α] [Shell α]

/-- Check if a command name is a POSIX special builtin -/
private def isSpecialBuiltinName (name : String) : Bool :=
  name ∈ ["break", ":", "continue", ".", "eval", "exec", "exit",
           "export", "readonly", "return", "set", "shift", "times",
           "trap", "unset"]

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
                    (.evalLoop 0 (none, none) (.parseString .parseTrap (String.join (ssHandler.filterMap (fun c => match c with | .c ch => some (String.ofList [ch]) | .sym _ => none)))) .noninteractive .subsidiary) c
        (step', s1, c')

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
    else
      (s0, (lookupParam s0 str).map (fun ss => [ss]))
  let cstr (sv : String) := (s1, [ExpandedWord.expS sv], ([] : Words))
  let ewfs (fs : Fields) := (s1, expandedWordsOfFields fs, ([] : Words))
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
def tryMatchSubstring (_lc : Locale) (side : SubstringSide) (mode : SubstringMode)
    (pat str : SymbolicString) : SymbolicString :=
  let matcherFn := match side, mode with
    | .prefix_, .shortest => matchShortest _lc pat
    | .prefix_, .longest  => matchLongest _lc pat
    | .suffix_, .shortest => matchShortest _lc pat
    | .suffix_, .longest  => matchLongest _lc pat
  match matcherFn str with
  | .match_ (_, remainder) => remainder
  | _ => str

-- Result types for expand_control / expand_words
-- Left = error:  (step, os, expanded_words)
-- Right = continue: (step, os, expanded_words, words)
abbrev ExpCtrlResult (α : Type) :=
  Sum (ExpansionStep × OsState α × ExpandedWords)
      (ExpansionStep × OsState α × ExpandedWords × Words)

instance : Nonempty (ExpCtrlResult α) := ⟨Sum.inl (.esStep "", sorry, [])⟩

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
    let (s1, _, pat) := concretize s0 sympat
    let matched := tryMatchSubstring s1.sh.locale side mode (symbolicStringOfString pat) symstr
    Sum.inr (.esParam "finished match", s1, [], wordsOfSymbolicString matched)
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
          | some s => match String.toInt? s with | some i => i | none => 0
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
    Sum.inr (.esEscape "", s0, [.dquo [.c c]], [])

/-- Expand a word list — translated from expand_words (semantics.lem:469-487) -/
partial def expandWords (stepFun : StepFun α) (s0 : OsState α) (split : SplittingMode) (q : QuotingMode) (sm : StringMode)
    (f : ExpandedWords) : Words → ExpCtrlResult α
  | [] => Sum.inr (.esStep "done", s0, f, [])
  | .f :: ws => Sum.inr (.esStep "user field separator", s0, f ++ [.usrF], ws)
  | .s "" :: ws => expandWords stepFun s0 split q sm f ws
  | .s str :: ws =>
    let f1 := match q, sm with
      | .quoted, _ => [ExpandedWord.dquo (symbolicStringOfString str)]
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

/-- Main evaluation stepper — this is the heart of the semantics -/
instance : Nonempty (EvaluationStep × OsState α × Stmt) := ⟨sorry⟩
partial def stepEval (s : OsState α) (c : Stmt)
    : EvaluationStep × OsState α × Stmt :=
  match c with
  | .done => (.xsSimple "done", s, .done)

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
      (.xsSimple "command-exp-redirs", s', .commandExpRedirs assigns fs rs opts)
    | _ =>
      (.xsSimple "expanding", s', .commandExpArgs assigns es' redirs opts)

  -- Expanding redirects
  | .commandExpRedirs assigns fs (ers, mxr, []) opts =>
    match mxr with
    | none =>
      -- All redirects expanded — push local scope for assignments
      let (s1, savedFds) := match (doRedirs s ers) with
        | (s', .inr sf) => (s', sf)
        | (s', .inl _) => (s', [])
      let s2 := newLocalScope s1
      (.xsSimple "command-ready", s2,
       .commandExpAssign (assigns.map (fun (k, w) => (k, .expStart { splitting := .noSplit, globbing := false } w))) fs savedFds opts)
    | some xr =>
      match stepRedir (stepEval' s) s xr with
      | .redirExpDone s' er =>
        (.xsRedir "expanding", s', .commandExpRedirs assigns fs (ers ++ [er], none, []) opts)
      | .redirExpStep step s' xr' =>
        ((.xsExpand (.xsRedir "redirect") step), s', .commandExpRedirs assigns fs (ers, some xr', []) opts)
      | .redirExpError msg =>
        (.xsSimple "redir-error", failWith msg s, .done)
  | .commandExpRedirs assigns fs (ers, mxr, r :: rs) opts =>
    let xr := match r with
      | .rfile ty fd w => ExpandingRedir.xrFile ty fd (.expStart { splitting := .noSplit, globbing := false } w)
      | .rdup ty fd w => ExpandingRedir.xrDup ty fd (.expStart { splitting := .noSplit, globbing := false } w)
      | .rheredoc ty fd w => ExpandingRedir.xrHeredoc ty fd (.expStart { splitting := .noSplit, globbing := false } w)
    (.xsRedir "starting", s, .commandExpRedirs assigns fs (ers, some xr, rs) opts)

  -- Semi (sequencing)
  | .semi s1 s2 =>
    match s1 with
    | .done => (.xsSemi "next", s, s2)
    | .exit_ => (.xsSimple "propagate-exit", s, .exit_)
    | .return_ => (.xsSimple "propagate-return", s, .return_)
    | .break_ n => (.xsSimple "propagate-break", s, .break_ n)
    | .continue_ n => (.xsSimple "propagate-continue", s, .continue_ n)
    | _ =>
      let (step, s', c') := stepEval s s1
      match c' with
      | .done => (.xsNested (.xsSemi "done LHS") step, s', s2)
      | .exit_ => (.xsNested (.xsSemi "propagate-exit") step, s', .exit_)
      | .return_ => (.xsNested (.xsSemi "propagate-return") step, s', .return_)
      | .break_ n => (.xsNested (.xsSemi "propagate-break") step, s', .break_ n)
      | .continue_ n => (.xsNested (.xsSemi "propagate-continue") step, s', .continue_ n)
      | _ => (.xsNested (.xsSemi "left") step, s', .semi c' s2)

  -- And
  | .and_ s1 s2 =>
    match s1 with
    | .done =>
      if s.sh.exitCode == 0 then (.xsAnd "success-continue", s, s2)
      else (.xsAnd "fail-skip", s, .done)
    | .exit_ => (.xsSimple "propagate-exit", s, .exit_)
    | .return_ => (.xsSimple "propagate-return", s, .return_)
    | .break_ n => (.xsSimple "propagate-break", s, .break_ n)
    | .continue_ n => (.xsSimple "propagate-continue", s, .continue_ n)
    | _ =>
      let (step, s', c') := stepEval s s1
      match c' with
      | .done =>
        if s'.sh.exitCode == 0 then (.xsNested (.xsAnd "success-continue") step, s', s2)
        else (.xsNested (.xsAnd "fail-skip") step, s', .done)
      | .exit_ => (.xsNested (.xsAnd "propagate-exit") step, s', .exit_)
      | .return_ => (.xsNested (.xsAnd "propagate-return") step, s', .return_)
      | .break_ n => (.xsNested (.xsAnd "propagate-break") step, s', .break_ n)
      | .continue_ n => (.xsNested (.xsAnd "propagate-continue") step, s', .continue_ n)
      | _ => (.xsNested (.xsAnd "left") step, s', .and_ c' s2)

  -- Or
  | .or_ s1 s2 =>
    match s1 with
    | .done =>
      if s.sh.exitCode != 0 then (.xsOr "fail-continue", s, s2)
      else (.xsOr "success-skip", s, .done)
    | .exit_ => (.xsSimple "propagate-exit", s, .exit_)
    | .return_ => (.xsSimple "propagate-return", s, .return_)
    | .break_ n => (.xsSimple "propagate-break", s, .break_ n)
    | .continue_ n => (.xsSimple "propagate-continue", s, .continue_ n)
    | _ =>
      let (step, s', c') := stepEval s s1
      match c' with
      | .done =>
        if s'.sh.exitCode != 0 then (.xsNested (.xsOr "fail-continue") step, s', s2)
        else (.xsNested (.xsOr "success-skip") step, s', .done)
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
      (.xsNot "negate", exitWith ec s, .done)
    | .exit_ => (.xsSimple "propagate-exit", s, .exit_)
    | .return_ => (.xsSimple "propagate-return", s, .return_)
    | .break_ n => (.xsSimple "propagate-break", s, .break_ n)
    | .continue_ n => (.xsSimple "propagate-continue", s, .continue_ n)
    | _ =>
      let (step, s', c') := stepEval s s1
      match c' with
      | .done =>
        let ec := if s'.sh.exitCode == 0 then 1 else 0
        (.xsNested (.xsNot "negate") step, exitWith ec s', .done)
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
      let (step, s', c') := stepEval s cond
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
    let s' := { s with sh := { s.sh with loopNest := s.sh.loopNest + 1 } }
    (.xsWhile "enter", s', .whileCond cond cond body none)

  | .whileCond origCond curCond origBody _savedEc =>
    match curCond with
    | .done =>
      if s.sh.exitCode == 0 then (.xsWhile "body", s, .whileRunning origCond origBody origBody)
      else
        let ec := match _savedEc with | some ec => ec | none => 0
        (.xsWhile "exit", exitWith ec { s with sh := { s.sh with loopNest := s.sh.loopNest - 1 } }, .done)
    | .exit_ => (.xsSimple "propagate-exit", s, .exit_)
    | .return_ => (.xsSimple "propagate-return", s, .return_)
    | .break_ n => (.xsSimple "propagate-break", s, .break_ n)
    | .continue_ n => (.xsSimple "propagate-continue", s, .continue_ n)
    | _ =>
      let (step, s', c') := stepEval s curCond
      match c' with
      | .done =>
        if s'.sh.exitCode == 0 then (.xsNested (.xsWhile "body") step, s', .whileRunning origCond origBody origBody)
        else
          let ec := match _savedEc with | some ec => ec | none => 0
          (.xsNested (.xsWhile "exit") step, exitWith ec { s' with sh := { s'.sh with loopNest := s'.sh.loopNest - 1 } }, .done)
      | .exit_ => (.xsNested (.xsWhile "propagate-exit") step, s', .exit_)
      | .return_ => (.xsNested (.xsWhile "propagate-return") step, s', .return_)
      | .break_ n => (.xsNested (.xsWhile "propagate-break") step, s', .break_ n)
      | .continue_ n => (.xsNested (.xsWhile "propagate-continue") step, s', .continue_ n)
      | _ => (.xsNested (.xsWhile "cond") step, s', .whileCond origCond c' origBody _savedEc)

  | .whileRunning origCond origBody curBody =>
    match curBody with
    | .done => (.xsWhile "loop", s, .whileCond origCond origCond origBody (some s.sh.exitCode))
    | .exit_ => (.xsSimple "propagate-exit", s, .exit_)
    | .return_ => (.xsSimple "propagate-return", s, .return_)
    | .break_ n =>
      if n ≤ 1 then
        -- Break loop: decrement loopNest and exit
        (.xsWhile "break-loop", { s with sh := { s.sh with loopNest := s.sh.loopNest - 1 } }, .done)
      else
        (.xsWhile "propagate-break", { s with sh := { s.sh with loopNest := s.sh.loopNest - 1 } }, .break_ (n - 1))
    | .continue_ n =>
      if n ≤ 1 then
        -- Continue loop: next iteration (condition)
        (.xsWhile "continue-loop", s, .whileCond origCond origCond origBody (some s.sh.exitCode))
      else
        (.xsWhile "propagate-continue", { s with sh := { s.sh with loopNest := s.sh.loopNest - 1 } }, .continue_ (n - 1))
    | _ =>
      let (step, s', c') := stepEval s curBody
      match c' with
      | .done => (.xsNested (.xsWhile "loop") step, s', .whileCond origCond origCond origBody (some s'.sh.exitCode))
      | .exit_ => (.xsNested (.xsWhile "propagate-exit") step, s', .exit_)
      | .return_ => (.xsNested (.xsWhile "propagate-return") step, s', .return_)
      | .break_ n =>
        if n ≤ 1 then (.xsNested (.xsWhile "break-loop") step, { s' with sh := { s'.sh with loopNest := s'.sh.loopNest - 1 } }, .done)
        else (.xsNested (.xsWhile "propagate-break") step, { s' with sh := { s'.sh with loopNest := s'.sh.loopNest - 1 } }, .break_ (n - 1))
      | .continue_ n =>
        if n ≤ 1 then (.xsNested (.xsWhile "continue-loop") step, s', .whileCond origCond origCond origBody (some s'.sh.exitCode))
        else (.xsNested (.xsWhile "propagate-continue") step, { s' with sh := { s'.sh with loopNest := s'.sh.loopNest - 1 } }, .continue_ (n - 1))
      | _ => (.xsNested (.xsWhile "body-step") step, s', .whileRunning origCond origBody c')

  -- For
  | .for_ var words body =>
    (.xsFor "expand", s, .forExpArgs var (.expStart { splitting := .split, globbing := true } words) body)

  | .forExpArgs var es body =>
    let (step, s', es') := stepExpansion (stepEval' s) s es
    match es' with
    | .expDone fs => (.xsFor "expanded", s', .forExpanded var fs body)
    | _ => (.xsFor "expanding", s', .forExpArgs var es' body)

  | .forExpanded var fs body =>
    let s' := { s with sh := { s.sh with loopNest := s.sh.loopNest + 1 } }
    match fs with
    | [] => (.xsFor "empty", { s' with sh := { s'.sh with loopNest := s'.sh.loopNest - 1 } }, .done)
    | val :: fs' =>
      let s'' := internalSetParam var val s'
      (.xsFor "start", s'', .forRunning var fs' body body)

  | .forRunning var fs origBody curBody =>
    match curBody with
    | .done =>
      match fs with
      | [] =>
        let s' := { s with sh := { s.sh with loopNest := s.sh.loopNest - 1 } }
        (.xsFor "done", s', .done)
      | val :: fs' =>
        let s' := internalSetParam var val s
        (.xsFor "next", s', .forRunning var fs' origBody origBody)
    | .exit_ => (.xsSimple "propagate-exit", s, .exit_)
    | .return_ => (.xsSimple "propagate-return", s, .return_)
    | .break_ n =>
      if n ≤ 1 then (.xsFor "break-loop", { s with sh := { s.sh with loopNest := s.sh.loopNest - 1 } }, .done)
      else (.xsFor "propagate-break", { s with sh := { s.sh with loopNest := s.sh.loopNest - 1 } }, .break_ (n - 1))
    | .continue_ n =>
      if n ≤ 1 then
        match fs with
        | [] => (.xsFor "continue-done", { s with sh := { s.sh with loopNest := s.sh.loopNest - 1 } }, .done)
        | val :: fs' =>
          let s' := internalSetParam var val s
          (.xsFor "continue-next", s', .forRunning var fs' origBody origBody)
      else
        (.xsFor "propagate-continue", { s with sh := { s.sh with loopNest := s.sh.loopNest - 1 } }, .continue_ (n - 1))
    | _ =>
      match fs with
      | [] =>
        let (step, s', c') := stepEval s curBody
        match c' with
        | .done =>
          -- Should effectively be done (loop empty)
           (.xsNested (.xsFor "body-done") step, { s' with sh := { s'.sh with loopNest := s'.sh.loopNest - 1 } }, .done) -- Weird case if fs empty but body running?
        | .exit_ => (.xsNested (.xsFor "propagate-exit") step, s', .exit_)
        | .return_ => (.xsNested (.xsFor "propagate-return") step, s', .return_)
        | .break_ n =>
           if n ≤ 1 then (.xsNested (.xsFor "break-loop") step, { s' with sh := { s'.sh with loopNest := s'.sh.loopNest - 1 } }, .done)
           else (.xsNested (.xsFor "propagate-break") step, { s' with sh := { s'.sh with loopNest := s'.sh.loopNest - 1 } }, .break_ (n - 1))
        | .continue_ n =>
           if n ≤ 1 then (.xsNested (.xsFor "continue-done") step, { s' with sh := { s'.sh with loopNest := s'.sh.loopNest - 1 } }, .done)
           else (.xsNested (.xsFor "propagate-continue") step, { s' with sh := { s'.sh with loopNest := s'.sh.loopNest - 1 } }, .continue_ (n - 1))
        | _ => (.xsNested (.xsFor "body") step, s', .forRunning var [] origBody c')
      | val :: fs' =>
        -- First iteration: set var and start body (wait, this logic was only for init? No, it's for `curBody` advancement)
        -- If `fs` is present, it means we are in the middle of iterations.
        -- But `curBody` is the active statement. `fs` is the REMAINING items.
        -- Wait, the original logic had `match fs` inside `_` case.
        -- `curBody` is the *current* execution. `fs` is the *future* items.
        -- If `curBody` steps, we keep `fs`.
        let (step, s', c') := stepEval s curBody
        match c' with
        | .done =>
           -- Current iteration finished. Move to next.
           match fs with
           | [] => (.xsNested (.xsFor "loop-finish") step, { s' with sh := { s'.sh with loopNest := s'.sh.loopNest - 1 } }, .done)
           | val' :: fs'' =>
             let s'' := internalSetParam var val' s'
             (.xsNested (.xsFor "loop-next") step, s'', .forRunning var fs'' origBody origBody)
        | .exit_ => (.xsNested (.xsFor "propagate-exit") step, s', .exit_)
        | .return_ => (.xsNested (.xsFor "propagate-return") step, s', .return_)
        | .break_ n =>
           if n ≤ 1 then (.xsNested (.xsFor "break-loop") step, { s' with sh := { s'.sh with loopNest := s'.sh.loopNest - 1 } }, .done)
           else (.xsNested (.xsFor "propagate-break") step, { s' with sh := { s'.sh with loopNest := s'.sh.loopNest - 1 } }, .break_ (n - 1))
        | .continue_ n =>
           if n ≤ 1 then
             match fs with
             | [] => (.xsNested (.xsFor "continue-finish") step, { s' with sh := { s'.sh with loopNest := s'.sh.loopNest - 1 } }, .done)
             | val' :: fs'' =>
               let s'' := internalSetParam var val' s'
               (.xsNested (.xsFor "continue-next") step, s'', .forRunning var fs'' origBody origBody)
           else (.xsNested (.xsFor "propagate-continue") step, { s' with sh := { s'.sh with loopNest := s'.sh.loopNest - 1 } }, .continue_ (n - 1))
        | _ => (.xsNested (.xsFor "body") step, s', .forRunning var (val :: fs') origBody c')

  -- Case
  | .case_ w cases =>
    (.xsCase "expand", s, .caseExpArg (.expStart { splitting := .noSplit, globbing := false } w) cases)

  | .caseExpArg es cases =>
    let (step, s', es') := stepExpansion (stepEval' s) s es
    match es' with
    | .expDone fs =>
      let ss := fs.flatMap id
      (.xsCase "match", s', .caseMatch ss cases)
    | _ => (.xsCase "expanding", s', .caseExpArg es' cases)

  | .caseMatch _ss [] => (.xsCase "no-match", s, .done)
  | .caseMatch ss ((pats, body) :: rest) =>
    match pats with
    | [] => (.xsCase "next-case", s, .caseMatch ss rest)
    | pat :: _pats' =>
      let es := ExpansionState.expStart { splitting := .noSplit, globbing := false } pat
      (.xsCase "testing", s, .caseCheckMatch ss es body rest)

  | .caseCheckMatch ss es body rest =>
    let (_step, s', es') := stepExpansion (stepEval' s) s es
    match es' with
    | .expDone fs =>
      let pat := fs.flatMap id
      match matchExact s'.sh.locale pat ss with
      | .match_ _ => (.xsCase "matched", s', body)
      | _ => (.xsCase "no-match", s', .caseMatch ss rest)
    | _ => (.xsCase "expanding-pat", s', .caseCheckMatch ss es' body rest)

  -- Defun
  | .defun name body =>
    let s' := { s with sh := { s.sh with funcs := (name, body) :: s.sh.funcs.filter (fun (n, _) => n != name) } }
    (.xsDefun "define", exitWith 0 s', .done)

  -- Call (function invocation)
  | .call outerLoopNest outerParams funcName origBody curBody =>
    match curBody with
    | .done =>
      let s' := { s with sh := { s.sh with loopNest := outerLoopNest, positionalParams := outerParams } }
      (.xsStack funcName (.xsSimple "return"), s', .done)
    | .return_ =>
      let s' := { s with sh := { s.sh with loopNest := outerLoopNest, positionalParams := outerParams } }
      (.xsStack funcName (.xsSimple "return"), s', .done)
    | _ =>
      let (step, s', c') := stepEval s curBody
      (.xsStack funcName step, s', .call outerLoopNest outerParams funcName origBody c')

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
      let (s2, pid) := OS.osForkAndSubshell s1 stmt' .fg none true
      (.xsSubshell s!"started subshell with pid {pid}",
       restoreFds s2 savedFds,
       .wait pid .unchecked none .waitInternal)

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

  -- Break / continue
  | .break_ n =>
    if n ≤ 1 then (.xsSimple "break", s, .done)
    else (.xsSimple "break-outer", s, .break_ (n - 1))

  | .continue_ n =>
    if n ≤ 1 then (.xsSimple "continue", s, .done)
    else (.xsSimple "continue-outer", s, .continue_ (n - 1))

  -- Return
  | .return_ => (.xsSimple "return", s, .done)

  -- Exit
  | .exit_ => (.xsSimple "exit", s, .done)

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
    | _ =>
      let (_step, s', c') := stepEval s handler
      (.xsTrap signal "handler", s', .trapped signal ec c' cont)

  -- Checked exit
  | .checkedExit stmt =>
    match stmt with
    | .done =>
      if s.sh.exitCode != 0 && s.sh.opts.any (· == .errexit) then
        (.xsSimple "errexit", s, .exit_)
      else
        (.xsSimple "checked-done", s, .done)
    | _ =>
      let (_step, s', c') := stepEval s stmt
      (.xsSimple "checking", s', .checkedExit c')

  -- Pushredir
  | .pushredir stmt saved =>
    match stmt with
    | .done =>
      let s' := restoreFds s saved
      (.xsRedir "restore", s', .done)
    | _ =>
      let (_step, s', c') := stepEval s stmt
      (.xsRedir "body", s', .pushredir c' saved)

  -- EvalLoop
  | .evalLoop linno _ctx src _mode _level =>
    (.xsEval linno src "eval-loop", s, .done)

  | .evalLoopCmd linno _ctx src _mode _level cmd =>
    match cmd with
    | .done => (.xsEval linno src "next", s, .evalLoop (linno + 1) _ctx src _mode _level)
    | _ =>
      let (_step, s', c') := stepEval s cmd
      (.xsEval linno src "running", s', .evalLoopCmd linno _ctx src _mode _level c')


  -- Simple command execution (invoked via runCommand dispatch)
  | .exec path prog args env binsh =>
    -- Dispatch via Shell typeclass
    Shell.runCommand s { shouldFork := false, ranCmdSubst := false, forceSimpleCommand := false } .unchecked prog args env []

  | .commandExpAssign ((x, es) :: assigns) args savedFds opts =>
    let (step, s', es') := stepExpansion (stepEval' s) s es
    match es' with
    | .expDone f =>
      match forceLocalParam s' x (symbolicStringOfFields f) with
      | Sum.inl err =>
        let s'' := safeWriteStderr (err ++ "\n") s'
        (.xsSimple "assignment error", exitWith 2 s'', Stmt.done)
      | Sum.inr s'' =>
        (.xsSimple ("assign " ++ x), s'', .commandExpAssign assigns args savedFds opts)
    | .expError f =>
      let errMsg := String.join (f.map (fun field => String.join (field.map (fun c => match c with | .c ch => String.ofList [ch] | .sym _ => "?"))))
      (.xsSimple "assignment expansion error", failWith errMsg s', Stmt.done)
    | _ =>
      (.xsExpand (.xsSimple "") step, s', .commandExpAssign ((x, es') :: assigns) args savedFds opts)

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
      (.xsSimple "finished assignments w/o command, popping redirects", s4, Stmt.done)
    | cmd :: argv =>
      (.xsSimple "assignments fully expanded", s1, .commandReady assigns cmd argv savedFds opts)

  -- CommandReady: dispatch command
  | .commandReady assigns prog args savedFds opts =>
    if s.sh.opts.any (· == .noexec) then
      (.xsSimple "set -n: skipping command", s, Stmt.done)
    else
      let (s0, _concretizedSS, progName) := concretize s prog
      -- For special builtins, apply assignments to current environment
      let s1 :=
        if isSpecialBuiltinName progName && !opts.forceSimpleCommand
        then assigns.foldr (fun (x, v) os => checkedSetParam x v os) s0
        else s0
      -- Try to find a function
      match s1.sh.funcs.find? (fun (n, _) => n == progName) with
      | some (_, body) =>
        -- Function call
        let outerLoopNest := s1.sh.loopNest
        let outerParams := s1.sh.positionalParams
        let newParams := prog :: args.map id
        let s2 := { s1 with sh := { s1.sh with
          positionalParams := newParams,
          loopNest := 0,
          locals := [] :: s1.sh.locals } }
        (.xsSimple "function-call", s2, pushredir' (.call outerLoopNest outerParams progName body body) savedFds)
      | none =>
        -- No function found - just mark as external/builtin dispatch
        -- Full dispatch is in Command.lean which wraps stepEval
        (.xsSimple "command-dispatch", s1, pushredir' (.exec (symbolicStringOfString progName) prog (args.map id) assigns .tryBinSh) savedFds)

where
  stepEval' (_s : OsState α) : StepFun α := fun os stmt =>
    let (_step, os', stmt') := stepEval os stmt
    (os', match stmt' with | .done => .inr (some os'.sh.exitCode) | _ => .inl (_step, stmt'))

end Semantics
