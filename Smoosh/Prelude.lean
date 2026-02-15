/-
  Smoosh.Prelude — Core types, AST, shell state, and helpers
  Translated from smoosh_prelude.lem (2365 lines)
-/
import Smoosh.Num
import Smoosh.Signal

/-! # Utility Functions -/

def alphabetic : List Char :=
  "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ".toList

def alphanumerics : List Char :=
  "0123456789".toList ++ alphabetic

def isAlpha (c : Char) : Bool := c ∈ alphabetic
def isAlphanumeric (c : Char) : Bool := c ∈ alphanumerics
def isVariableInitialChar (c : Char) : Bool := isAlpha c || c == '_'
def isVariableChar (c : Char) : Bool := isAlphanumeric c || c == '_'

def uppercase (s : String) : String :=
  String.ofList (s.toList.map uppercaseChar)

def parens (s : String) : String := "( " ++ s ++ " )"

def tails : List α → List (List α)
  | [] => [[]]
  | xs@(_ :: xs') => xs :: tails xs'

def insertBy (lte : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys' => if lte x y then x :: y :: ys' else y :: insertBy lte x ys'

def sortBy' (lte : α → α → Bool) (xs : List α) : List α :=
  xs.foldr (insertBy lte) []

def collectEither : List (Sum α β) → List α × List β
  | [] => ([], [])
  | .inl a :: l' =>
    let (lefts, rights) := collectEither l'
    (a :: lefts, rights)
  | .inr b :: l' =>
    let (lefts, rights) := collectEither l'
    (lefts, b :: rights)

def isInfixOf [BEq α] (needle haystack : List α) : Bool :=
  (tails haystack).any (needle.isPrefixOf ·)

def replace' [BEq α] (lold lnew lorig : List α) : List α :=
  if lorig.isPrefixOf lold then lnew ++ lorig.drop lold.length
  else match lorig with
    | [] => []
    | x :: lorig' => x :: replace' lold lnew lorig'

def replaceString (sold snew sorig : String) : String :=
  String.ofList (replace' sold.toList snew.toList sorig.toList)

def ltrimNewlines : List Char → List Char
  | [] => []
  | '\n' :: cl' => ltrimNewlines cl'
  | cl => cl

def intersperse' (sep : α) : List α → List α
  | [] => []
  | [x] => [x]
  | x :: xs' => x :: sep :: intersperse' sep xs'

def trimrOneNewline (s : String) : String :=
  let cl := s.toList
  match cl.reverse with
  | [] => ""
  | '\n' :: cl' => String.ofList cl'.reverse
  | _ => s

def trimrNewlines (s : String) : String :=
  let cl := s.toList
  String.ofList (ltrimNewlines cl.reverse).reverse

def padLeftWith (c : Char) (s : String) (len : Nat) : String :=
  let padding := len - s.length
  String.ofList (List.replicate padding c) ++ s

def padRightWith (c : Char) (s : String) (len : Nat) : String :=
  let padding := len - s.length
  s ++ String.ofList (List.replicate padding c)

def padLeft := padLeftWith ' '
def padRight := padRightWith ' '

def maximum' [Max α] : List α → Option α
  | [] => none
  | [x] => some x
  | x :: xs' => (maximum' xs').map (max x)

def break' (p : α → Bool) : List α → List α × List α
  | [] => ([], [])
  | x :: xs =>
    if p x then ([], x :: xs)
    else let (xs', xs'') := break' p xs; (x :: xs', xs'')

def spaced (s1 s2 : String) : String :=
  let sep := if s1 != "" && s2 != "" then " " else ""
  s1 ++ sep ++ s2

def spacedMany : List String → String
  | [] => ""
  | [s] => s
  | s :: ss' => spaced s (spacedMany ss')

def breakOnEsc (escapable : Bool) (sep : Char) : List Char → List Char × List Char
  | [] => ([], [])
  | '\\' :: c :: cs =>
    if escapable then
      let (cs', cs'') := breakOnEsc escapable sep cs
      ('\\' :: c :: cs', cs'')
    else
      if sep == '\\' then ([], c :: cs)
      else
        let (cs', cs'') := breakOnEsc escapable sep (c :: cs)
        ('\\' :: cs', cs'')
  | c :: cs =>
    if sep == c then ([], cs)
    else let (cs', cs'') := breakOnEsc escapable sep cs; (c :: cs', cs'')

def splitOn (escapable : Bool) (sep : Char) : List Char → List (List Char)
  | cs =>
    match breakOnEsc escapable sep cs with
    | ([], []) => []
    | (cs', []) => [cs']
    | (cs', cs'') => cs' :: splitOn escapable sep cs''
termination_by cs => cs.length
decreasing_by all_goals sorry

def splitStringOn (escapable : Bool) (sep : Char) (s : String) : List String :=
  (splitOn escapable sep s.toList).map String.ofList

def adjustNth (l : List α) (n : Nat) (f : α → α × β) : Option (List α × β) :=
  match l, n with
  | [], _ => none
  | v :: l', 0 =>
    let (v', res) := f v
    some (v' :: l', res)
  | v :: l', n + 1 =>
    match adjustNth l' n f with
    | none => none
    | some (l'', res) => some (v :: l'', res)

/-! # Locales -/

inductive RangeChar where
  | rchar (c : Char)
  | rcollating (s : String)
  deriving Repr, BEq

structure Locale where
  name : String
  collates : Char → String → Bool
  equiv : Char → String → Bool
  charclass : Char → String → Bool
  range : Char → RangeChar → RangeChar → Bool

def between (lo c hi : Nat) : Bool := lo ≤ c && c ≤ hi

def ambientCharclass (c : Char) (cls : String) : Bool :=
  match cls with
  | "alnum" => ambientCharclass c "alpha" || ambientCharclass c "digit"
  | "alpha" => ambientCharclass c "upper" || ambientCharclass c "lower"
  | "blank" => c == ' ' || c == '\t'
  | "cntrl" => c.toNat < ' '.toNat || c.toNat == 127
  | "digit" => '0' ≤ c && c ≤ '9'
  | "graph" => ambientCharclass c "alnum" || ambientCharclass c "punct"
  | "lower" => between 'a'.toNat c.toNat 'z'.toNat
  | "print" => ambientCharclass c "graph" || c == ' '
  | "punct" => "!\"#$%&'()*+,-./:;<=>?@[\\]^_{}~|".toList.contains c
  | "space" => c == ' ' || c == '\t' || c == '\n' || c == '\r' || c.toNat == 11 || c.toNat == 14
  | "upper" => between 'A'.toNat c.toNat 'Z'.toNat
  | "xdigit" => "0123456789ABCDEFabcdef".toList.contains c
  | _ => false
termination_by cls.length
decreasing_by all_goals sorry

def lcAmbient : Locale :=
  let collates (c : Char) (cls : String) : Bool := cls.toList.contains c
  let equiv (c : Char) (cls : String) : Bool := cls.toList.contains c
  let rchar : RangeChar → Option Char
    | .rchar c => some c
    | .rcollating s =>
      match s.toList with
      | [c] => some c
      | _ => none
  let range' (c : Char) (rlo rhi : RangeChar) : Bool :=
    match rchar rlo, rchar rhi with
    | some lo, some hi => between lo.toNat c.toNat hi.toNat
    | _, _ => false
  { name := "ambient", collates := collates, equiv := equiv,
    charclass := ambientCharclass, range := range' }

/-! # File Permissions -/

inductive FilePerm where
  | read | write | execute
  deriving Repr, BEq, Hashable, DecidableEq, Ord

structure Perms where
  setuid : Bool
  setgid : Bool
  sticky : Bool
  user   : List FilePerm
  group  : List FilePerm
  other  : List FilePerm
  deriving Repr, BEq

def permsAllClear : Perms :=
  { setuid := false, setgid := false, sticky := false,
    user := [], group := [], other := [] }

def allFilePerms : List FilePerm := [.read, .write, .execute]

def defaultUmask : Perms :=
  { setuid := false, setgid := false, sticky := false,
    user := [], group := [.write], other := [.write] }

def invertFilePerms (fperms : List FilePerm) : List FilePerm :=
  allFilePerms.filter (fun p => !fperms.contains p)

def invertPerms (perms : Perms) : Perms :=
  { setuid := !perms.setuid, setgid := !perms.setgid, sticky := !perms.sticky,
    user := invertFilePerms perms.user,
    group := invertFilePerms perms.group,
    other := invertFilePerms perms.other }

def natOfFilePerms (fperms : List FilePerm) : Nat :=
  let bit0 := if fperms.contains .execute then 1 else 0
  let bit1 := if fperms.contains .write then 2 else 0
  let bit2 := if fperms.contains .read then 4 else 0
  bit0 + bit1 + bit2

def filePermsOfNat (n : Nat) : List FilePerm :=
  let r := if hasBit n 0 then [FilePerm.execute] else []
  let w := if hasBit n 1 then [FilePerm.write] else []
  let x := if hasBit n 2 then [FilePerm.read] else []
  r ++ w ++ x

def permsOfNat (n : Nat) : Perms :=
  { other := filePermsOfNat n,
    group := filePermsOfNat (n / 8),
    user := filePermsOfNat (n / 64),
    sticky := hasBit n 9,
    setgid := hasBit n 10,
    setuid := hasBit n 11 }

def natOfPerms (perms : Perms) : Nat :=
  let bit0 := if perms.sticky then 1 else 0
  let bit1 := if perms.setgid then 2 else 0
  let bit2 := if perms.setuid then 4 else 0
  let first := bit0 + bit1 + bit2
  let second := natOfFilePerms perms.user
  let third := natOfFilePerms perms.group
  let fourth := natOfFilePerms perms.other
  (2^9 * first) + (2^6 * second) + (2^3 * third) + fourth

def stringOfFilePerms (fperms : List FilePerm) : String :=
  let r := if fperms.contains .read then "r" else ""
  let w := if fperms.contains .write then "w" else ""
  let x := if fperms.contains .execute then "x" else ""
  r ++ w ++ x

def stringOfPerms (perms : Perms) : String :=
  let u := stringOfFilePerms perms.user
  let g := stringOfFilePerms perms.group
  let o := stringOfFilePerms perms.other
  s!"u={u},g={g},o={o}"

/-! # Symbolic chmod types -/

inductive PermsWho where | whoU | whoG | whoO
  deriving Repr, BEq, DecidableEq, Hashable, Ord

def permsWholistAll : List PermsWho := [.whoU, .whoG, .whoO]

inductive PermsFlag where
  | permR | permW | permX | permBigX | permS | permT
  deriving Repr, BEq, DecidableEq, Hashable, Ord

inductive PermsOp where | opPlus | opMinus | opEqual
  deriving Repr, BEq

inductive PermsAction where
  | actOp (op : PermsOp)
  | actPerms (op : PermsOp) (flags : List PermsFlag)
  | actCopy (op : PermsOp) (who : PermsWho)
  deriving Repr, BEq

def PermsClause := List PermsWho × List PermsAction
def PermsSymbolic := List PermsClause

/-! # Shell Options -/

inductive TraceTag where
  | symbolic | syscall | traps | undef | unspec
  deriving Repr, BEq, DecidableEq, Hashable, Ord

def TraceTag.toString : TraceTag → String
  | .symbolic => "symbolic"
  | .syscall  => "syscall"
  | .traps    => "traps"
  | .undef    => "undef"
  | .unspec   => "unspec"

def TraceTag.ofString : String → Option TraceTag
  | "symbolic" => some .symbolic
  | "syscall"  => some .syscall
  | "traps"    => some .traps
  | "undef"    => some .undef
  | "unspec"   => some .unspec
  | _ => none

inductive ShOpt where
  | allexport | errexit | ignoreeof | earlyhash | interactive
  | monitor | noclobber | noglob | noexec | nolog | notify
  | nounset | verbose | vi | xtrace
  | nonlexicalctrl
  | trace (tag : TraceTag)
  deriving Repr, BEq

def ShOpt.toString : ShOpt → String
  | .allexport      => "allexport"
  | .errexit        => "errexit"
  | .ignoreeof      => "ignoreeof"
  | .earlyhash      => "earlyhash"
  | .interactive    => "interactive"
  | .monitor        => "monitor"
  | .noclobber      => "noclobber"
  | .noglob         => "noglob"
  | .noexec         => "noexec"
  | .nolog          => "nolog"
  | .notify         => "notify"
  | .nounset        => "nounset"
  | .verbose        => "verbose"
  | .vi             => "vi"
  | .xtrace         => "xtrace"
  | .nonlexicalctrl => "nonlexicalctrl"
  | .trace tag      => "trace" ++ tag.toString

def ShOpt.charOfShOpt : ShOpt → Option Char
  | .allexport   => some 'a'
  | .errexit     => some 'e'
  | .earlyhash   => some 'h'
  | .interactive => some 'i'
  | .monitor     => some 'm'
  | .noclobber   => some 'C'
  | .noglob      => some 'f'
  | .noexec      => some 'n'
  | .notify      => some 'b'
  | .nounset     => some 'u'
  | .verbose     => some 'v'
  | .xtrace      => some 'x'
  | _ => none

def ShOpt.ofShortopt : Char → Option ShOpt
  | 'a' => some .allexport
  | 'b' => some .notify
  | 'C' => some .noclobber
  | 'e' => some .errexit
  | 'f' => some .noglob
  | 'h' => some .earlyhash
  | 'm' => some .monitor
  | 'n' => some .noexec
  | 'u' => some .nounset
  | 'v' => some .verbose
  | 'x' => some .xtrace
  | _ => none

def ShOpt.ofLongopt : String → Option ShOpt
  | "allexport"      => some .allexport
  | "errexit"        => some .errexit
  | "ignoreeof"      => some .ignoreeof
  | "monitor"        => some .monitor
  | "noclobber"      => some .noclobber
  | "noglob"         => some .noglob
  | "noexec"         => some .noexec
  | "nolog"          => some .nolog
  | "notify"         => some .notify
  | "nounset"        => some .nounset
  | "verbose"        => some .verbose
  | "xtrace"         => some .xtrace
  | "vi"             => some .vi
  | "nonlexicalctrl" => some .nonlexicalctrl
  | "interactive"    => some .interactive
  | _                => none

/-! # Modes and flags -/

inductive SubstringMode where | shortest | longest
  deriving Repr, BEq

inductive SubstringSide where | prefix_ | suffix_
  deriving Repr, BEq

inductive RedirType where | to | clobber | from_ | fromTo | append
  deriving Repr, BEq

inductive DupType where | toFD | fromFD
  deriving Repr, BEq

inductive HeredocType where | here | xhere
  deriving Repr, BEq

inductive OrigFdAction where | closeOrig | leaveOrig
  deriving Repr, BEq

def OrigFdAction.shouldClose : OrigFdAction → Bool
  | .closeOrig => true
  | .leaveOrig => false

structure CommandOpts where
  ranCmdSubst : Bool
  shouldFork : Bool
  forceSimpleCommand : Bool
  deriving Repr, BEq

inductive SplittingMode where | split | noSplit
  deriving Repr, BEq

def SplittingMode.shouldSplit : SplittingMode → Bool
  | .split => true
  | .noSplit => false

structure ExpansionOpts where
  splitting : SplittingMode
  globbing : Bool
  deriving Repr, BEq

inductive BgMode where | fg | bg
  deriving Repr, BEq

def BgMode.isFg : BgMode → Bool
  | .fg => true
  | .bg => false

def BgMode.isBg : BgMode → Bool
  | .bg => true
  | .fg => false

inductive InteractivityMode where | interactive | noninteractive
  deriving Repr, BEq

def InteractivityMode.isInteractive : InteractivityMode → Bool
  | .interactive => true
  | .noninteractive => false

inductive ShellLevel where | toplevel | subsidiary
  deriving Repr, BEq

def ShellLevel.isToplevel : ShellLevel → Bool
  | .toplevel => true
  | .subsidiary => false

inductive BinshMode where | tryBinSh | noBinSh
  deriving Repr, BEq

inductive CheckingMode where | checked | unchecked
  deriving Repr, BEq

def CheckingMode.checkedExit : CheckingMode → Bool
  | .checked => true
  | .unchecked => false

inductive WaitMode where | waitCommand | waitInternal
  deriving Repr, BEq

inductive ParseStringMode where | parseEval | parseTrap
  deriving Repr, BEq

inductive ParseFileMode where | pushFile | noPushFile
  deriving Repr, BEq

inductive ParseSource where
  | parseSTDIN
  | parseString (mode : ParseStringMode) (s : String)
  | parseFile (path : String) (mode : ParseFileMode)
  deriving Repr, BEq

/-! # Core types (aliases) -/

abbrev Pid := Nat
abbrev Fd := Nat
abbrev Path := String

-- Opaque FFI types (stubbed)
inductive Stackmark where | unit
  deriving Repr, BEq

inductive DashString where | unit
  deriving Repr, BEq

/-! # AST — Massive Mutual Inductive -/
-- This corresponds to the core of smoosh_prelude.lem lines 880-1078
-- All types refer to each other, requiring a mutual block.

mutual

inductive Format where
  | normal
  | default_ (w : List Entry)
  | ndefault (w : List Entry)
  | assign (w : List Entry)
  | nassign (w : List Entry)
  | error (w : List Entry)
  | nerror (w : List Entry)
  | alt (w : List Entry)
  | nalt (w : List Entry)
  | length_
  | substring (side : SubstringSide) (mode : SubstringMode) (w : List Entry)

inductive Control where
  | tilde (s : String)
  | param (s : String) (f : Format)
  | lassign (s : String) (ew : List ExpandedWord) (w : List Entry)
  | lmatch (fs : List (List SymbolicChar)) (side : SubstringSide) (mode : SubstringMode) (ew : List ExpandedWord) (w : List Entry)
  | lerror (s : String) (ew : List ExpandedWord) (w : List Entry)
  | backtick (c : Stmt)
  | lbacktick (c : Stmt) (pid : Pid) (fd : Fd)
  | lbacktickWait (c : Stmt) (pid : Pid) (result : String)
  | arith (ew : List ExpandedWord) (w : List Entry)
  | quote (ew : List ExpandedWord) (w : List Entry)
  | escape (c : Char)

inductive Entry where
  | s (str : String)
  | k (ctrl : Control)
  | f
  | esym (sym : Sym)

inductive Stmt where
  | command (assigns : List (String × List Entry)) (args : List Entry) (redirs : List Redir) (opts : CommandOpts)
  | commandExpArgs (assigns : List (String × List Entry)) (es : ExpansionState) (redirs : List Redir) (opts : CommandOpts)
  | commandExpRedirs (assigns : List (String × List Entry)) (fs : List (List SymbolicChar)) (rs : List ExpandedRedir × Option ExpandingRedir × List Redir) (opts : CommandOpts)
  | commandExpAssign (assigns : List (String × ExpansionState)) (fs : List (List SymbolicChar)) (savedFds : List (Fd × Sum Fd Unit)) (opts : CommandOpts)
  | commandReady (assigns : List (String × List SymbolicChar)) (cmd : List SymbolicChar) (args : List (List SymbolicChar)) (savedFds : List (Fd × Sum Fd Unit)) (opts : CommandOpts)
  | pipe (mode : BgMode) (cmds : List Stmt)
  | redir (stmt : Stmt) (rs : List ExpandedRedir × Option ExpandingRedir × List Redir)
  | background (stmt : Stmt) (rs : List ExpandedRedir × Option ExpandingRedir × List Redir)
  | subshell (stmt : Stmt) (rs : List ExpandedRedir × Option ExpandingRedir × List Redir)
  | and_ (s1 s2 : Stmt)
  | or_ (s1 s2 : Stmt)
  | not_ (s : Stmt)
  | semi (s1 s2 : Stmt)
  | if_ (cond then_ else_ : Stmt)
  | while_ (cond body : Stmt)
  | whileCond (origCond curCond origBody : Stmt) (savedEc : Option Nat)
  | whileRunning (origCond origBody curBody : Stmt)
  | for_ (var : String) (words : List Entry) (body : Stmt)
  | forExpArgs (var : String) (es : ExpansionState) (body : Stmt)
  | forExpanded (var : String) (fs : List (List SymbolicChar)) (body : Stmt)
  | forRunning (var : String) (fs : List (List SymbolicChar)) (origBody curBody : Stmt)
  | case_ (w : List Entry) (cases : List (List (List Entry) × Stmt))
  | caseExpArg (es : ExpansionState) (cases : List (List (List Entry) × Stmt))
  | caseMatch (ss : List SymbolicChar) (cases : List (List (List Entry) × Stmt))
  | caseCheckMatch (ss : List SymbolicChar) (es : ExpansionState) (cmd : Stmt) (rest : List (List (List Entry) × Stmt))
  | defun (name : String) (body : Stmt)
  | call (outerLoopNest : Nat) (outerParams : List (List SymbolicChar)) (funcName : String) (origBody curBody : Stmt)
  | evalLoop (linno : Nat) (ctx : Option DashString × Option Stackmark) (src : ParseSource) (mode : InteractivityMode) (level : ShellLevel)
  | evalLoopCmd (linno : Nat) (ctx : Option DashString × Option Stackmark) (src : ParseSource) (mode : InteractivityMode) (level : ShellLevel) (cmd : Stmt)
  | break_ (n : Nat)
  | continue_ (n : Nat)
  | return_
  | exit_
  | exec (cmdPath cmdName : List SymbolicChar) (args : List (List SymbolicChar)) (env : List (String × List SymbolicChar)) (binsh : BinshMode)
  | wait (pid : Pid) (check : CheckingMode) (steps : Option Nat) (mode : WaitMode)
  | trapped (signal : Signal) (ec : Nat) (handler cont : Stmt)
  | checkedExit (stmt : Stmt)
  | pushredir (stmt : Stmt) (saved : List (Fd × Sum Fd Unit))
  | done

inductive Redir where
  | rfile (ty : RedirType) (fd : Nat) (w : List Entry)
  | rdup (ty : DupType) (fd : Nat) (w : List Entry)
  | rheredoc (ty : HeredocType) (fd : Nat) (w : List Entry)

inductive ExpandingRedir where
  | xrFile (ty : RedirType) (fd : Nat) (es : ExpansionState)
  | xrDup (ty : DupType) (fd : Nat) (es : ExpansionState)
  | xrHeredoc (ty : HeredocType) (fd : Nat) (es : ExpansionState)

inductive ExpandedRedir where
  | erFile (ty : RedirType) (fd : Nat) (ss : List SymbolicChar)
  | erDup (ty : DupType) (origAction : OrigFdAction) (fd : Nat) (tgt : Option Nat)
  | erHeredoc (ty : HeredocType) (fd : Nat) (ss : List SymbolicChar)

inductive ExpandedWord where
  | usrF
  | expS (s : String)
  | usrS (s : String)
  | at_ (fs : List (List SymbolicChar))
  | dquo (ss : List SymbolicChar)
  | ewSym (sym : Sym)

inductive TmpField where
  | wfs
  | fs
  | field (ss : List SymbolicChar)
  | qfield (ss : List SymbolicChar)

inductive Sym where
  | symArith (fs : List (List SymbolicChar))
  | symCommand (stmt : Stmt)
  | symPat (side : SubstringSide) (mode : SubstringMode) (pat str : List SymbolicChar)

inductive SymbolicChar where
  | c (ch : Char)
  | q (ch : Char)
  | sym (s : Sym)
  deriving Repr, BEq

inductive ExpansionState where
  | expStart (opts : ExpansionOpts) (w : List Entry)
  | expExpand (opts : ExpansionOpts) (ew : List ExpandedWord) (w : List Entry)
  | expSplit (opts : ExpansionOpts) (ew : List ExpandedWord)
  | expPath (opts : ExpansionOpts) (ifs : List TmpField)
  | expQuote (opts : ExpansionOpts) (ifs : List TmpField)
  | expError (fs : List (List SymbolicChar))
  | expDone (fs : List (List SymbolicChar))

end

deriving instance Repr for Format, Control, Entry, Stmt, Redir, ExpandingRedir, ExpandedRedir, ExpandedWord, TmpField, Sym, SymbolicChar, ExpansionState

instance : Inhabited Stmt := ⟨.done⟩

/-! # Step types — separate (smaller) mutual block -/
-- These types reference Stmt but nothing in the core block references them.

mutual

inductive ExpansionStep where
  | esTilde (s : String)
  | esParam (s : String)
  | esCommand (s : String)
  | esArith (s : String)
  | esSplit (s : String)
  | esPath (s : String)
  | esQuote (s : String)
  | esEscape (s : String)
  | esStep (s : String)
  | esNested (outer inner : ExpansionStep)
  | esEval (step : ExpansionStep) (evalStep : EvaluationStep)

inductive EvaluationStep where
  | xsSimple (s : String)
  | xsPipe (s : String)
  | xsRedir (s : String)
  | xsBackground (s : String)
  | xsSubshell (s : String)
  | xsAnd (s : String)
  | xsOr (s : String)
  | xsNot (s : String)
  | xsSemi (s : String)
  | xsIf (s : String)
  | xsWhile (s : String)
  | xsFor (s : String)
  | xsCase (s : String)
  | xsDefun (s : String)
  | xsStack (name : String) (step : EvaluationStep)
  | xsStep (s : String)
  | xsExec (s : String)
  | xsEval (linno : Nat) (src : ParseSource) (s : String)
  | xsWait (s : String)
  | xsTrap (signal : Signal) (s : String)
  | xsProc (pid : Pid) (stmt : Stmt)
  | xsNested (outer inner : EvaluationStep)
  | xsExpand (step : EvaluationStep) (eStep : ExpansionStep)

end

/-! # ParseResult — standalone, after mutual blocks -/

inductive ParseResult where
  | parseDone
  | parseError (s : String)
  | parseNull
  | parseStmt (s : Stmt)

/-! # Type abbreviations (after mutual block) -/

abbrev Words := List Entry
abbrev ExpandedWords := List ExpandedWord
abbrev SymbolicString := List SymbolicChar
abbrev Fields := List SymbolicString
abbrev IntermediateFields := List TmpField
abbrev RedirState := List ExpandedRedir × Option ExpandingRedir × List Redir
abbrev SavedFdInfo := Sum Fd Unit  -- Saved fd | Close
abbrev SavedFds := List (Fd × SavedFdInfo)
abbrev Env := List (String × SymbolicString)
abbrev ParseContext := Option DashString × Option Stackmark

-- BEq for SymbolicChar (needed for symbolic string comparison)
-- We compare structurally: concrete chars are easy; symbolic parts compare false
mutual
def beqSymbolicChar : SymbolicChar → SymbolicChar → Bool
  | .c c1, .c c2 => c1 == c2
  | .q c1, .q c2 => c1 == c2
  | _, _ => false  -- symbolic parts don't compare equal
end

instance : BEq SymbolicChar where
  beq := beqSymbolicChar

instance : BEq (List SymbolicChar) where
  beq a b := a.length == b.length && (a.zip b).all (fun (x, y) => beqSymbolicChar x y)


/-! # Shell state types -/

inductive JobStopped where | tstp | stop | ttin | ttou
  deriving Repr, BEq

inductive JobStatus where
  | jobRunning
  | jobStopped (reason : JobStopped)
  | jobTerminated (signal : Signal)
  | jobDone (ec : Nat)
  deriving Repr, BEq

abbrev PipelineInfo := List (Pid × Stmt)

structure JobInfo where
  id : Nat
  pipeline : PipelineInfo
  pid : Pid
  cmd : Stmt
  status : JobStatus

structure LocalOpts where
  localReadonly : Bool
  localExported : Bool
  deriving Repr, BEq

abbrev LocalEnv := List (String × (Option SymbolicString × LocalOpts))

abbrev History := List (Nat × Stmt)

structure ShellState where
  rootpid : Pid
  outermost : Bool
  opts : List ShOpt
  traps : List (Signal × SymbolicString)
  supershellTraps : Option (List (Signal × SymbolicString))
  jobs : List JobInfo := []
  lastPid : Option Pid
  exitCode : Nat
  positionalParams : List SymbolicString  -- $0, $1, $2, ...
  env : Env
  locals : List LocalEnv
  optoff : Option Nat
  readonly : List String
  export_ : List String
  funcs : List (String × Stmt)
  aliases : List (String × String)
  cwd : String
  locale : Locale
  loopNest : Nat
  history : History
  hashes : List (String × (Path × Nat))

/-! # Standard FDs -/

def STDIN  : Fd := 0
def STDOUT : Fd := 1
def STDERR : Fd := 2

/-! # Symbolic string functions -/

def firstIsSlash (path : Path) : Bool :=
  match path.toList with
  | '/' :: _ => true
  | _ => false

def lastIsSlash (path : Path) : Bool :=
  path != "" && (path.toList.getLast? |>.getD ' ') == '/'

def joinPath (root ext : Path) : Path :=
  root ++ (if lastIsSlash root then "" else "/") ++ ext

def symbolicStringOfString (s : String) : SymbolicString :=
  s.toList.map .c

def quotedSymbolicStringOfString (s : String) : SymbolicString :=
  s.toList.map .q

def symbolicStringOfNat (n : Nat) : SymbolicString :=
  symbolicStringOfString (Nat.repr n)

def tryConcrete : SymbolicString → Option String
  | [] => some ""
  | .c ch :: vs' => do
    let cs ← tryConcrete vs'
    some (String.ofList [ch] ++ cs)
  | .q ch :: vs' => do
    let cs ← tryConcrete vs'
    some (String.ofList [ch] ++ cs)
  | .sym _ :: _ => none

def fieldsOfSymbolicString (s : SymbolicString) : Fields := [s]

/-! # Default values -/

def defaultCmdOpts : CommandOpts :=
  { ranCmdSubst := false, shouldFork := true, forceSimpleCommand := false }

def localOptsDefault : LocalOpts :=
  { localReadonly := false, localExported := false }

/-! # Helper functions -/

def isSpecialParam (x : String) : Bool :=
  match readNat x.toList with
  | .ok _ => true
  | .error _ => x ∈ ["@", "*", "#", "?", "-", "$", "!"]

def assignsOfEnv (env : Env) : List (String × SymbolicString) := env

def sequence' : List Stmt → Stmt
  | [] => .done
  | [stmt] => stmt
  | stmt :: stmts' => .semi stmt (sequence' stmts')

def simpleCommand (cmd : String) (args : Fields) (env : Env) : Stmt :=
  .commandReady (assignsOfEnv env) (symbolicStringOfString cmd) args []
    { defaultCmdOpts with ranCmdSubst := true }

def skip : Stmt := simpleCommand ":" [] []

def commandEval (cmd : SymbolicString) : Stmt :=
  simpleCommand "eval" [cmd] []

def isTerminatingControl : Stmt → Bool
  | .exit_ => true
  | .return_ => true
  | .break_ _ => true
  | .continue_ _ => true
  | .done => true
  | _ => false

def isActiveJob (job : JobInfo) : Bool :=
  match job.status with
  | .jobRunning => true
  | .jobStopped _ => true
  | .jobTerminated _ => false
  | .jobDone _ => false

def stringOfJobStatus : JobStatus → String
  | .jobRunning => "Running"
  | .jobStopped .tstp => "Stopped (SIGTSTP)"
  | .jobStopped .stop => "Stopped (SIGSTOP)"
  | .jobStopped .ttin => "Stopped (SIGTTIN)"
  | .jobStopped .ttou => "Stopped (SIGTTOU)"
  | .jobTerminated signal => s!"Terminated ({signal.toString})"
  | .jobDone 0 => "Done"
  | .jobDone code => s!"Done ({code})"

inductive JobsMode where
  | jobsNormal | jobsTerse | jobsLong | jobsFGCommand | jobsBGCommand
  deriving Repr, BEq

/-! # Default shell state -/

def defaultShellState : ShellState :=
  { rootpid := 0,
    outermost := true,
    opts := [],
    traps := [],
    supershellTraps := none,
    jobs := [],
    exitCode := 0,
    lastPid := none,
    positionalParams := [symbolicStringOfString "smoosh"],
    env := [("OPTIND", symbolicStringOfString "1"),
            ("HOME", symbolicStringOfString "/home/user"),
            ("IFS", symbolicStringOfString " \t\n"),
            ("PWD", symbolicStringOfString "/")],
    locals := [],
    optoff := none,
    readonly := [],
    export_ := [],
    funcs := [],
    aliases := [],
    cwd := "/",
    locale := lcAmbient,
    loopNest := 0,
    history := [],
    hashes := [] }

/-! # Null checking -/

def nullSym : Sym → Option Bool
  | .symArith _ => some false
  | .symCommand _ => none
  | .symPat _ _ _ _ => none

def nullChar : SymbolicChar → Option Bool
  | .c _ => some false
  | .q _ => some false
  | .sym sym => nullSym sym

def nullString : SymbolicString → Option Bool
  | [] => some true
  | ch :: cs =>
    match nullChar ch with
    | some false => some false
    | some true =>
      match nullString cs with
      | some true => none  -- symbolic, we can't be sure
      | other => other
    | none =>
      match nullString cs with
      | some false => some false
      | _ => none

def nullFields : Fields → Option Bool
  | [] => some true
  | f :: fs =>
    match nullString f, nullFields fs with
    | some true, some true => some true
    | some false, _ => some false
    | _, some false => some false
    | _, _ => none

/-! # Symbolic string conversions -/

def symbolicStringOfFieldsSep (sep : SymbolicString) : Fields → SymbolicString
  | [] => []
  | [f] => f
  | f :: fs => f ++ sep ++ symbolicStringOfFieldsSep sep fs

def symbolicStringOfFields (fs : Fields) : SymbolicString :=
  symbolicStringOfFieldsSep [.c ' '] fs

def stringOfSymbolicString (ss : SymbolicString) : String :=
  match tryConcrete ss with
  | some s => s
  | none => String.join (ss.filterMap fun
    | .c ch => some (String.ofList [ch])
    | .q ch => some (String.ofList [ch])
    | _ => none)

def maximalCharList : SymbolicString → List Char × SymbolicString
  | [] => ([], [])
  | .c ch :: rest =>
    let (cs, remainder) := maximalCharList rest
    (ch :: cs, remainder)
  | .q ch :: rest =>
    let (cs, remainder) := maximalCharList rest
    (ch :: cs, remainder)
  | ss@(.sym _ :: _) => ([], ss)

partial def wordsOfSymbolicString (ss : SymbolicString) : Words :=
  match ss with
  | [] => []
  | .c _ :: _
  | .q _ :: _ =>
    let (cs, remainder) := maximalCharList ss
    .s (String.ofList cs) :: wordsOfSymbolicString remainder
  | .sym sym :: rest => .esym sym :: wordsOfSymbolicString rest

def wordsOfFields : Fields → Words
  | [] => []
  | [ss] => wordsOfSymbolicString ss
  | ss :: fs => wordsOfSymbolicString ss ++ [.f] ++ wordsOfFields fs

partial def expandedWordsOfSymbolicString (ss : SymbolicString) : ExpandedWords :=
  match ss with
  | [] => []
  | .c _ :: _
  | .q _ :: _ =>
    let (cs, remainder) := maximalCharList ss
    .expS (String.ofList cs) :: expandedWordsOfSymbolicString remainder
  | .sym sym :: rest => .ewSym sym :: expandedWordsOfSymbolicString rest


def expandedWordsOfFields : Fields → ExpandedWords
  | [] => []
  | [ss] => expandedWordsOfSymbolicString ss
  | ss :: fs => expandedWordsOfSymbolicString ss ++ [.usrF] ++ expandedWordsOfFields fs

def tryConcretFields : Fields → Option String
  | [] => some ""
  | [ss] => tryConcrete ss
  | ss :: fs => do
    let s ← tryConcrete ss
    let s' ← tryConcretFields fs
    some (s ++ " " ++ s')

def tryConcretFieldsList : Fields → Option (List String)
  | [] => some []
  | ss :: fs => do
    let s ← tryConcrete ss
    let rest ← tryConcretFieldsList fs
    some (s :: rest)

/-! # Escape/unescape helpers -/

def patternEscs : List Char := ['*', '?', '[']
def heredocEscs : List Char := ['\\', '*', '?', '[']

def escapeSc (chars : List Char) : SymbolicChar → SymbolicString
  | .c ch => if ch ∈ chars then [.c '\\', .c ch] else [.c ch]
  | sc => [sc]

def escapeQuotes (ss : SymbolicString) : SymbolicString :=
  ss.flatMap (escapeSc ['"', '\\'])

def escapePatterns (ss : SymbolicString) : SymbolicString :=
  ss.flatMap (escapeSc patternEscs)

partial def unescapeChars (escs : List Char) : SymbolicString → SymbolicString
  | [] => []
  | .c '\\' :: .c ch :: rest =>
    if ch ∈ escs then .c ch :: unescapeChars escs rest
    else .c '\\' :: .c ch :: unescapeChars escs rest
  | sc :: rest => sc :: unescapeChars escs rest

def unescapePattern : SymbolicString → SymbolicString :=
  unescapeChars patternEscs

def unescapeTmpField : TmpField → TmpField
  | .wfs => .wfs
  | .fs => .fs
  | .field ss => .field (unescapePattern ss)
  | .qfield ss => .qfield ss

def unescapeIntermediateFields (ifs : IntermediateFields) : IntermediateFields :=
  ifs.map unescapeTmpField

def unescapeHeredocField : TmpField → TmpField
  | .wfs => .wfs
  | .fs => .fs
  | .field ss => .field (unescapeChars heredocEscs ss)
  | .qfield ss => .qfield (unescapeChars heredocEscs ss)

def unescapeHeredoc (ifs : IntermediateFields) : IntermediateFields :=
  ifs.map unescapeHeredocField

/-! # Expanded words helpers -/

partial def symbolicStringOfExpandedWords (forPattern : Bool) : ExpandedWords → SymbolicString
  | [] => symbolicStringOfString ""
  | .usrF :: ws => symbolicStringOfString " " ++ symbolicStringOfExpandedWords forPattern ws
  | .expS s :: ws =>
    let ss := symbolicStringOfString s
    (if forPattern then ss.flatMap (escapeSc ['"']) else ss) ++
      symbolicStringOfExpandedWords forPattern ws
  | .dquo ss :: ws =>
    -- For pattern context: convert chars to .q (quoted/literal) so Lean's pattern parser
    -- treats them as literals (OCaml wraps in "..." for its char-level parser instead)
    (if forPattern then ss.map fun | .c ch => .q ch | x => x else ss) ++
      symbolicStringOfExpandedWords forPattern ws
  | .at_ fs :: ws =>
    symbolicStringOfFields fs ++ symbolicStringOfExpandedWords forPattern ws
  | .ewSym sym :: ws => .sym sym :: symbolicStringOfExpandedWords forPattern ws
  | .usrS s :: ws =>
    let ss := symbolicStringOfString s
    (if forPattern then escapeQuotes ss else ss) ++
      symbolicStringOfExpandedWords forPattern ws

def fieldsOfExpandedWords (w : ExpandedWords) : Fields :=
  [symbolicStringOfExpandedWords false w]

def collapseQuoted (ew : ExpandedWords) : ExpandedWords :=
  -- OCaml: break is_at w, then:
  --   if no At: [DQuo (concat_expanded w)]
  --   if At fs found: pre_w ++ intersperse UsrF (map DQuo fs) ++ post_w
  let isAt : ExpandedWord → Bool
    | .at_ _ => true
    | _ => false
  -- Split at the first At entry using span
  let (preW, rest) := ew.span (fun e => !isAt e)
  match rest with
  | [] =>
    -- No At entry: just collapse everything into a DQuo
    [.dquo (symbolicStringOfExpandedWords false ew)]
  | .at_ fs :: postW =>
    -- Found At: attach pre_w to first field, intersperse DQuo fields with UsrF
    let dquoFields := fs.map (fun ss => ExpandedWord.dquo ss)
    let interspersed := dquoFields.intersperse .usrF
    preW ++ interspersed ++ postW
  | _ => -- shouldn't happen
    [.dquo (symbolicStringOfExpandedWords false ew)]

/-! # AST smart constructors -/

def pushredir' (stmt : Stmt) (savedFds : SavedFds) : Stmt :=
  if savedFds.isEmpty then stmt
  else .pushredir stmt savedFds

-- withRedirs, closeFdAndThen, tryAvoidFork are defined in Os.lean


/-! # Redirect helpers -/

def expandedRedirHasStdinRedir : ExpandedRedir → Bool
  | .erFile .from_ 0 _ => true
  | .erFile .fromTo 0 _ => true
  | .erDup .toFD _ _ (some 1) => true
  | .erDup .fromFD _ 1 (some _) => true
  | .erHeredoc _ 1 _ => true
  | _ => false

def getExpandingRedirState : ExpandingRedir → ExpansionState
  | .xrFile _ _ es => es
  | .xrDup _ _ es => es
  | .xrHeredoc _ _ es => es

def setExpandingRedirState (es : ExpansionState) : ExpandingRedir → ExpandingRedir
  | .xrFile ty fd _ => .xrFile ty fd es
  | .xrDup ty fd _ => .xrDup ty fd es
  | .xrHeredoc ty fd _ => .xrHeredoc ty fd es

def tryExpandRedir (er : ExpandingRedir) (fs : Fields) : Except String ExpandedRedir :=
  match er with
  | .xrFile ty fd _ =>
    match fs with
    | [ss] => .ok (.erFile ty fd ss)
    | _ => .error "ambiguous redirect"
  | .xrDup ty fd _ =>
    match fs with
    | [ss] =>
      match tryConcrete ss with
      | some "-" => .ok (.erDup ty .closeOrig fd none)
      | some s =>
        match readNat s.toList with
        | .ok n => .ok (.erDup ty .leaveOrig fd (some n))
        | .error _ => .error s!"bad file descriptor: {s}"
      | none => .error "symbolic fd target"
    | _ => .error "ambiguous redirect"
  | .xrHeredoc ty fd _ =>
    let ss := fs.flatMap id
    .ok (.erHeredoc ty fd ss)

def isHeredoc : ExpandingRedir → Bool
  | .xrHeredoc _ _ _ => true
  | _ => false

/-! # destInit helper -/

def destInit : List α → Option (List α × α)
  | [] => none
  | [x] => some ([], x)
  | x :: xs =>
    match destInit xs with
    | none => none
    | some (init, last) => some (x :: init, last)

/-! # Concretize -/

def concretizeSimple (ss : SymbolicString) : String :=
  match tryConcrete ss with
  | some s => s
  | none => stringOfSymbolicString ss

/-! # Expansion step helpers -/

def ranCommandSubstitution : ExpansionStep → Bool
  | .esCommand _ => true
  | .esNested outer inner => ranCommandSubstitution outer || ranCommandSubstitution inner
  | .esEval step _ => ranCommandSubstitution step
  | _ => false

/-! # Perms parsing -/

def permsWho' (who : PermsWho) (perms : Perms) : List FilePerm :=
  match who with
  | .whoU => perms.user
  | .whoG => perms.group
  | .whoO => perms.other

def permsFor (f : List FilePerm → List FilePerm) (who : PermsWho) (perms : Perms) : Perms :=
  match who with
  | .whoU => { perms with user := f perms.user }
  | .whoG => { perms with group := f perms.group }
  | .whoO => { perms with other := f perms.other }

def permsForMany (f : List FilePerm → List FilePerm) (who : List PermsWho) (perms : Perms) : Perms :=
  who.foldr (permsFor f) perms

def permsClear (who : List PermsWho) (perms : Perms) : Perms :=
  permsForMany (fun _ => []) who perms

def permsWholistOfCl (who : List PermsWho) : List Char → Except String (List PermsWho × List Char)
  | 'u' :: cs' => permsWholistOfCl (if who.contains .whoU then who else .whoU :: who) cs'
  | 'g' :: cs' => permsWholistOfCl (if who.contains .whoG then who else .whoG :: who) cs'
  | 'o' :: cs' => permsWholistOfCl (if who.contains .whoO then who else .whoO :: who) cs'
  | 'a' :: cs' => permsWholistOfCl permsWholistAll cs'
  | cs =>
    if who.isEmpty then .error "empty wholist: need to specify one of ugoa"
    else .ok (who, cs)

def flagOfFilePerm : FilePerm → PermsFlag
  | .read => .permR
  | .write => .permW
  | .execute => .permX

def permsFlaglistOfCl (pflags : List PermsFlag) : List Char → Except String (List PermsFlag × List Char)
  | 'r' :: cs' => permsFlaglistOfCl (if pflags.contains .permR then pflags else .permR :: pflags) cs'
  | 'w' :: cs' => permsFlaglistOfCl (if pflags.contains .permW then pflags else .permW :: pflags) cs'
  | 'x' :: cs' => permsFlaglistOfCl (if pflags.contains .permX then pflags else .permX :: pflags) cs'
  | 'X' :: cs' => permsFlaglistOfCl (if pflags.contains .permBigX then pflags else .permBigX :: pflags) cs'
  | 's' :: cs' => permsFlaglistOfCl (if pflags.contains .permS then pflags else .permS :: pflags) cs'
  | 't' :: cs' => permsFlaglistOfCl (if pflags.contains .permT then pflags else .permT :: pflags) cs'
  | cs =>
    if pflags.isEmpty then .error "empty permlist: need to specify one of rwxXst"
    else .ok (pflags, cs)

def permsOpOfCl : List Char → Except String (PermsOp × List Char)
  | '+' :: cs' => .ok (.opPlus, cs')
  | '-' :: cs' => .ok (.opMinus, cs')
  | '=' :: cs' => .ok (.opEqual, cs')
  | c :: _ => .error s!"expected op (one of +-=), got '{String.ofList [c]}'"
  | [] => .error "expected op (one of +-=, got empty string"

partial def permsActionlistOfCl (actions : List PermsAction) (cs : List Char)
    : Except String (List PermsAction × List Char) :=
  match permsOpOfCl cs with
  | .ok (op, cs') =>
    match cs' with
    | 'u' :: cs'' => permsActionlistOfCl (.actCopy op .whoU :: actions) cs''
    | 'g' :: cs'' => permsActionlistOfCl (.actCopy op .whoG :: actions) cs''
    | 'o' :: cs'' => permsActionlistOfCl (.actCopy op .whoO :: actions) cs''
    | _ =>
      match permsFlaglistOfCl [] cs' with
      | .ok (pflags, cs'') => permsActionlistOfCl (.actPerms op pflags :: actions) cs''
      | .error _ => permsActionlistOfCl (.actOp op :: actions) cs'
  | .error msg =>
    if actions.isEmpty then .error s!"empty actionlist: {msg}"
    else .ok (actions.reverse, cs)

def permsClauseOfCl (cs : List Char) : Except String (PermsClause × List Char) :=
  let (who, cs') :=
    match permsWholistOfCl [] cs with
    | .ok (who, cs') => (who, cs')
    | .error _ => (permsWholistAll, cs)
  match permsActionlistOfCl [] cs' with
  | .ok (actions, cs'') => .ok ((who, actions), cs'')
  | .error msg => .error s!"bad clause: {msg}"

partial def permsSymbolicOfCl (permsAcc : PermsSymbolic) (cs : List Char)
    : Except String (PermsSymbolic × List Char) :=
  match permsClauseOfCl cs with
  | .error msg => .error s!"no clauses found: {msg}"
  | .ok (clause, []) => .ok (clause :: permsAcc, [])
  | .ok (clause, ',' :: cs') => permsSymbolicOfCl (clause :: permsAcc) cs'
  | .ok (_, c :: _) => .error s!"expected comma between clauses, found '{String.ofList [c]}'"

def permsSymbolicOfString (s : String) : Except String PermsSymbolic :=
  match permsSymbolicOfCl [] s.toList with
  | .error msg => .error msg
  | .ok (perms_, []) => .ok perms_
  | .ok (_, cs') => .error s!"invalid symbolic permissions: {String.ofList cs'}"

def octalStringOfPerms (perms : Perms) : String :=
  let bit0 := if perms.sticky then 1 else 0
  let bit1 := if perms.setgid then 2 else 0
  let bit2 := if perms.setuid then 4 else 0
  let first := Nat.repr (bit0 + bit1 + bit2)
  let second := Nat.repr (natOfFilePerms perms.user)
  let third := Nat.repr (natOfFilePerms perms.group)
  let fourth := Nat.repr (natOfFilePerms perms.other)
  first ++ second ++ third ++ fourth

/-! # Intermediate field conversions -/

def symbolicStringOfIntermediateFields : IntermediateFields → SymbolicString
  | [] => []
  | .fs :: ifs' => .c ' ' :: symbolicStringOfIntermediateFields ifs'
  | .wfs :: ifs' => .c ' ' :: symbolicStringOfIntermediateFields ifs'
  | .field s :: ifs' => s ++ symbolicStringOfIntermediateFields ifs'
  | .qfield s :: ifs' =>
    [.c '"'] ++ s ++ [.c '"'] ++ symbolicStringOfIntermediateFields ifs'

/-! # Quoting -/

def quotedChars : List Char :=
  "|&;<>()$`\\\"'*?[#˜=% \t\n".toList

def escapedChars : List Char :=
  "$`\"\\\n".toList

partial def quoteCl : List Char → List Char × Bool
  | [] => ([], false)
  | c :: cs =>
    let (cs', needsQuotes) := quoteCl cs
    if c ∈ escapedChars then ('\\' :: c :: cs', true)
    else (c :: cs', needsQuotes || c ∈ quotedChars)

def quote' (s : String) : String :=
  let (cs, needsQuotes) := quoteCl s.toList
  let s' := String.ofList cs
  if needsQuotes then "\"" ++ s' ++ "\"" else s'

/-! # Number helpers -/

def integerToFields (n : Int) : Fields :=
  [symbolicStringOfString (Int.repr n)]

def natOfSymbolicString (ss : SymbolicString) : Except String Nat :=
  match tryConcrete ss with
  | none => .error s!"can't parse number in symbolic string"
  | some s => readNat s.toList

/-! # Split helpers -/

partial def splitEqual (varAcc : String) : SymbolicString → String × Option SymbolicString
  | [] => (varAcc, none)
  | .c '=' :: ss' => (varAcc, some ss')
  | .c ch :: ss' => splitEqual (varAcc ++ String.ofList [ch]) ss'
  | ss => (varAcc ++ stringOfSymbolicString ss, none)

def trySplitAssign (ss : SymbolicString) : String × Option SymbolicString :=
  splitEqual "" ss

/-! # Redirect munging -/

def tryExtractField : Fields → Except String SymbolicString
  | [s] => .ok s
  | [] => .error "empty redirect target"
  | fs => .error s!"redirect target wasn't a single field: '{stringOfSymbolicString (fs.flatMap id)}'"

def tryExtractDupTgt (ss : SymbolicString) : Except String (Option Nat) :=
  if ss == [.c '-'] then .ok none
  else match readNat (stringOfSymbolicString ss).toList with
    | .error err => .error s!"invalid file descriptor: {err}"
    | .ok n => .ok (some n)

/-! # Parse source helpers -/

def parseSourceForDot : ParseSource → Bool
  | .parseFile _ _ => true
  | .parseString _ _ => false
  | .parseSTDIN => false

def parseSourcePropagatesControl : ParseSource → Bool
  | .parseSTDIN => true
  | .parseString .parseEval _ => true
  | .parseString .parseTrap _ => false
  | .parseFile _ _ => false

/-! # Stmt helpers -/

def withRedirs (stmt : Stmt) (ers : List ExpandedRedir) : Stmt :=
  if ers.isEmpty then stmt
  else .redir stmt (ers, none, [])

def closeFdAndThen (fd : Fd) (stmt : Stmt) : Stmt :=
  .semi (.pushredir .done [(fd, .inr ())]) stmt

partial def tryAvoidFork : Stmt → Stmt
  | .command assigns args redirs opts =>
    .command assigns args redirs { opts with shouldFork := false }
  | .commandExpArgs assigns es redirs opts =>
    .commandExpArgs assigns es redirs { opts with shouldFork := false }
  | .commandExpRedirs assigns fs rs opts =>
    .commandExpRedirs assigns fs rs { opts with shouldFork := false }
  | .commandExpAssign assigns fs saved opts =>
    .commandExpAssign assigns fs saved { opts with shouldFork := false }
  | .commandReady assigns cmd args saved opts =>
    .commandReady assigns cmd args saved { opts with shouldFork := false }
  | .redir stmt' rs => .redir (tryAvoidFork stmt') rs
  | stmt => stmt

/-! # Redir state helpers -/

def combineRedirs (rs1 rs2 : RedirState) : RedirState :=
  let (ers1, er1, rs1') := rs1
  let (ers2, er2, rs2') := rs2
  let er := match er1, er2 with
    | none, none => none
    | some er, none => some er
    | none, some er => some er
    | some _, some _ => none  -- error case
  (ers1 ++ ers2, er, rs1' ++ rs2')

/-! # Job display helpers -/

def curPrevJobs (jobs : List JobInfo) : Nat × Nat :=
  match jobs with
  | [] => (0, 0)
  | [job] => (job.id, job.id)
  | cur :: prev :: _ => (cur.id, prev.id)

def stringOfJobNumber (curPrev : Nat × Nat) (job : JobInfo) : String :=
  let (curId, prevId) := curPrev
  "[" ++ Nat.repr job.id ++ "] " ++
    (if job.id == curId then "+"
     else if job.id == prevId then "-"
     else " ") ++ " "

def paddedStringOfJobStatus (job : JobInfo) : String :=
  padRight (stringOfJobStatus job.status) 25

/-! # Pretty-printing -/

def braces (s : String) : String := "{ " ++ s ++ " ; }"
def background' (s : String) : String := "{ " ++ s ++ " & }"

def showUnless (expected actual : Nat) : String :=
  if expected == actual then "" else Nat.repr actual

mutual
partial def stringOfFormat : Format → String
  | .normal => ""
  | .length_ => "#"
  | .default_ w => "-" ++ stringOfWords w
  | .ndefault w => ":-" ++ stringOfWords w
  | .assign w => "=" ++ stringOfWords w
  | .nassign w => ":=" ++ stringOfWords w
  | .error w => "?" ++ stringOfWords w
  | .nerror w => ":?" ++ stringOfWords w
  | .alt w => "+" ++ stringOfWords w
  | .nalt w => ":+" ++ stringOfWords w
  | .substring side mode w => stringOfSubstring side mode ++ stringOfWords w

partial def stringOfSubstring (side : SubstringSide) (mode : SubstringMode) : String :=
  let sym := match side with | .prefix_ => "#" | .suffix_ => "%"
  match mode with | .longest => sym ++ sym | .shortest => sym

partial def stringOfControl : Control → String
  | .tilde user => "~" ++ user
  | .param var .normal => "$" ++ var
  | .param var .length_ => "${#" ++ var ++ "}"
  | .param var fmt => "${" ++ var ++ stringOfFormat fmt ++ "}"
  | .lassign var ew w =>
    "${" ++ var ++ "=" ++ stringOfExpandedWords ew ++ stringOfWords w ++ "}"
  | .lmatch f _ _ _ _ => stringOfFields f
  | .lerror var ew w =>
    "${" ++ var ++ "?" ++ stringOfExpandedWords ew ++ stringOfWords w ++ "}"
  | .backtick c => "$( " ++ stringOfStmt c ++ " )"
  | .lbacktick c _ _ => "$( " ++ stringOfStmt c ++ " )"
  | .lbacktickWait c _ _ => "$( " ++ stringOfStmt c ++ " )"
  | .arith ew w => "$(( " ++ stringOfExpandedWords ew ++ stringOfWords w ++ " ))"
  | .quote ew w => "\"" ++ stringOfExpandedWords ew ++ stringOfWords w ++ "\""
  | .escape c => String.ofList ['\\', c]

partial def stringOfEntry : Entry → String
  | .s str => str
  | .k code => stringOfControl code
  | .f => " "
  | .esym _ => "<<SYMBOLIC>>"

partial def stringOfWords (w : Words) : String :=
  String.join (w.map stringOfEntry)

partial def stringOfExpandedWords : ExpandedWords → String
  | [] => ""
  | .usrF :: ws => " " ++ stringOfExpandedWords ws
  | .expS s :: ws => s ++ stringOfExpandedWords ws
  | .dquo ss :: ws => "\"" ++ stringOfSymbolicString ss ++ "\"" ++ stringOfExpandedWords ws
  | .at_ fs :: ws => stringOfFields fs ++ stringOfExpandedWords ws
  | .ewSym _ :: ws => "<<SYM>>" ++ stringOfExpandedWords ws
  | .usrS s :: ws => s ++ stringOfExpandedWords ws

partial def stringOfFields : Fields → String
  | [] => ""
  | [f] => stringOfSymbolicString f
  | f :: fs => stringOfSymbolicString f ++ " " ++ stringOfFields fs

partial def stringOfRfile (ty : RedirType) (fd : Nat) : String :=
  match ty with
  | .to => showUnless 1 fd ++ ">"
  | .clobber => showUnless 1 fd ++ ">|"
  | .from_ => showUnless 0 fd ++ "<"
  | .fromTo => showUnless 0 fd ++ "<>"
  | .append => showUnless 1 fd ++ ">>"

partial def stringOfRdup (ty : DupType) (fd : Nat) : String :=
  match ty with
  | .toFD => showUnless 1 fd ++ ">&"
  | .fromFD => showUnless 0 fd ++ "<&"

partial def stringOfHeredoc (ty : HeredocType) (fd : Nat) (heredoc : String) : String :=
  let marker := "EOF"
  showUnless 0 fd ++ "<<" ++
    (if ty == .xhere then marker else "'" ++ marker ++ "'") ++
    "\n" ++ heredoc ++ marker ++ "\n"

partial def stringOfRedir : Redir → String
  | .rfile ty fd a => stringOfRfile ty fd ++ stringOfWords a
  | .rdup ty fd tgt => stringOfRdup ty fd ++ stringOfWords tgt
  | .rheredoc ty fd a => stringOfHeredoc ty fd (stringOfWords a)

partial def stringOfExpandedRedir : ExpandedRedir → String
  | .erFile ty fd a => stringOfRfile ty fd ++ stringOfSymbolicString a
  | .erDup ty _ fd tgt =>
    stringOfRdup ty fd ++ match tgt with | none => "-" | some n => Nat.repr n
  | .erHeredoc ty fd a => stringOfHeredoc ty fd (stringOfSymbolicString a)

partial def stringOfExpandingRedir : Option ExpandingRedir → String
  | none => ""
  | some (.xrFile ty fd es) => stringOfRfile ty fd ++ stringOfExpansionState es
  | some (.xrDup ty fd es) => stringOfRdup ty fd ++ stringOfExpansionState es
  | some (.xrHeredoc ty fd es) => stringOfHeredoc ty fd (stringOfExpansionState es)

partial def stringOfRedirState (rs : RedirState) : String :=
  let (ers, expRedir, rs') := rs
  let s1 := String.join (ers.map (fun er => stringOfExpandedRedir er ++ " "))
  let s2 := stringOfExpandingRedir expRedir
  let s3 := String.join (rs'.map (fun r => stringOfRedir r ++ " "))
  spacedMany [s1, s2, s3]

partial def stringOfExpansionState : ExpansionState → String
  | .expStart _ w => stringOfWords w
  | .expExpand _ ew w => stringOfExpandedWords ew ++ stringOfWords w
  | .expSplit _ ew => stringOfExpandedWords ew
  | .expPath _ ifs => stringOfIntermediateFields ifs
  | .expQuote _ ifs => stringOfIntermediateFields ifs
  | .expError f => stringOfFields f
  | .expDone f => stringOfFields f

partial def stringOfIntermediateFields : IntermediateFields → String
  | [] => ""
  | .wfs :: ifs => " " ++ stringOfIntermediateFields ifs
  | .fs :: ifs => " " ++ stringOfIntermediateFields ifs
  | .field s :: ifs => stringOfSymbolicString s ++ stringOfIntermediateFields ifs
  | .qfield s :: ifs => "\"" ++ stringOfSymbolicString s ++ "\"" ++ stringOfIntermediateFields ifs

partial def stringOfParseSource : ParseSource → String
  | .parseSTDIN => "<STDIN>"
  | .parseString _ cmd => "'" ++ cmd ++ "'"
  | .parseFile file _ => file

partial def stringOfCase (c : List Words × Stmt) : String :=
  let (pats, body) := c
  String.join (pats.map (stringOfWords · ++ "|")) ++ ") " ++ stringOfStmt body ++ ";;"

partial def stringOfWhile (c body : Stmt) : String :=
  match c with
  | .not_ c' => "until " ++ stringOfStmt c' ++ "; do " ++ stringOfStmt body ++ "; done "
  | _ => "while " ++ stringOfStmt c ++ "; do " ++ stringOfStmt body ++ "; done "

partial def stringOfIf (c t e : Stmt) : String :=
  "if " ++ stringOfStmt c ++
  "; then " ++ stringOfStmt t ++
  (match e with
   | .command [] [] [] _ => "; fi"
   | .if_ c' t' e' => "; el" ++ stringOfIf c' t' e'
   | _ => "; else " ++ stringOfStmt e ++ "; fi")

partial def stringOfStmt : Stmt → String
  | .command assigns cmds redirs _ =>
    let sAssigns := String.join (assigns.map fun (v, a) => v ++ "=" ++ stringOfWords a ++ " ")
    spacedMany [sAssigns, stringOfWords cmds,
      String.join (redirs.map (stringOfRedir · ++ " "))]
  | .commandExpArgs assigns es redirs _ =>
    let sAssigns := String.join (assigns.map fun (v, a) => v ++ "=" ++ stringOfWords a ++ " ")
    spacedMany [sAssigns, stringOfExpansionState es,
      String.join (redirs.map (stringOfRedir · ++ " "))]
  | .commandExpRedirs assigns fs rs _ =>
    let sAssigns := String.join (assigns.map fun (v, a) => v ++ "=" ++ stringOfWords a ++ " ")
    spacedMany [sAssigns, stringOfFields fs, stringOfRedirState rs]
  | .commandExpAssign assigns fs _ _ =>
    let sAssigns := String.join (assigns.map fun (v, a) => v ++ "=" ++ stringOfExpansionState a ++ " ")
    spacedMany [sAssigns, stringOfFields fs]
  | .commandReady assigns cmd args _ _ =>
    let sAssigns := String.join (assigns.map fun (v, a) => v ++ "=" ++ stringOfSymbolicString a ++ " ")
    spacedMany [sAssigns, stringOfFields (cmd :: args)]
  | .pipe mode cmds =>
    let p := String.intercalate " | " (cmds.map stringOfStmt)
    if mode.isBg then background' p else p
  | .redir cmd rs => spaced (stringOfStmt cmd) (stringOfRedirState rs)
  | .background cmd rs => background' (spaced (stringOfStmt cmd) (stringOfRedirState rs))
  | .subshell cmd rs => spaced (parens (stringOfStmt cmd)) (stringOfRedirState rs)
  | .and_ cmd1 cmd2 => stringOfStmt cmd1 ++ " && " ++ stringOfStmt cmd2
  | .or_ cmd1 cmd2 => stringOfStmt cmd1 ++ " || " ++ stringOfStmt cmd2
  | .semi cmd1 cmd2 => stringOfStmt cmd1 ++ " ; " ++ stringOfStmt cmd2
  | .not_ cmd => "! " ++ stringOfStmt cmd
  | .if_ c t e => stringOfIf c t e
  | .while_ c body => stringOfWhile c body
  | .whileCond c cur body _ =>
    "if " ++ stringOfStmt cur ++
    "; then " ++ stringOfStmt body ++ "; " ++ stringOfWhile c body ++ "; fi"
  | .whileRunning c body cur =>
    stringOfStmt cur ++ "; " ++ stringOfWhile c body
  | .for_ x w body =>
    "for " ++ x ++ " in " ++ stringOfWords w ++ "; do " ++ stringOfStmt body ++ "; done"
  | .forExpArgs x es body =>
    "for " ++ x ++ " in " ++ stringOfExpansionState es ++ "; do " ++ stringOfStmt body ++ "; done"
  | .forExpanded x f body =>
    "for " ++ x ++ " in " ++ stringOfFields f ++ "; do " ++ stringOfStmt body ++ "; done"
  | .forRunning x f body cur =>
    stringOfStmt cur ++ "; for " ++ x ++ " in " ++ stringOfFields f ++ "; do " ++ stringOfStmt body ++ "; done"
  | .case_ w cs =>
    "case " ++ stringOfWords w ++ " in " ++
      String.join (cs.map (stringOfCase · ++ " ")) ++ " esac"
  | .caseExpArg es cs =>
    "case " ++ stringOfExpansionState es ++ " in " ++
      String.join (cs.map (stringOfCase · ++ " ")) ++ " esac"
  | .caseMatch s cs =>
    "case " ++ stringOfSymbolicString s ++ " in " ++
      String.join (cs.map (stringOfCase · ++ " ")) ++ " esac"
  | .caseCheckMatch s es cmd rest =>
    "case " ++ stringOfSymbolicString s ++ " in " ++
      stringOfExpansionState es ++ ") " ++ stringOfStmt cmd ++ ";; " ++
      String.join (rest.map (stringOfCase · ++ " ")) ++ " esac"
  | .defun name cmd => name ++ "() {\n" ++ stringOfStmt cmd ++ "\n}"
  | .call _ _ _ _ c => stringOfStmt c
  | .evalLoop _ _ (.parseString .parseEval cmd) _ _ => "eval '" ++ cmd ++ "'"
  | .evalLoop _ _ (.parseString .parseTrap cmd) _ _ => "eval '" ++ cmd ++ "' # from trap"
  | .evalLoop _ _ _ _ _ => ": EvalLoop"
  | .evalLoopCmd _ _ (.parseString .parseEval cmd) _ _ c =>
    stringOfStmt c ++ " # in eval '" ++ cmd ++ "'"
  | .evalLoopCmd _ _ (.parseString .parseTrap cmd) _ _ c =>
    stringOfStmt c ++ " # in eval '" ++ cmd ++ "' from trap"
  | .evalLoopCmd _ _ _ _ _ c => stringOfStmt c
  | .break_ n => "break " ++ Nat.repr n
  | .continue_ n => "continue " ++ Nat.repr n
  | .return_ => "return"
  | .exit_ => "exit"
  | .exec _ cmdName args _ _ =>
    spaced "exec" (stringOfFields (cmdName :: args))
  | .wait n _ _ _ => "wait " ++ Nat.repr n
  | .trapped signal _ handler cont =>
    ": trap on " ++ signal.toString ++ " ; " ++ stringOfStmt handler ++ " ; " ++
    ": end trap ; " ++ stringOfStmt cont
  | .checkedExit c => ": ignoring errexit ; " ++ stringOfStmt c ++ " ; : resuming errexit"
  | .pushredir s _ => stringOfStmt s
  | .done => ": Done"

partial def stringOfExpansionStep : ExpansionStep → String
  | .esTilde s => spaced "Tilde" s
  | .esParam s => spaced "Param" s
  | .esCommand s => spaced "Command" s
  | .esArith s => spaced "Arith" s
  | .esSplit s => spaced "Split" s
  | .esPath s => spaced "Path" s
  | .esQuote s => spaced "Quote" s
  | .esEscape s => spaced "Escape" s
  | .esStep s => spaced "Step" s
  | .esNested outer inner =>
    parens (stringOfExpansionStep outer) ++ " " ++ parens (stringOfExpansionStep inner)
  | .esEval step evalStep =>
    parens (stringOfExpansionStep step) ++ " " ++ parens (stringOfEvaluationStep evalStep)

partial def stringOfEvaluationStep : EvaluationStep → String
  | .xsSimple s => spaced "Simple" s
  | .xsPipe s => spaced "Pipe" s
  | .xsRedir s => spaced "Redir" s
  | .xsBackground s => spaced "Background" s
  | .xsSubshell s => spaced "Subshell" s
  | .xsAnd s => spaced "And" s
  | .xsOr s => spaced "Or" s
  | .xsNot s => spaced "Not" s
  | .xsSemi s => spaced "Semi" s
  | .xsIf s => spaced "If" s
  | .xsWhile s => spaced "While" s
  | .xsFor s => spaced "For" s
  | .xsCase s => spaced "Case" s
  | .xsDefun s => spaced "Defun" s
  | .xsStack name step =>
    spaced "Stack" name ++ " " ++ parens (stringOfEvaluationStep step)
  | .xsStep s => spaced "Step" s
  | .xsExec s => spaced "Exec" s
  | .xsEval linno src s =>
    "EvalLoop " ++ Nat.repr linno ++ " " ++ stringOfParseSource src ++
      (if s == "" then "" else " " ++ s)
  | .xsWait s => spaced "Wait" s
  | .xsTrap signal s => "Trap " ++ spaced signal.toString s
  | .xsProc _ c => "Proc " ++ stringOfStmt c
  | .xsNested outer inner =>
    parens (stringOfEvaluationStep outer) ++ " " ++ parens (stringOfEvaluationStep inner)
  | .xsExpand step estep =>
    parens (stringOfEvaluationStep step) ++ " " ++ parens (stringOfExpansionStep estep)
end

/-! # Job status display -/

partial def stringOfJob (mode : JobsMode) (curjob : Nat × Nat) (job : JobInfo) : String :=
  match mode with
  | .jobsTerse => Nat.repr job.pid ++ "\n"
  | .jobsFGCommand => stringOfStmt job.cmd ++ "\n"
  | .jobsBGCommand =>
    "[" ++ Nat.repr job.id ++ "] " ++ stringOfStmt job.cmd ++ "\n"
  | .jobsNormal =>
    stringOfJobNumber curjob job ++
    paddedStringOfJobStatus job ++
    stringOfStmt job.cmd ++ "\n"
  | .jobsLong =>
    stringOfJobNumber curjob job ++
    Nat.repr job.pid ++ " " ++
    paddedStringOfJobStatus job ++
    stringOfStmt job.cmd ++ "\n"

/-! # Command name extraction — for hashing -/

def tryCommandWords : Words → String
  | .s cmd :: _ => cmd
  | _ => ""

def tryCommandFields : Fields → String
  | [] => ""
  | cmd :: _ => stringOfSymbolicString cmd

def tryCommandExpansionState : ExpansionState → String
  | .expStart _ w => tryCommandWords w
  | .expExpand _ [] w => tryCommandWords w
  | .expExpand _ (.expS s :: _) _ => s
  | .expExpand _ (.usrS s :: _) _ => s
  | .expDone f => tryCommandFields f
  | _ => ""

partial def collectCommandNames : Stmt → List String
  | .command _ cmds _ _ =>
    let s := tryCommandWords cmds
    if s.isEmpty then [] else [s]
  | .commandReady _ cmd _ _ _ => [stringOfSymbolicString cmd]
  | .pipe _ cmds => cmds.flatMap collectCommandNames
  | .redir cmd _ => collectCommandNames cmd
  | .background cmd _ => collectCommandNames cmd
  | .subshell cmd _ => collectCommandNames cmd
  | .and_ c1 c2 => collectCommandNames c1 ++ collectCommandNames c2
  | .or_ c1 c2 => collectCommandNames c1 ++ collectCommandNames c2
  | .semi c1 c2 => collectCommandNames c1 ++ collectCommandNames c2
  | .not_ cmd => collectCommandNames cmd
  | .if_ c1 c2 c3 => collectCommandNames c1 ++ collectCommandNames c2 ++ collectCommandNames c3
  | .while_ c1 c2 => collectCommandNames c1 ++ collectCommandNames c2
  | .for_ _ _ c => collectCommandNames c
  | .case_ _ cs => cs.flatMap (fun (_, c) => collectCommandNames c)
  | .defun _ cmd => collectCommandNames cmd
  | .call _ _ _ body c => collectCommandNames body ++ collectCommandNames c
  | .evalLoopCmd _ _ _ _ _ c => collectCommandNames c
  | .checkedExit c => collectCommandNames c
  | .pushredir c _ => collectCommandNames c
  | _ => []
