import Smoosh.Compat.PervasivesExtra
import Smoosh.BuildInfo
import Smoosh.Platform.SignalPlatform
import Smoosh.Signal
import Smoosh.Prelude.FilePerm
import Smoosh.Map
import Smoosh.Prelude.Pattern
import Smoosh.Prelude.Redirect
import Smoosh.Prelude.ShellOptions
import Smoosh.Prelude.Locales
import Init.Classical

namespace Smoosh
open Smoosh

/-- Lem: parse_string_mode type -/
inductive parse_string_mode where
  | ParseEval
  | ParseTrap
deriving Repr, DecidableEq

/-- Lem: parse_file_mode type -/
inductive parse_file_mode where
  | PushFile
  | NoPushFile
deriving Repr, DecidableEq

/-- Lem: should_push_file : parse_file_mode -> bool -/
def should_push_file : parse_file_mode → Bool
  | .PushFile   => true
  | .NoPushFile => false

/-- Lem : parse_source type -/
inductive parse_source where
  | ParseSTDIN
  | ParseString (mode : parse_string_mode) (s : String)
  | ParseFile (path : String) (mode : parse_file_mode)
deriving Repr, DecidableEq

abbrev pid  := Nat
abbrev fd   := Nat
abbrev path := String


/-
type stackmark
declare ocaml target_rep type stackmark = `Ctypes.structure` `Dash.stackmark`
type dash_string
declare ocaml target_rep type dash_string = `Ctypes.ptr` char
-/
-- opaque stackmark  : Type
-- opaque dash_string : Type
abbrev stackmark := UInt64
abbrev dash_string := String

inductive parse_context : Type u
  | Mk (ds : Option dash_string) (sm : Option stackmark)
deriving Repr, DecidableEq

/-
  ===========
  SHELL STATE pieces that AST needs (saved_fds)
  ===========
-/

inductive saved_fd_info
  | Saved (f : fd) | Close
  deriving Repr, DecidableEq

abbrev saved_fds := List (fd × saved_fd_info)

mutual
  /-- Lem: format type -/
  inductive format : Type
    | Normal
    | Default  (ws : List entry)
    | NDefault (ws : List entry)
    | Assign   (ws : List entry)
    | NAssign  (ws : List entry)
    | Error    (ws : List entry)
    | NError   (ws : List entry)
    | Alt      (ws : List entry)
    | NAlt     (ws : List entry)
    | Length
    | Substring (side : substring_side) (mode : substring_mode) (ws : List entry)
  deriving Repr

  inductive control : Type
    | Tilde  (s : String)
    | Param  (name : String) (fmt : format)
    | LAssign (name : String) (ew : List expanded_word) (ws : List entry)
    | LMatch (fs : List (List symbolic_char)) (side : substring_side) (mode : substring_mode)
             (ew : List expanded_word) (ws : List entry)
    | LError (name : String) (ew : List expanded_word) (ws : List entry)
    | Backtick (st : stmt)
    | LBacktick (orig : stmt) (p : pid) (f : fd)
    | LBacktickWait (orig : stmt) (p : pid) (result : String)
    | Arith (ew : List expanded_word) (ws : List entry)
    | Quote (ew : List expanded_word) (ws : List entry)
    | Escape (c : Char)
  deriving Repr

  inductive entry : Type
    | S    (s : String)
    | K    (ctl : control)
    | F
    | ESym (sym : sym)
  deriving Repr

  inductive stmt : Type
    | Command (assigns : List (String × List entry)) (args : List entry) (redirs : List redir) (opts : command_opts)
    | CommandExpArgs (assigns : List (String × List entry)) (st : expansion_state) (redirs : List redir) (opts : command_opts)
    | CommandExpRedirs (assigns : List (String × List entry)) (fs : List (List symbolic_char))
        (rs : (List expanded_redir) × Option expanding_redir × List redir) (opts : command_opts)
    | CommandExpAssign (assigns : List (String × expansion_state)) (fs : List (List symbolic_char)) (saved : saved_fds) (opts : command_opts)
    | CommandReady (assigns : List (String × List symbolic_char)) (cmd : List symbolic_char) (fs : List (List symbolic_char)) (saved : saved_fds) (opts : command_opts)

    | Pipe (bg : bg_mode) (sts : List stmt)
    | Redir (st : stmt) (rs : (List expanded_redir) × Option expanding_redir × List redir)
    | Background (st : stmt) (rs : (List expanded_redir) × Option expanding_redir × List redir)
    | Subshell (st : stmt) (rs : (List expanded_redir) × Option expanding_redir × List redir)

    | And  (a b : stmt)
    | Or   (a b : stmt)
    | Not  (a : stmt)
    | Semi (a b : stmt)
    | If   (c t e : stmt)

    | While (cond body : stmt)
    | WhileCond (origCond curCond origBody : stmt) (savedEc : Option Nat)
    | WhileRunning (origCond origBody curBody : stmt)

    | For (x : String) (ws : List entry) (body : stmt)
    | ForExpArgs (x : String) (st : expansion_state) (body : stmt)
    | ForExpanded (x : String) (fs : List (List symbolic_char)) (body : stmt)
    | ForRunning (x : String) (fs : List (List symbolic_char)) (origBody curBody : stmt)

    | Case (ws : List entry) (cases : List (List (List entry) × stmt))
    | CaseExpArg (st : expansion_state) (cases : List (List (List entry) × stmt))
    | CaseMatch (s : List symbolic_char) (cases : List (List (List entry) × stmt))
    | CaseCheckMatch (s : List symbolic_char) (pat : expansion_state) (cur : stmt)
        (rest : List (List (List entry) × stmt))

    | Defun (name : String) (body : stmt)

    | Call (outerLoopNest : Nat) (outerParams : List (List symbolic_char)) (fname : String)
        (origBody curBody : stmt)

    | EvalLoop (lineno : Nat) (ctx : parse_context) (src : parse_source)
        (im : interactivity_mode) (lvl : shell_level)
    | EvalLoopCmd (lineno : Nat) (ctx : parse_context) (src : parse_source)
        (im : interactivity_mode) (lvl : shell_level) (st : stmt)

    | Break (n : Nat)
    | Continue (n : Nat)
    | Return
    | Exit

    | Exec (cmdPath cmdName : List symbolic_char) (argv : List (List symbolic_char))
      (env : Map.map String (List symbolic_char)) (mode : binsh_mode)

    | Wait (p : pid) (cm : checking_mode) (steps : Option Nat) (wm : wait_mode)

    | Trapped (sig : signal) (restoreEc : Nat) (handler cont : stmt)
    | CheckedExit (st : stmt)
    | Pushredir (st : stmt) (saved : saved_fds)
    | Done
  deriving Repr

  inductive redir : Type
    | RFile   (rt : redir_type) (n : Nat) (ws : List entry)
    | RDup    (dt : dup_type) (n : Nat) (ws : List entry)
    | RHeredoc (ht : heredoc_type) (n : Nat) (ws : List entry)
  deriving Repr

  inductive expanding_redir : Type
    | XRFile   (rt : redir_type) (n : Nat) (st : expansion_state)
    | XRDup    (dt : dup_type) (n : Nat) (st : expansion_state)
    | XRHeredoc (ht : heredoc_type) (n : Nat) (st : expansion_state)
  deriving Repr

  inductive expanded_redir : Type
    | ERFile   (rt : redir_type) (n : Nat) (s : List symbolic_char)
    | ERDup    (dt : dup_type) (orig : orig_fd_action) (n : Nat) (m : Option Nat)
    | ERHeredoc (ht : heredoc_type) (n : Nat) (s : List symbolic_char)
  deriving Repr

  /- Expansion -/
  inductive expanded_word : Type
    | UsrF
    | ExpS (s : String)
    | UsrS (s : String)
    | At   (fs : List (List symbolic_char))
    | DQuo (s : List symbolic_char)
    | EWSym (sym : sym)
  deriving Repr

  inductive tmp_field : Type
    | WFS
    | FS
    | Field  (s : List symbolic_char)
    | QField (s : List symbolic_char)
  deriving Repr

  /- Symbolic strings -/
  inductive sym : Type
    | SymArith (fs : List (List symbolic_char))
    | SymCommand (st : stmt)
    | SymPat (side : substring_side) (mode : substring_mode) (pat str : List symbolic_char)
  deriving Repr

  inductive symbolic_char : Type
    | C   (c : Char)
    | Sym (s : sym)
  deriving Repr

  inductive expansion_state : Type
    | ExpStart  (opts : expansion_opts) (ws : List entry)
    | ExpExpand (opts : expansion_opts) (ews : List expanded_word) (ws : List entry)
    | ExpSplit  (opts : expansion_opts) (ews : List expanded_word)
    | ExpPath   (opts : expansion_opts) (ifs : List tmp_field)
    | ExpQuote  (opts : expansion_opts) (ifs : List tmp_field)
    | ExpError  (fs : List (List symbolic_char))
    | ExpDone   (fs : List (List symbolic_char))
  deriving Repr

  inductive expansion_step : Type
    | ESTilde  (s : String)
    | ESParam  (s : String)
    | ESCommand (s : String)
    | ESArith  (s : String)
    | ESSplit  (s : String)
    | ESPath   (s : String)
    | ESQuote  (s : String)
    | ESEscape (s : String)
    | ESStep   (s : String)
    | ESNested (a b : expansion_step)
    | ESEval   (es : expansion_step) (xs : evaluation_step)
  deriving Repr

  inductive evaluation_step : Type
    | XSSimple (s : String)
    | XSPipe (s : String)
    | XSRedir (s : String)
    | XSBackground (s : String)
    | XSSubshell (s : String)
    | XSAnd (s : String)
    | XSOr (s : String)
    | XSNot (s : String)
    | XSSemi (s : String)
    | XSIf (s : String)
    | XSWhile (s : String)
    | XSFor (s : String)
    | XSCase (s : String)
    | XSDefun (s : String)
    | XSStack (fname : String) (step : evaluation_step)
    | XSStep (s : String)
    | XSExec (s : String)
    | XSEval (lineno : Nat) (src : parse_source) (s : String)
    | XSWait (s : String)
    | XSTrap (sig : signal) (s : String)
    | XSProc (p : pid) (st : stmt)
    | XSNested (a b : evaluation_step)
    | XSExpand (ev : evaluation_step) (ex : expansion_step)
  deriving Inhabited, Repr

  inductive parse_result : Type
    | ParseDone
    | ParseError (msg : String)
    | ParseNull
    | ParseStmt (st : stmt)
  deriving Inhabited, Repr

end

abbrev words             := List entry
abbrev redir_state       := (List expanded_redir) × Option expanding_redir × List redir
abbrev expanded_words    := List expanded_word
abbrev intermediate_fields := List tmp_field
abbrev symbolic_string   := List symbolic_char
abbrev fields            := List symbolic_string
abbrev env               := Map.map String symbolic_string


  -- termination_by a b => sizeOf a + sizeOf b
  -- decreasing_by repeat' (simp_wf; omega)

/-
  SHELL STATE (not depended by stmt)
-/

structure local_opts where
  local_readonly : Bool
  local_exported : Bool
  deriving Repr, DecidableEq

abbrev local_env := Map.map String (Option symbolic_string × local_opts)

inductive job_stopped
  | TSTP | STOP | TTIN | TTOU
  deriving Repr, DecidableEq, Ord

inductive job_status
  | JobRunning
  | JobStopped (s : job_stopped)
  | JobTerminated (sig : signal)
  | JobDone (ec : Nat)
  deriving Repr, DecidableEq

abbrev pipeline_info := List (pid × stmt)

structure job_info where
  id       : Nat
  pipeline : pipeline_info
  pid      : pid
  cmd      : stmt
  status   : job_status

abbrev history := List (Nat × stmt)

structure shell_state where
  rootpid : pid
  outermost : Bool
  opts : Set.Set sh_opt
  traps : Map.map signal symbolic_string
  supershell_traps : Option (Map.map signal symbolic_string)
  jobs : List job_info
  last_pid : Option pid
  exit_code : Nat
  positional_params : List symbolic_string
  env : Map.map String symbolic_string
  locals : List local_env
  optoff : Option Nat
  readonly : Set.Set String
  exported : Set.Set String
  funcs : Map.map String stmt
  aliases : Map.map String String
  cwd : String
  locale : locale
  loop_nest : Nat
  history : history
  hashes : Map.map String (path × Nat)

def STDIN  : fd := 0
def STDOUT : fd := 1
def STDERR : fd := 2

instance : BEq job_info where
  beq a b := a.id == b.id

instance : Ord job_info where
  compare a b := compare a.id b.id

def job_info_ne (a b : job_info) : Bool := !(a == b)
def job_info_lt (a b : job_info) : Bool := a.id < b.id
def job_info_le (a b : job_info) : Bool := a.id ≤ b.id
def job_info_gt (a b : job_info) : Bool := a.id > b.id
def job_info_ge (a b : job_info) : Bool := a.id ≥ b.id

end Smoosh
