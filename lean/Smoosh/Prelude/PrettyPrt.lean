import Smoosh.Compat.PervasivesExtra
import Smoosh.BuildInfo
import Smoosh.Platform.SignalPlatform
import Smoosh.Prelude.FilePerm
import Smoosh.Prelude.AST
import Smoosh.Prelude.ShellOptions
import Smoosh.Map
import Smoosh.Prelude.Parser
import Smoosh.Num
import Smoosh.Signal
import Smoosh.Prelude.Redirect
import Smoosh.Prelude.ASTHelper
import Smoosh.Prelude.symStrFunc

namespace Smoosh

/-- Lem: braces -/
def braces (s : String) : String :=
  "{ " ++ s ++ " ; }"

/-- Lem: background -/
def background (s : String) : String :=
  "{ " ++ s ++ " & }"

/-- Lem: show_unless -/
def show_unless (expected actual : Nat) : String :=
  if expected = actual then "" else stringFromNat actual

/-- Lem: string_of_pid -/
def string_of_pid (pid : Nat) : String :=
  stringFromNat pid

/-- Lem: string_of_simple -/
def string_of_simple {α c r : Type u}
    (f_a : α → String) (f_c : c → String) (f_r : r → String)
    (assigns : List (String × α)) (cmds : c) (redirs : r) : String :=
  let s_assigns :=
    String.intercalate " " (List.map (fun (va : String × α) => va.1 ++ "=" ++ f_a va.2) assigns)
  let s_cmds := f_c cmds
  let s_redirs := f_r redirs
  spaced_many [s_assigns, s_cmds, s_redirs]

mutual
  /-- Lem: val string_of_symbolic : sym -> string -/
  partial def string_of_symbolic (sym : sym) : String :=
    match sym with
    | .SymArith f => "<<arith(" ++ string_of_fields f ++ ")>>"
    | .SymCommand stmt => "<<eval(" ++ string_of_stmt stmt ++ ")>>"
    | .SymPat side mode pat s =>
      "<<pat(" ++ string_of_substring side mode ++ ","
               ++ string_of_symbolic_string pat ++ ","
               ++ string_of_symbolic_string s ++ ")>>"

  /-- Lem: val string_of_symbolic_char : symbolic_char -> string -/
  partial def string_of_symbolic_char (c : symbolic_char) : String :=
    match c with
    | .C ch     => String.ofList [ch]
    | .Sym sym  => string_of_symbolic sym

  /-- Lem: val char_list_of_symbolic_string : symbolic_string -> list char -/
  partial def char_list_of_symbolic_string (sym_str : symbolic_string) : List Char :=
    match sym_str with
    | [] => []
    | (.C c)::cs => c :: char_list_of_symbolic_string cs
    | (.Sym sym)::cs => toCharList (string_of_symbolic sym) ++ char_list_of_symbolic_string cs

  /-- Lem: val string_of_symbolic_string : symbolic_string -> string -/
  partial def string_of_symbolic_string (sym_str : symbolic_string) : String :=
    match sym_str with
    | [] => ""
    | c::cs => string_of_symbolic_char c ++ string_of_symbolic_string cs

  /-- Lem: val string_of_fields : fields -> string -/
  partial def string_of_fields (fs : fields) : String :=
    match fs with
    | [] => ""
    | [f] => string_of_symbolic_string f
    | f::fs' => string_of_symbolic_string f ++ " " ++ string_of_fields fs'

  /-- Lem: val string_of_stmt : stmt -> string -/
  partial def string_of_stmt (c : stmt) : String :=
    match c with
    | .Command assigns cmds redirs _opts =>
        string_of_simple string_of_words string_of_words string_of_redirs
          assigns cmds redirs
    | .CommandExpArgs assigns cmds redirs _opts =>
        string_of_simple string_of_words string_of_expansion_state string_of_redirs
          assigns cmds redirs
    | .CommandExpRedirs assigns cmds redir_state _opts =>
        string_of_simple string_of_words string_of_fields string_of_redir_state
          assigns cmds redir_state
    | .CommandExpAssign assigns cmds saved_fds _opts =>
        string_of_simple string_of_expansion_state string_of_fields (fun _ => "")
          assigns cmds saved_fds
    | .CommandReady assigns cmd args saved_fds _opts =>
        string_of_simple string_of_symbolic_string string_of_fields (fun _ => "")
          assigns (cmd :: args) saved_fds
    | .Pipe mode cmds =>
        let p := String.intercalate " | " (List.map string_of_stmt cmds)
        if is_bg mode then background p else p
    | .Redir cmd redir_state =>
        spaced (string_of_stmt cmd) (string_of_redir_state redir_state)
    | .Background cmd redir_state =>
        background (spaced (string_of_stmt cmd) (string_of_redir_state redir_state))
    | .Subshell cmd redir_state =>
        spaced (parens (string_of_stmt cmd)) (string_of_redir_state redir_state)
    | .And cmd1 cmd2 =>
        string_of_stmt cmd1 ++ " && " ++ string_of_stmt cmd2
    | .Or cmd1 cmd2 =>
        string_of_stmt cmd1 ++ " || " ++ string_of_stmt cmd2
    | .Semi cmd1 cmd2 =>
        string_of_stmt cmd1 ++ " ; " ++ string_of_stmt cmd2
    | .Not cmd =>
        "! " ++ string_of_stmt cmd
    | .If c1 c2 c3 =>
        string_of_if c1 c2 c3
    | .While c1 c2 => string_of_while c1 c2
    | .WhileCond c cur body _saved_ec =>
        "if " ++ string_of_stmt cur
        ++ "; then " ++ string_of_stmt body
        ++ "; " ++ string_of_while c body ++ "; fi"
    | .WhileRunning c body cur =>
        string_of_stmt cur ++ "; " ++ string_of_while c body
    | .For x w body =>
        "for " ++ x ++ " in " ++ string_of_words w
        ++ "; do " ++ string_of_stmt body ++ "; done"
    | .ForExpArgs x exp_state body =>
        "for " ++ x ++ " in " ++ string_of_expansion_state exp_state
        ++ "; do " ++ string_of_stmt body ++ "; done"
    | .ForExpanded x f body =>
        "for " ++ x ++ " in " ++ string_of_fields f
        ++ "; do " ++ string_of_stmt body ++ "; done"
    | .ForRunning x f body cur =>
        string_of_stmt cur ++ "; "
        ++ "for " ++ x ++ " in " ++ string_of_fields f
        ++ "; do " ++ string_of_stmt body ++ "; done"
    | .Case w cs =>
        "case " ++ string_of_words w ++ " in "
        ++ String.intercalate " " (List.map string_of_case cs) ++ " esac"
    | .CaseExpArg exp cs =>
        "case " ++ string_of_expansion_state exp ++ " in "
        ++ String.intercalate " " (List.map string_of_case cs) ++ " esac"
    | .CaseMatch s cs =>
        "case " ++ string_of_symbolic_string s ++ " in "
        ++ String.intercalate " " (List.map string_of_case cs) ++ " esac"
    | .CaseCheckMatch s exp st cs =>
        "case " ++ string_of_symbolic_string s ++ " in "
        ++ string_of_expansion_state exp ++ ") " ++ string_of_stmt st ++ ";; "
        ++ String.intercalate " " (List.map string_of_case cs) ++ " esac"
    | .Defun name cmd =>
        name ++ "() {\n" ++ string_of_stmt cmd ++ "\n}"
    | .Call _loopnest _argv _f _body c =>
        string_of_stmt c
    | .EvalLoop _linno _ctx (.ParseFile _src _push) _i _tl =>
        ": EvalLoop"
    | .EvalLoop _linno _ctx (.ParseString .ParseEval cmd) _i _tl =>
        "eval '" ++ cmd ++ "'"
    | .EvalLoop _linno _ctx (.ParseString .ParseTrap cmd) _i _tl =>
        "eval '" ++ cmd ++ "' # from trap"
    | .EvalLoop _linno _ctx .ParseSTDIN _i _tl =>
        ": EvalLoop"
    | .EvalLoopCmd _linno _ctx (.ParseFile _src _push) _i _tl c =>
        string_of_stmt c
    | .EvalLoopCmd _linno _ctx (.ParseString .ParseEval cmd) _i _tl c =>
        string_of_stmt c ++ " # in eval '" ++ cmd ++ "'"
    | .EvalLoopCmd _linno _ctx (.ParseString .ParseTrap cmd) _i _tl c =>
        string_of_stmt c ++ " # in eval '" ++ cmd ++ "' from trap"
    | .EvalLoopCmd _linno _ctx .ParseSTDIN _i _tl c =>
        string_of_stmt c
    | .Break n =>
        "break " ++ stringFromNat n
    | .Continue n =>
        "continue " ++ stringFromNat n
    | .Return => "return"
    | .Exit => "exit"
    | .Exec _cmd cmd_argv0 args _env _binsh => spaced "exec" (string_of_fields (cmd_argv0 :: args))
    | .Wait n _checked _steps _mode => "wait " ++ string_of_pid n
    | .Trapped signal _ec c_handler c_cont =>
        ": trap on " ++ string_of_signal signal ++ " ; "
        ++ string_of_stmt c_handler ++ " ; : end trap ; " ++ string_of_stmt c_cont
    | .CheckedExit c => ": ignoring errexit ; " ++ string_of_stmt c ++ " ; : resuming errexit"
    | .Pushredir s _saved => string_of_stmt s
    | .Done => ": Done"

  /-- Lem: string_of_while -/
  partial def string_of_while (c body : stmt) : String :=
    match c with
    | .Not c' => "until " ++ string_of_stmt c' ++ "; do " ++ string_of_stmt body ++ "; done "
    | _ => "while " ++ string_of_stmt c ++ "; do " ++ string_of_stmt body ++ "; done "

  /-- Lem: string_of_if -/
  partial def string_of_if (c t e : stmt) : String :=
    "if " ++ string_of_stmt c
    ++ "; then " ++ string_of_stmt t
    ++ (match e with
        | .Command [] [] [] _ =>
            "; fi"
        | .If c' t' e' =>
            "; el" ++ string_of_if c' t' e'
        | _ =>
            "; else " ++ string_of_stmt e ++ "; fi")

  /-- Lem: string_of_case -/
  partial def string_of_case (wc : List words × stmt) : String :=
    let w := wc.1
    let c := wc.2
    String.intercalate "|" (List.map string_of_words w) ++ ") " ++ string_of_stmt c ++ ";;"

  /-- Lem: string_of_rfile -/
  partial def string_of_rfile (ty : redir_type) (fd : Nat) : String :=
    match ty with
    | .To      => show_unless 1 fd ++ ">"
    | .Clobber => show_unless 1 fd ++ ">|"
    | .From    => show_unless 0 fd ++ "<"
    | .FromTo  => show_unless 0 fd ++ "<>"
    | .Append  => show_unless 1 fd ++ ">>"

  /-- Lem: string_of_rdup -/
  partial def string_of_rdup (ty : dup_type) (fd : Nat) : String :=
    match ty with
    | .ToFD   => show_unless 1 fd ++ ">&"
    | .FromFD => show_unless 0 fd ++ "<&"

  /-- Lem: string_of_heredoc -/
  partial def string_of_heredoc (ty : heredoc_type) (fd : Nat) (heredoc : String) : String :=
    let marker := "EOF"
    show_unless 0 fd ++ "<<"
    ++ (if ty = .XHere then marker else "'" ++ marker ++ "'")
    ++ "\n" ++ heredoc ++ marker ++ "\n"

  /-- Lem: string_of_redir -/
  partial def string_of_redir (r : redir) : String :=
    match r with
    | .RFile ty fd a    => string_of_rfile ty fd ++ string_of_words a
    | .RDup ty fd tgt   => string_of_rdup ty fd ++ string_of_words tgt
    | .RHeredoc ty fd a => string_of_heredoc ty fd (string_of_words a)

  /-- Lem: string_of_expanding_redir -/
  partial def string_of_expanding_redir (exp_redir : Option expanding_redir) : String :=
    match exp_redir with
    | none => ""
    | some (.XRFile ty fd exp_state) =>
      string_of_rfile ty fd ++ string_of_expansion_state exp_state
    | some (.XRDup ty fd exp_state) =>
      string_of_rdup ty fd ++ string_of_expansion_state exp_state
    | some (.XRHeredoc ty fd exp_state) =>
      string_of_heredoc ty fd (string_of_expansion_state exp_state)

  /-- Lem: string_of_expanded_redir -/
  partial def string_of_expanded_redir (er : expanded_redir) : String :=
    match er with
    | .ERFile ty fd a => string_of_rfile ty fd ++ string_of_symbolic_string a
    | .ERDup ty _close_orig fd tgt =>
      string_of_rdup ty fd ++
        match tgt with
        | none => "-"
        | some fd_tgt => stringFromNat fd_tgt
    | .ERHeredoc ty fd a => string_of_heredoc ty fd (string_of_symbolic_string a)

  /-- Lem: string_of_expanded_redirs -/
  partial def string_of_expanded_redirs (ers : List expanded_redir) : String :=
    String.intercalate " " (List.map string_of_expanded_redir ers)
  /-- Lem: string_of_redirs -/
  partial def string_of_redirs (rs : List redir) : String :=
    String.intercalate " " (List.map string_of_redir rs)

  /-- Lem: string_of_redir_state -/
  partial def string_of_redir_state (st : redir_state) : String :=
    let ers := st.1
    let exp_redir := st.2.1
    let rs := st.2.2
    let s_ers := string_of_expanded_redirs ers
    let s_exp_redir := string_of_expanding_redir exp_redir
    let s_rs := string_of_redirs rs
    spaced_many [s_ers, s_exp_redir, s_rs]

  /-- Lem: string_of_tmp_field -/
  partial def string_of_tmp_field (tf : tmp_field) : String :=
    match tf with
    | .WFS       => " "
    | .FS        => " "
    | .Field s   => string_of_symbolic_string s
    | .QField s  => "\"" ++ string_of_symbolic_string s ++ "\""

  /-- Lem: string_of_intermediate_fields -/
  partial def string_of_intermediate_fields (ifs : intermediate_fields) : String :=
    match ifs with
    | [] => ""
    | tf::ifs' => string_of_tmp_field tf ++ string_of_intermediate_fields ifs'

  /-- Lem: debug_expanded_words -/
  partial def debug_expanded_words (ew : expanded_words) : String :=
    match ew with
    | [] => ""
    | .UsrF::ws => "<UsrF>" ++ debug_expanded_words ws
    | .ExpS s::ws => "<ExpS(" ++ s ++ ")>" ++ debug_expanded_words ws
    | .DQuo ss::ws => "<DQuo(" ++ string_of_symbolic_string ss ++ ")>" ++ debug_expanded_words ws
    | .At fs::ws =>
        "<At(" ++ String.intercalate "," (List.map string_of_symbolic_string fs) ++ ")>"
        ++ debug_expanded_words ws
    | .EWSym sym::ws => "<EWSym(" ++ string_of_symbolic sym ++ ")>" ++ debug_expanded_words ws
    | .UsrS s::ws => "<UsrS(" ++ s ++ ")>" ++ debug_expanded_words ws

  /-- Lem: string_of_expanded_words -/
  partial def string_of_expanded_words (ew : expanded_words) : String :=
    match ew with
    | [] => ""
    | .UsrF::ws => " " ++ string_of_expanded_words ws
    | .ExpS s::ws => s ++ string_of_expanded_words ws
    | .DQuo ss::ws =>
      -- we don't include the quotes, since they'll be ultimately erased anyway!
      "\"" ++ string_of_symbolic_string ss ++ "\"" ++ string_of_expanded_words ws
    | .At fs::ws =>
      -- we collapse the result of $@ expansion, too. special cased in expand_control
      string_of_fields fs ++ string_of_expanded_words ws
    | .EWSym sym::ws => string_of_symbolic sym ++ string_of_expanded_words ws
    | .UsrS s::ws => s ++ string_of_expanded_words ws

  /-- Lem: val string_of_words : words -> string -/
  partial def string_of_words (w : words) : String :=
    let parts := List.map string_of_entry w
    List.foldr (fun s acc => s ++ acc) "" parts
  /-- Lem: val string_of_entry : entry -> string -/
  partial def string_of_entry (e : entry) : String :=
    match e with
    | .S str  => str
    | .ESym _ => "<<SYMBOLIC>>"
    | .K code => string_of_control code
    | .F      => " "

  /-- Lem: string_of_control -/
  partial def string_of_control (code : control) : String :=
    match code with
    | .Tilde user => "~" ++ user
    | .Param var .Normal => "$" ++ var
    | .Param var .Length => "${#" ++ var ++ "}"
    | .Param var fmt => "${" ++ var ++ string_of_format fmt ++ "}"
    | .LAssign var ew w =>
        "${" ++ var ++ "=" ++ string_of_expanded_words ew ++ string_of_words w ++ "}"
    | .LMatch f _side _mode _ew _w => string_of_fields f
    | .LError var ew w =>
        "${" ++ var ++ "?" ++ string_of_expanded_words ew ++ string_of_words w ++ "}"
    | .Backtick c =>
        "$( " ++ string_of_stmt c ++ " )"
    | .LBacktick c _pid _fd => "$( " ++ string_of_stmt c ++ " )"
    | .LBacktickWait c _pid _s => "$( " ++ string_of_stmt c ++ " )"
    | .Arith ew w => "$(( " ++ string_of_expanded_words ew ++ string_of_words w ++ " ))"
    | .Quote ew w => "\"" ++ string_of_expanded_words ew ++ string_of_words w ++ "\""
    | .Escape c => String.ofList [ '\\', c ]

  /-- Lem: string_of_format -/
  partial def string_of_format (fmt : format) : String :=
    match fmt with
    | .Normal     => ""
    | .Length     => "#"
    | .Default w  => "-"  ++ string_of_words w
    | .NDefault w => ":-" ++ string_of_words w
    | .Assign w   => "="  ++ string_of_words w
    | .NAssign w  => ":=" ++ string_of_words w
    | .Error w    => "?"  ++ string_of_words w
    | .NError w   => ":?" ++ string_of_words w
    | .Alt w      => "+"  ++ string_of_words w
    | .NAlt w     => ":+" ++ string_of_words w
    | .Substring side mode w => string_of_substring side mode ++ string_of_words w

  /-- Lem: string_of_substring -/
  partial def string_of_substring (side : substring_side) (mode : substring_mode) : String :=
    let sym :=
      match side with
      | .Prefix => "#"
      | .Suffix => "%"
    match mode with
    | .Longest  => sym ++ sym
    | .Shortest => sym

  /-- Lem: string_of_expansion_state -/
  partial def string_of_expansion_state (exp_state : expansion_state) : String :=
    match exp_state with
    | .ExpStart _opts w => string_of_words w
    | .ExpExpand _opts ew w => string_of_expanded_words ew ++ string_of_words w
    | .ExpSplit _opts ew => string_of_expanded_words ew
    | .ExpPath _opts ifs => string_of_intermediate_fields ifs
    | .ExpQuote _opts ifs => string_of_intermediate_fields ifs
    | .ExpError f => string_of_fields f
    | .ExpDone f => string_of_fields f

  /-- Lem: string_of_expansion_step -/
  partial def string_of_expansion_step (estep : expansion_step) : String :=
    match estep with
    | .ESTilde s   => spaced "Tilde" s
    | .ESParam s   => spaced "Param" s
    | .ESCommand s => spaced "Command" s
    | .ESArith s   => spaced "Arith" s
    | .ESSplit s   => spaced "Split" s
    | .ESPath s    => spaced "Path" s
    | .ESQuote s   => spaced "Quote" s
    | .ESEscape s  => spaced "Escape" s
    | .ESStep s    => spaced "Step" s
    | .ESNested outer inner =>
      parens (string_of_expansion_step outer) ++ " " ++
      parens (string_of_expansion_step inner)
    | .ESEval estep' step =>
      parens (string_of_expansion_step estep') ++ " " ++
      parens (string_of_evaluation_step step)

  /-- Lem: string_of_evaluation_step -/
  partial def string_of_evaluation_step (step : evaluation_step) : String :=
    match step with
    | .XSSimple s     => spaced "Simple" s
    | .XSPipe s       => spaced "Pipe" s
    | .XSRedir s      => spaced "Redir" s
    | .XSBackground s => spaced "Background" s
    | .XSSubshell s   => spaced "Subshell" s
    | .XSAnd s        => spaced "And" s
    | .XSOr s         => spaced "Or" s
    | .XSNot s        => spaced "Not" s
    | .XSSemi s       => spaced "Semi" s
    | .XSIf s         => spaced "If" s
    | .XSWhile s      => spaced "While" s
    | .XSFor s        => spaced "For" s
    | .XSCase s       => spaced "Case" s
    | .XSDefun s      => spaced "Defun" s
    | .XSStack s step'=> spaced "Stack" s ++ " " ++ parens (string_of_evaluation_step step')
    | .XSStep s       => spaced "Step" s
    | .XSExec s       => spaced "Exec" s
    | .XSEval linno src s =>
        "EvalLoop " ++ stringFromNat linno ++ " " ++ string_of_parse_source src
        ++ (if s = "" then "" else " " ++ s)
    | .XSWait s        => spaced "Wait" s
    | .XSTrap signal s => "Trap " ++ spaced (string_of_signal signal) s
    | .XSProc _pid c   => "Proc " ++ string_of_stmt c
    | .XSNested outer inner =>
      parens (string_of_evaluation_step outer) ++ " " ++
      parens (string_of_evaluation_step inner)
    | .XSExpand step' estep =>
      parens (string_of_evaluation_step step') ++ " " ++
      parens (string_of_expansion_step estep)

  /-- Lem: string_of_parse_source -/
  partial def string_of_parse_source (src : parse_source) : String :=
    match src with
    | .ParseSTDIN => "<STDIN>"
    | .ParseString _ cmd => "'" ++ cmd ++ "'"
    | .ParseFile file _push => file

end

/-- Lem: string_of_job_pipeline -/
def string_of_job_pipeline
    (curjob :  Nat × Nat) (job : job_info)
    (pipeline : List (Nat × stmt)) (first : Bool) : String :=
  match pipeline with
  | [] => ""
  | (pid, st)::pipeline' =>
      (if first then string_of_job_number curjob job else "      ")
      ++ pad_right (stringFromNat pid) 6
      ++ (if first then padded_string_of_job_status job
          else String.ofList (List.replicate 23 ' ') ++ "| ")
      ++ string_of_stmt st ++ "\n"
      ++ string_of_job_pipeline curjob job pipeline' false

/-- Lem: string_of_job -/
def string_of_job (mode : jobs_mode) (curjob : Nat × Nat) (job : job_info) : String :=
  match mode with
  | .JobsTerse => stringFromNat job.pid ++ "\n"
  | .JobsFGCommand => string_of_stmt job.cmd ++ "\n"
  | .JobsBGCommand => "[" ++ stringFromNat job.id ++ "] " ++ string_of_stmt job.cmd ++ "\n"
  | .JobsNormal =>
    string_of_job_number curjob job
    ++ padded_string_of_job_status job
    ++ string_of_stmt job.cmd ++ "\n"
  | .JobsLong => string_of_job_pipeline curjob job job.pipeline true

/-- Lem: val nat_of_symbolic_string : symbolic_string -> either string nat -/
def nat_of_symbolic_string (ss : symbolic_string) : Except String Nat :=
  match try_concrete ss with
  | none =>
      .error ("can't parse number in symbolic string '" ++ string_of_symbolic_string ss ++ "'")
  | some s =>
      Num.readNat s.toList

/-- Lem: val split_equal : string -> symbolic_string -> string * maybe symbolic_string -/
def split_equal (var : String) (ss : symbolic_string) : String × Option symbolic_string :=
  match ss with
  | [] => (var, none)
  | (.C '=') :: ss' => (var, some ss')
  | (.C c) :: ss' => split_equal (var ++ String.ofList [c]) ss'
  | _ => (var ++ string_of_symbolic_string ss, none)

/-- Lem: val try_split_assign : symbolic_string -> string * maybe symbolic_string -/
def try_split_assign (ss : symbolic_string) : String × Option symbolic_string :=
  split_equal "" ss

/-- Lem: val try_extract_field : fields -> either string symbolic_string -/
def try_extract_field (f : fields) : Except String symbolic_string :=
  match f with
  | [s] => .ok s
  | []  => .error "empty redirect target"
  | _   => .error ("redirect target wasn't a single field: '" ++ string_of_fields f ++ "'")

/-- Lem: val try_extract_dup_tgt : symbolic_string -> either string (maybe nat) -/
def try_extract_dup_tgt (ss : symbolic_string) : Except String (Option Nat) :=
  match ss with
  | [.C '-'] => .ok none
  | _ =>
    match Num.readNat (string_of_symbolic_string ss |>.toList) with
    | .error err => .error ("invalid file descriptor: " ++ err)
    | .ok n      => .ok (some n)

/-- Lem: val try_extract_dup_tgt : symbolic_string -> either string (maybe nat) -/
def try_expand_redir (er : expanding_redir) (f : fields) : Except String expanded_redir :=
  match er, try_extract_field f with
  | .XRHeredoc ty src _, _ =>
      .ok (.ERHeredoc ty src (symbolic_string_of_fields f))
  | _, .error err => .error err
  | .XRFile ty src _, .ok ss => .ok (.ERFile ty src ss)
  | .XRDup ty src _, .ok ss =>
    match try_extract_dup_tgt ss with
    | .error err  => .error err
    | .ok tgt  => .ok (.ERDup ty .LeaveOrig src tgt)

/-- Lem: val try_command_name : forall 'a. ('a -> string) -> 'a -> set string -/
def try_command_name {α : Type u} (conv : α → String) (cmds : α) : Set.Set String :=
  let str := conv cmds
  let cs  := str.toList
  let (first, _rest) := break_on_esc false ' ' cs
  if first.isEmpty then .empty else .singleton (String.ofList first)

/-- Lem: try_command_words -/
def try_command_words (cmds : words) : String :=
  match cmds with
  | .S cmd :: _ => cmd
  | _ => ""

/-- Lem: try_command_expanded_words -/
def try_command_expanded_words (cmds : expanded_words) : String :=
  match cmds with
  | .UsrS cmd :: _ => cmd
  | .ExpS cmd :: _ => cmd
  | _ => ""

/-- Lem: try_command_intermediate_fields -/
def try_command_intermediate_fields (cmds : intermediate_fields) : String :=
  match cmds with
  | .Field cmd :: _  => string_of_symbolic_string cmd
  | .QField cmd :: _ => string_of_symbolic_string cmd
  | _ => ""

/-- Lem: try_command_fields -/
def try_command_fields (cmds : fields) : String :=
  match cmds with
  | [] => ""
  | cmd :: _ => string_of_symbolic_string cmd

/-- Lem: try_command_expansion_state -/
def try_command_expansion_state (es : expansion_state) : String :=
  match es with
  | .ExpStart _eo w => try_command_words w
  | .ExpExpand _eo [] w => try_command_words w
  | .ExpExpand _eo e _w => try_command_expanded_words e
  | .ExpSplit _eo e => try_command_expanded_words e
  | .ExpPath _eo i => try_command_intermediate_fields i
  | .ExpQuote _eo i => try_command_intermediate_fields i
  | .ExpError _ => ""
  | .ExpDone f => try_command_fields f

/-- Lem: val collect_command_names : stmt -> set string -/
partial def collect_command_names : stmt → Set.Set String
  | .Command _assigns cmds _redirs _opts => try_command_name try_command_words cmds
  | .CommandExpArgs _assigns cmds _redirs _opts => try_command_name string_of_expansion_state cmds
  | .CommandExpRedirs _assigns cmds _redir_state _opts => try_command_name try_command_fields cmds
  | .CommandExpAssign _assigns cmds _saved_fds _opts => try_command_name try_command_fields cmds
  | .CommandReady _assigns cmd _args _saved_fds _opts => .singleton (string_of_symbolic_string cmd)
  | .Pipe _mode cmds => .unions (cmds.map collect_command_names)
  | .Redir cmd _ => collect_command_names cmd
  | .Background cmd _ => collect_command_names cmd
  | .Subshell cmd _ => collect_command_names cmd
  | .And cmd1 cmd2 => .union (collect_command_names cmd1) (collect_command_names cmd2)
  | .Or cmd1 cmd2 => .union (collect_command_names cmd1) (collect_command_names cmd2)
  | .Semi cmd1 cmd2 => .union (collect_command_names cmd1) (collect_command_names cmd2)
  | .Not cmd => collect_command_names cmd
  | .If c1 c2 c3 =>
    .unions [collect_command_names c1,
             collect_command_names c2,
             collect_command_names c3]
  | .While c1 c2 => .union (collect_command_names c1) (collect_command_names c2)
  | .WhileCond c cur body _ =>
    .unions [collect_command_names c,
             collect_command_names cur,
             collect_command_names body]
  | .WhileRunning c body cur =>
    .unions [collect_command_names c,
             collect_command_names cur,
             collect_command_names body]
  | .For _ _ c => collect_command_names c
  | .ForExpArgs _ _ body => collect_command_names body
  | .ForExpanded _ _ body => collect_command_names body
  | .ForRunning _ _ body cur =>
      .union (collect_command_names body) (collect_command_names cur)
  | .Case _ cs => .unions (cs.map (fun (_pat, c) => collect_command_names c))
  | .CaseExpArg _ cs => .unions (cs.map (fun (_pat, c) => collect_command_names c))
  | .CaseMatch _ cs => .unions (cs.map (fun (_pat, c) => collect_command_names c))
  | .CaseCheckMatch _ _ c cs =>
    .unions ((([], c) :: cs).map (fun (_pat, c) => collect_command_names c))
  | .Defun _ cmd => collect_command_names cmd
  | .Call _ _ _ body c =>
      .union (collect_command_names body) (collect_command_names c)
  | .EvalLoop _ _ _ _ _ => .empty
  | .EvalLoopCmd _ _ _ _ _ c => collect_command_names c
  | .Break _ | .Continue _ | .Return | .Exit | .Wait _ _ _ _ | .Done =>
    .empty
  | .Exec cmd _ _ _ _ => .singleton (string_of_symbolic_string cmd)
  | .Trapped _ _ h k =>
    .union (collect_command_names h) (collect_command_names k)
  | .CheckedExit c => collect_command_names c
  | .Pushredir c _ => collect_command_names c

end Smoosh
