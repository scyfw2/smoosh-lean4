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
import Smoosh.Prelude.symStrFunc

namespace Smoosh

/-- Lem: is_special_param -/
def is_special_param (x : String) : Bool :=
  match Num.readNat (toCharList x) with
  | .error _ => true
  | .ok _  => x ∈ (["@", "*", "#", "?", "-", "$", "!"] : List String)

/-- Lem: assigns_of_env -/
def assigns_of_env (ρ : env) : List (String × symbolic_string) :=
  -- Lem 里的 map (fun (x,v) => (x,v)) 是恒等
  Map.map.toList ρ

/-- Lem: sequence : list stmt -> stmt -/
def sequence : List stmt → stmt
  | []      => .Done
  | [s]     => s
  | s :: ss => .Semi s (sequence ss)

/-- Lem: default_cmd_opts -/
def default_cmd_opts : command_opts :=
  { ran_cmd_subst := false
  , should_fork := true
  , force_simple_command := false
  }

/-- Lem: simple_command : string -> fields -> env -> stmt -/
def simple_command (cmd : String) (args : fields) (ρ : env) : stmt :=
  stmt.CommandReady
    (assigns_of_env ρ)
    (symbolic_string_of_string cmd)
    args
    []
    ({ default_cmd_opts with ran_cmd_subst := true })  -- ensure ec is set

/-- Lem: skip : stmt -/
def skip : stmt :=
  simple_command ":" [] Map.empty

/-- Lem: command_eval : symbolic_string -> stmt -/
def command_eval (cmd : symbolic_string) : stmt :=
  simple_command "eval" [cmd] Map.empty

/-- Lem: string_of_saved_fd -/
def string_of_saved_fd : (fd × saved_fd_info) → String
  | (f, info) =>
      stringFromNat f ++ "|->" ++
        match info with
        | saved_fd_info.Saved f' => stringFromNat f'
        | saved_fd_info.Close    => "-"

/-- Lem: string_of_saved_fds -/
def string_of_saved_fds (sfs : saved_fds) : String :=
  "[" ++ String.intercalate " " (sfs.map string_of_saved_fd) ++ "]"

/-- Lem: pushredir : stmt -> saved_fds -> stmt -/
def pushredir (st : stmt) (sfs : saved_fds) : stmt :=
  match sfs with
  | [] => st
  | _  => .Pushredir st sfs

/-- Lem: with_redirs : stmt -> list expanded_redir -> stmt -/
def with_redirs (st : stmt) (ers : List expanded_redir) : stmt :=
  match ers with
  | [] => st
  | _  => .Redir st (ers, none, [])

/-- Lem: close_fd_and_then : fd -> stmt -> stmt -/
def close_fd_and_then (f : fd) (st : stmt) : stmt :=
  .Semi (.Pushredir .Done [(f, saved_fd_info.Close)]) st

/-- Lem: try_avoid_fork : stmt -> stmt -/
def try_avoid_fork : stmt → stmt
  | .Command assigns args redirs opts =>
      .Command assigns args redirs ({ opts with should_fork := false })
  | .CommandExpArgs assigns est redirs opts =>
      .CommandExpArgs assigns est redirs ({ opts with should_fork := false })
  | .CommandExpRedirs assigns fs rs opts =>
      .CommandExpRedirs assigns fs rs ({ opts with should_fork := false })
  | .CommandExpAssign exp_assigns fs saved opts =>
      .CommandExpAssign exp_assigns fs saved ({ opts with should_fork := false })
  | .CommandReady assigns cmd fs saved opts =>
      .CommandReady assigns cmd fs saved ({ opts with should_fork := false })
  | .Redir st rs =>
      .Redir (try_avoid_fork st) rs
  | st => st

/-- expanded_redir_has_stdin_redir : expanded_redir -> bool -/
def expanded_redir_has_stdin_redir : expanded_redir → Bool
  | .ERFile .From 0 _           => true
  | .ERFile .FromTo 0 _         => true
  | .ERDup .ToFD _ _ (some 1)   => true
  | .ERDup .FromFD _ 1 (some _) => true
  | .ERHeredoc _ 1 _ => true
  | _                           => false

/-- Lem: is_terminating_control : stmt -> bool -/
def is_terminating_control : stmt → Bool
  | .Exit       => true
  | .Return     => true
  | .Break _    => true
  | .Continue _ => true
  | .Done       => true
  | _               => false

/-- Lem: combine_redirs : redir_state -> redir_state -> redir_state -/
def combine_redirs : redir_state → redir_state → redir_state
  | (ers1, er1, rs1), (ers2, er2, rs2) =>
      let er :=
        match er1, er2 with
        | none,    none    => none
        | some er, none    => some er
        | none,    some er => some er
        | some _,  some _  =>
            panic! "couldn't combine two in-flight redirects"
      (ers1 ++ ers2, er, rs1 ++ rs2)

/-- Lem: get_expanding_redir_state : expanding_redir -> expansion_state -/
def get_expanding_redir_state : expanding_redir → expansion_state
  | .XRFile _ _ es    => es
  | .XRDup _ _ es     => es
  | .XRHeredoc _ _ es => es

/-- Lem: is_heredoc : expanding_redir -> bool -/
def is_heredoc : expanding_redir → Bool
  | .XRFile _ _ _    => false
  | .XRDup _ _ _     => false
  | .XRHeredoc _ _ _ => true

/-- Lem: set_expanding_redir_state : expansion_state -> expanding_redir -> expanding_redir -/
def set_expanding_redir_state : expansion_state → expanding_redir → expanding_redir
  | es, .XRFile ty src _    => .XRFile ty src es
  | es, .XRDup ty src _     => .XRDup ty src es
  | es, .XRHeredoc ty src _ => .XRHeredoc ty src es

/-- Lem: parse_source_for_dot : parse_source -> bool -/
def parse_source_for_dot : parse_source → Bool
  | .ParseFile _ _   => true
  | .ParseString _ _ => false
  | .ParseSTDIN      => false

/-- Lem: parse_source_propagates_control : parse_source -> bool -/
def parse_source_propagates_control : parse_source → Bool
  | .ParseSTDIN                 => true
  | .ParseString .ParseEval _    => true
  | .ParseString .ParseTrap _    => false
  | .ParseFile _ _              => false

/-- Lem: is_active_job : job_info -> bool -/
def is_active_job (job : job_info) : Bool :=
  match job.status with
  | .JobRunning      => true
  | .JobStopped _    => true
  | .JobTerminated _ => false
  | .JobDone _       => false

/-- Lem: string_of_job_status : job_status -> string -/
def string_of_job_status : job_status → String
  | .JobRunning           => "Running"
  | .JobStopped .TSTP      => "Stopped (SIGTSTP)"
  | .JobStopped .STOP      => "Stopped (SIGSTOP)"
  | .JobStopped .TTIN      => "Stopped (SIGTTIN)"
  | .JobStopped .TTOU      => "Stopped (SIGTTOU)"
  | .JobTerminated signal => "Terminated (" ++ string_of_signal signal ++ ")"
  | .JobDone 0            => "Done"
  | .JobDone code         => "Done (" ++ stringFromNat code ++ ")"

/-- Lem: cur_prev_jobs : list job_info -> nat * nat -/
def cur_prev_jobs : List job_info → Nat × Nat
  | []              => (0, 0)  -- doesn't matter
  | [job]           => (job.id, job.id)
  | cur :: prev :: _ => (cur.id, prev.id)

/-- Lem: string_of_job_number : nat * nat -> job_info -> string -/
def string_of_job_number : Nat × Nat → job_info → String
  | (cur_id, prev_id), job =>
      "[" ++ stringFromNat job.id ++ "] " ++
        (if job.id = cur_id then "+"
         else if job.id = prev_id then "-"
         else " ") ++ " "

/-- Lem: jobs_mode type -/
inductive jobs_mode where
  | JobsNormal
  | JobsTerse
  | JobsLong
  | JobsFGCommand
  | JobsBGCommand
deriving Repr, DecidableEq

/-- Lem: padded_string_of_job_status job = pad_right (string_of_job_status job.status) 25 -/
def padded_string_of_job_status (job : job_info) : String :=
  pad_right (string_of_job_status job.status) 25

/-- Lem: ran_command_substitution : expansion_step -> bool -/
def ran_command_substitution : expansion_step → Bool
  | .ESTilde _s        => false
  | .ESParam _s        => false
  | .ESCommand _s      => true
  | .ESArith _s        => false
  | .ESSplit _s        => false
  | .ESPath _s         => false
  | .ESQuote _s        => false
  | .ESEscape _s       => false
  | .ESStep _s         => false
  | .ESNested outer inner =>
      ran_command_substitution outer || ran_command_substitution inner
  | .ESEval _estep' _step => true


end Smoosh
