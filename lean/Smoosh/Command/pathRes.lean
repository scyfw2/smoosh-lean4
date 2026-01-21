import Smoosh.Smoosh
import Smoosh.Fields
import Smoosh.Test
import Smoosh.Command.builtin
import Smoosh.os.All

universe u v

open Smoosh

variable
{α : Type u}
{β : Type v}


/-- Lem: resolve_path_with : (path -> bool) -> list path -> string -> maybe path -/
def resolve_path_with (ok : path → Bool) : List path → String → Option path
  | [], _ => none
  | ("" : path) :: path', name =>
    let altered : path := ("./" ++ name)
    if ok altered then
      some altered
    else
      resolve_path_with ok path' name
  | pwd :: path', name =>
    let altered : path := join_path pwd name
    if ok altered then
      some altered
    else
      resolve_path_with ok path' name

/-- Lem: command_path_ok : forall 'a. OS 'a => os_state 'a -> path -> bool -/
def command_path_ok [OS α] (s0 : os_state α) (p : path) : Bool :=
  file_exists s0 p && (file_type_follow s0 p = some .FileRegular)

/-- Lem: resolve_command_name_in_path
    : forall 'a. OS 'a =>
        os_state 'a -> path (* PATH *) -> string (* program *) -> os_state 'a * maybe string -/
def resolve_command_name_in_path [OS α]
    (s0 : os_state α) (pathEnv : path) (prog : String) : os_state α × Option String :=
  let progl := toCharList prog
  if List.elem ('/' : Char) progl then
  /-
   If the command name contains at least one <slash>, the shell
   shall execute the utility in a separate utility environment
   with actions equivalent to calling the execl() function defined
   in the System Interfaces volume of POSIX.1-2008 with the path
   and arg0 arguments set to the command name, and the remaining
   execl() arguments set to the command arguments (if any) and the
   null terminator.
  -/
    ( s0, some <|
      match progl with
      | ('/' : Char) :: _ => prog
      | _                 => (physical_cwd s0) ++ "/" ++ prog
    )
  else
    let (s1, hashed) := hash_lookup s0 (command_path_ok s0) prog
    match hashed with
    | none =>
    /-
     Otherwise, the command shall be searched for using the PATH
     environment variable as described in XBD Environment Variables *)
    -/
        -- TODO PERFORMANCE: pre-split PATH
      let paths := split_string_on true (':' : Char) pathEnv
      let m_path := resolve_path_with (command_path_ok s0) paths prog
      let s2 :=
        match m_path with
        | none      => s1
        | some pth  => hash_insert s1 prog pth
      (s2, m_path)
    | some pth =>
      (s1, some pth)

/-- Lem: resolve_command_name : forall 'a. OS 'a =>
                           os_state 'a -> string -> os_state 'a * maybe string -/
def resolve_command_name [OS α]
    (s0 : os_state α) (prog : String) : os_state α × Option String :=
  resolve_command_name_in_path s0 (get_path s0) prog

/-- Checks whether it's okay to call execve.
    If not, emit an appropriate error message and set the ec.
    Lem: val check_execve : forall 'a. OS 'a =>
                   maybe string -> (* prefix for error messages *)
                   os_state 'a ->
                   string ->
                   os_state 'a * maybe string (* nothing means failure *) -/
def check_execve [OS α]
    (mpfx : Option String) (s0 : os_state α) (prog : String) :
    os_state α × Option String :=
  let prefixs :=
    match mpfx with
    | none      => ""
    | some pfx  => pfx ++ ": "
  let (s1, m_path) := resolve_command_name s0 prog
  match m_path with
  | none =>
    let s2 := write_stderr (prefixs ++ prog ++ ": command not found\n") s1
    (exit_with 127 s2, none)
  | some executable =>
    if file_exists s1 executable then
      if is_executable s1 executable then
        (s1, some executable)
      else
        let s2 := write_stderr (prefixs ++ executable ++ ": command not executable\n") s1
        (exit_with 126 s2, none)
    else
      let s2 := write_stderr (prefixs ++ executable ++ ": command not found\n") s1
      (exit_with 127 s2, none)

/-- Lem: early_hash : forall 'a. OS 'a => os_state 'a -> stmt -> os_state 'a -/
def early_hash [OS α] (s0 : os_state α) (c : stmt) : os_state α :=
  let cmds := Set.Set.toList (collect_command_names c)
  let pathEnv := get_path s0
  List.foldr
    (fun cmd os => (resolve_command_name_in_path os pathEnv cmd).1)
    s0
    cmds


-- ARGUMENT PROCESSING

/-- Lem: strip_double_dash : fields -> fields -/
def strip_double_dash : fields → fields
  | ([(.C '-') , (.C '-')] :: argv') => argv'
  | argv => argv

/-- Lem: getopt : list char -> fields -> maybe (maybe char * fields) -/
def getopt (opts : List Char) : fields → Option (Option Char × fields)
  | [] => none
  | arg :: fields' =>
    match try_concrete arg with
    | none => none
    | some s =>
      match toCharList s with
      | '-' :: '-' :: [] => some (none, fields')
      | '-' :: c :: cs =>
        if List.elem c opts then
          -- try to support -LP constructions
          let argrest : fields :=
            match cs with
            | [] => fields'
            | _  => ((.C '-') :: (List.map .C cs)) :: fields'
          some (some c, argrest)
        else
          none
      | _ => none

/-
def getopts (opts : List Char) : fields → List Char × fields
  | fields =>
      match getopt opts fields with
      | none => ([], fields)
      | some (none, fields') =>
          -- stop! we hit -- or some such
          ([], fields')
      | some (some opt, fields') =>
          let (found_opts, fields'') := getopts opts fields'
          -- store in reverse order so we can process without accumulator
          (found_opts ++ [opt], fields'')
-/
/-- Lem: getopts : list char -> fields -> list char * fields -/
def getopts (opts : List Char) (argv : fields) : List Char × fields :=
  let rec go (pending : List Char) (fieldss : fields) : List Char × fields :=
    match pending with
    | [] =>
      match fieldss with
      | [] => ([], [])
      | arg :: fields' =>
        match try_concrete arg with
        | none => ([], arg :: fields')
        | some s =>
          match toCharList s with
          | '-' :: '-' :: [] => ([], fields')
          | '-' :: c :: cs =>
            if List.elem c opts then
              let (found, rest) := go cs fields'
              (found ++ [c], rest)
            else
              ([], arg :: fields')
          | _ =>
              ([], arg :: fields')
    | c :: cs =>
        if List.elem c opts then
          let (found, rest) := go cs fieldss
          (found ++ [c], rest)
        else
          let leftover : symbolic_string := (.C '-') :: (List.map .C (c :: cs))
          ([], leftover :: fieldss)
  go [] argv


-- PID RESOLUTION


/-- Lem: current_job -/
def current_job (s0 : os_state α) (msg : String) : Except String job_info :=
  match s0.sh.jobs with
  | []       => .error (msg ++ ": no such job")
  | job ::_  => .ok job

/-- Lem: prev_job -/
def prev_job (s0 : os_state α) : Except String job_info :=
  match s0.sh.jobs with
  | []            => .error "%-: no such job"
  | [job]         => .ok job        -- pretend circular buffer
  | _ :: job :: _ => .ok job

/-- Lem: find_job -/
def find_job (s0 : os_state α) (pred : job_info → Bool) (msg : String) : Except String job_info :=
  match List.filter pred s0.sh.jobs with
  | []      => .error (msg ++ ": no such job")
  | [job]   => .ok job             -- should only be one
  | _       => .error ("ambiguous job spec " ++ msg)

/-- Lem: job_cmd_cs -/
def job_cmd_cs (jb : job_info) : List Char :=
  toCharList (string_of_stmt jb.cmd)

/-- Lem: job_of_symbolic_string -/
def job_of_symbolic_string (s0 : os_state α) (ss : symbolic_string) : Except String job_info :=
  match try_concrete ss with
  | none =>
    .error ("couldn't translate symbolic string '" ++ string_of_symbolic_string ss ++ "'")
  | some s =>
    match toCharList s with
    | '%' :: fmt =>
      match fmt with
      | ['%'] => current_job s0 "%%"
      | ['+'] => current_job s0 "%+"
      | ['-'] => prev_job s0
      | '?' :: cs =>
        find_job s0
          (fun jb => isInfixOf cs (job_cmd_cs jb))
          ("%?" ++ toString cs)
      | _ =>
        match Num.readNat fmt with
        | .ok num =>
          find_job s0
            (fun jb => jb.id = num)
            ("%" ++ stringFromNat num)
        | .error _ =>
          find_job s0
            (fun jb => isPrefixOf fmt (job_cmd_cs jb))
            ("%" ++ toString fmt)
    | _ =>
      .error (s ++ ": no such job")

/-- Lem: pid_of_symbolic_string -/
def pid_of_symbolic_string
    (s0 : os_state α) (ss : symbolic_string) : Except String (Nat × signal_mode) :=
  match try_concrete ss with
  | none =>
    .error ("couldn't translate symbolic string '" ++ string_of_symbolic_string ss ++ "'")
  | some s =>
    match toCharList s with
    | '%' :: _ =>
      if is_monitoring s0 then
        match job_of_symbolic_string s0 ss with
        | .ok jb   => .ok (jb.pid, .SignalProcessGroup)  -- per dash
        | .error e => .error e
      else
        .error ("no such process " ++ s)
    | cs =>
      let (cs', mode) :=
      match cs with
      | '-' :: cs' => (cs', .SignalProcessGroup)
      | _          => (cs,  .SignalProcess)
      match Num.readNat cs' with
      | .error _    => .error ("Illegal number: " ++ s)
      | .ok pid  => .ok (pid, mode)








-- SPECIAL BUILTINS
/-
  NB special builtins should NEVER use Right combined with a non-zero
  EC to signal an error; in order to comply with early exit rules in
  the table in 2.8.1
-/

-- Either (os_state α × String) (os_state α × stmt × Bool)
abbrev builtin_ret (α : Type u) :=
  Except (os_state α × String) (os_state α × stmt × Bool)

/-- Lem: builtin_colon -/
def builtin_colon [OS α]
    (s0 : os_state α) (_argv : fields) (_env : env) : builtin_ret α :=
  .ok (exit_with 0 s0, .Done, true)

/-- Lem: builtin_break -/
def builtin_break [OS α]
    (s0 : os_state α) (argv : fields) (_env : env) : builtin_ret α :=
    /-
     "If n is greater than the number of enclosing loops, the
     outermost enclosing loop shall be exited. If there is no
     enclosing loop, the behavior is unspecified."
    -/
  let try_break (wanted_n : Nat) : builtin_ret α :=
    let n :=
      if wanted_n <= s0.sh.loop_nest || Set.Set.member .Sh_nonlexicalctrl s0.sh.opts then
        wanted_n
      else
        s0.sh.loop_nest
    if n <= 0 then
      let s_n := stringFromNat wanted_n
      let s1 := log_trace .Trace_unspec ("break " ++ s_n ++ " outside of loop") s0
      -- printing here or returning non-0 breaks the POSIX test suite
      .ok (exit_with 0 s1, .Done, true)
    else
      .ok (exit_with 0 s0, .Break n, true)
  match strip_double_dash argv with
  | [] =>
    -- default to just breaking the immediate loop
    try_break 1
  | [s] =>
    match Num.readUnsignedInteger 10 (Num.trim (char_list_of_symbolic_string s)) with
    | .ok n => try_break (n.toNat)
    | .error _  =>
      .error (s0, string_of_symbolic_string s ++ ": positive argument required")
  | _ =>
    .error (s0, "too many arguments")

/-- Lem: builtin_continue -/
def builtin_continue [OS α]
    (s0 : os_state α) (argv : fields) (_env : env) : builtin_ret α :=
  let try_continue (wanted_n : Nat) : builtin_ret α :=
    let n :=
      if wanted_n <= s0.sh.loop_nest || Set.Set.member .Sh_nonlexicalctrl s0.sh.opts then
        wanted_n
      else
        s0.sh.loop_nest
    if n <= 0 then
      let s_n := stringFromNat wanted_n
      let s1 := log_trace .Trace_unspec ("continue " ++ s_n ++ " outside of loop") s0
      -- printing here or returning non-0 breaks the POSIX test suite
      .ok (exit_with 0 s1, .Done, true)
    else
      .ok (exit_with 0 s0, .Continue n, true)
  match strip_double_dash argv with
  | [] =>
    -- default to just continuing the immediate loop
    try_continue 1
  | [s] =>
    match Num.readUnsignedInteger 10 (Num.trim (char_list_of_symbolic_string s)) with
    | .ok n => try_continue (n.toNat)
    | .error _  =>
      .error (s0, string_of_symbolic_string s ++ ": positive numeric argument required")
  | _ =>
      .error (s0, "too many arguments")

/-- Lem: builtin_exit -/
def builtin_exit [OS α]
    (s0 : os_state α) (argv : fields) (_env : env) : builtin_ret α :=
  match strip_double_dash argv with
  | [] => .ok (s0, .Exit, true)  -- default to exit code of last command
  | [s] =>
    match Num.readUnsignedInteger 10 (Num.trim (char_list_of_symbolic_string s)) with
    | .ok n =>
      if n < (Int.ofNat 0) || n > (Int.ofNat 255) then
        .error (s0, Num.Read.write n ++ ": illegal number")
      else
        .ok (exit_with (n.toNat) s0, .Exit, true)
    | .error _ =>
      .error (s0, string_of_symbolic_string s ++ ": numeric argument required")
  | _ =>
    .error (s0, "too many arguments")

/-- Lem: builtin_return -/
def builtin_return [OS α]
    (s0 : os_state α) (argv : fields) (_env : env) : builtin_ret α :=
  -- unspecified; current arrangement yields ec=1 on error; bash 255; dash 2
  match strip_double_dash argv with
  | [] =>
    .ok (s0, .Return, true) -- keep last command's return status
  | [s] =>
    match Num.readNat (char_list_of_symbolic_string s) with
    | .ok n => .ok (exit_with n s0, .Return, true)
    | .error _  => .error (s0, string_of_symbolic_string s ++ ": numeric argument required")
  | _ =>
    .error (s0, "too many arguments")

/-- Lem: builtin_shift -/
def builtin_shift [OS α]
    (s0 : os_state α) (argv : fields) (_env : env) : builtin_ret α :=
  let nRes : Except String Nat :=
    match strip_double_dash argv with
    | [] => .ok 1
    | [s] =>
      match Num.readNat (char_list_of_symbolic_string s) with
      | .ok n => .ok n
      | .error _  => .error (string_of_symbolic_string s ++ ": numeric argument required")
    | _ =>
      .error "too many arguments"
  match nRes with
  | .error err => .error (s0, err)
  | .ok n =>
    let params := get_function_params s0
    if n > params.length then
      .error (s0, "can't shift that many")
    else
      let s1 := set_function_params s0.sh.loop_nest (params.drop n) s0
      .ok (exit_with 0 s1, .Done, true)

/-- Lem: val unset_var :
  forall 'a. OS 'a => symbolic_string -> os_state 'a -> either string (os_state 'a) -/
def unset_var [OS α]
    (sx : symbolic_string) (s0 : os_state α) : Except String (os_state α) :=
  match try_concrete sx with
  | none =>
    .error ("couldn't unset symbolic variable " ++ string_of_symbolic_string sx)
  | some x =>
    if is_readonly x s0 then
      .error (x ++ " is read-only")
    else if is_special_param x then
      .error (x ++ " is a special parameter and cannot be unset")
    else
      .ok (unset_param x s0)

/-- Lem: val unset_fun :
  forall 'a. OS 'a => symbolic_string -> (os_state 'a) -> either string (os_state 'a) -/
def unset_fun [OS α]
    (sx : symbolic_string) (s0 : os_state α) : Except String (os_state α) :=
  match try_concrete sx with
  | none =>
    .error ("couldn't unset symbolic function " ++ string_of_symbolic_string sx)
  | some x =>
    .ok { s0 with sh := { s0.sh with funcs := Map.delete x s0.sh.funcs } }

/-- Lem: unset_mode -/
def unset_mode [OS α]
    : List Char → (symbolic_string → os_state α → Except String (os_state α))
  | []        => unset_var
  | 'f' :: _  => unset_fun
  | 'v' :: _  => unset_var
  | _ :: opts => unset_mode opts

/-- Lem: val unset_all : forall 'a. OS 'a =>
  (symbolic_string -> os_state 'a -> either string (os_state 'a)) ->
  list symbolic_string ->
  os_state 'a ->
  either (os_state 'a * string) (os_state 'a * stmt * bool) -/
def unset_all [OS α]
    (unsetter : symbolic_string → os_state α → Except String (os_state α)) :
    List symbolic_string → os_state α → builtin_ret α
  | [], s0 => .ok (exit_with 0 s0, .Done, true)
  | name :: names', s0 =>
    match unsetter name s0 with
    | .error err => .error (s0, err)
    | .ok s1 => unset_all unsetter names' s1

/-- Lem: builtin_unset -/
def builtin_unset [OS α]
    (s0 : os_state α) (argv : fields) (_env : env) : builtin_ret α :=
  /-
   unspec whether to unset a function if no flag is given and no such var.
   dash doesn't do it; neither will we. *)
  -/
  let (opts, argv') := getopts ['f', 'v'] argv
  let unsetter := unset_mode (α := α) opts
  unset_all unsetter argv' s0

/-- Lem: show_varlist -/
def show_varlist [OS α]
    (s0 : os_state α) (cmd : String) : List String → Except String (os_state α)
  | [] => .ok s0
  | v :: vs' =>
    match lookup_param s0 v with
    | .error e => .error e
    | .ok mss =>
      let suffix :=
        match mss with
        | some ss => "=" ++ quote (string_of_fields ss)
        | none    => ""
      let msg := cmd ++ " " ++ v ++ suffix ++ "\n"
      let s1 := safe_write_stdout "cmd" msg s0
      show_varlist s1 cmd vs'

/-- Lem: val update_varlist : forall 'a. OS 'a =>
  os_state 'a -> string -> (os_state 'a -> string -> os_state 'a) ->
  list symbolic_string ->
  either (os_state 'a * string) (os_state 'a * stmt * bool) -/
def update_varlist [OS α]
    (s0 : os_state α)
    (cmd : String)
    (update : os_state α → String → os_state α) :
    List symbolic_string → builtin_ret α
  | [] => .ok (s0, .Done, true)
  | arg :: args' =>
    let (var, mvalue) := try_split_assign arg
    match mvalue with
    | none =>
      update_varlist (update s0 var) cmd update args'
    | some value =>
      match set_param var value s0 with
      | .error msg  => .error (s0, msg)
      | .ok s1  => update_varlist (update s1 var) cmd update args'

/-- Lem: log_null_argv_unspec -/
def log_null_argv_unspec [OS α]
    (s0 : os_state α) (name : String) (argv : fields) : os_state α :=
  if List.isEmpty argv then
    log_trace .Trace_unspec (name ++ " invoked with no arguments; pretending we got -p") s0
  else
    s0

/-- Lem: builtin_export -/
def builtin_export [OS α]
    (s0 : os_state α) (argv : fields) (_env : env) : builtin_ret α :=
  let s1 := exit_with 0 s0
  let (opts, argv') := getopts ['p'] argv
  if List.elem 'p' opts || List.isEmpty argv' then
    let s2 := log_null_argv_unspec s1 "export" argv
    match exported_vars s2 with
    | .error e => .error (s2, "export: " ++ e)
    | .ok m =>
      let vars := Set.Set.toOrderedList (Map.domain m)
      match show_varlist s2 "export" vars with
      | .ok s3    => .ok (s3, .Done, true)
      | .error e  => .error (s2, "export: " ++ e)
  else
    update_varlist s1 "export" set_exported argv'

/-- Lem: builtin_readonly -/
def builtin_readonly [OS α]
    (s0 : os_state α) (argv : fields) (_env : env) : builtin_ret α :=
  let s1 := exit_with 0 s0
  let (opts, argv') := getopts ['p'] argv
  if List.elem 'p' opts || List.isEmpty argv' then
    let s2 := log_null_argv_unspec s1 "readonly" argv
    match readonly_vars s2 with
    | .error e => .error (s2, "readonly: " ++ e)
    | .ok m =>
      let vars := Set.Set.toOrderedList (Map.domain m)
      match show_varlist s2 "readonly" vars with
      | .ok s3   => .ok (s3, .Done, true)
      | .error e => .error (s2, "readonly: " ++ e)
  else
    update_varlist s1 "readonly" set_readonly argv'

/-- Lem: add_locals -/
def add_locals [OS α]
    (os : os_state α) (lenv : local_env) : List symbolic_string → Except String local_env
  | [] => .ok lenv
  | arg :: args' =>
    let (var, mvalue) := try_split_assign arg
    if is_readonly var os then
      .error (var ++ ": readonly variable")
    else
      let opts :=
        if Set.Set.member .Sh_allexport os.sh.opts then
          { local_opts_default with local_exported := true }
        else
          local_opts_default
      let binding :=
        match (mvalue, Map.lookup var lenv) with
        | (none, some (existing, e_opts)) =>
          ( existing, { e_opts with local_exported := e_opts.local_exported || opts.local_exported } )
        | (none, none) =>
          (none, opts)
        | (some value, _) =>
          (some value, opts)
      add_locals os (Map.insert var binding lenv) args'

/-- Lem: builtin_local -/
def builtin_local [OS α]
    (s0 : os_state α) (argv : fields) (_env : env) : builtin_ret α :=
  let s1 :=
    log_trace .Trace_unspec "local is unspecified; treated here as a special-builtin"
      (exit_with 0 s0)
  let (opts, argv') := getopts ['p'] argv
  if List.elem 'p' opts || List.isEmpty argv' then
    let vars := get_locals s1
    match show_varlist s1 "local" vars with
    | .ok s2   => .ok (s2, .Done, true)
    | .error e => .error (s1, "local: " ++ e)
  else
    match s1.sh.locals with
    | [] =>
      .error (s1, "not in a function")
    | lenv :: locals' =>
      match add_locals s1 lenv argv' with
      | .error err => .error (s1, err)
      | .ok env' => .ok ({ s1 with sh := { s1.sh with locals := env' :: locals' } }, .Done, true)

/-- Lem: builtin_times -/
def builtin_times [OS α]
    (s0 : os_state α) (_argv : fields) (_env : env) : builtin_ret α :=
  let s1 := exit_with 0 s0
  let (utime, stime, cutime, cstime) := times s1
  .ok ( safe_write_stdout "times"
        (utime ++ " " ++ stime ++ "\n" ++ cutime ++ " " ++ cstime ++ "\n") s1
    , .Done
    , true )

/-- Lem: builtin_eval -/
def builtin_eval [OS α]
    (s0 : os_state α) (argv : fields) (_env : env) : builtin_ret α :=
  if List.isEmpty argv then
    .ok (exit_with 0 s0, .Done, true)
  else
    let argv' := strip_double_dash argv
    let src := .ParseString .ParseEval (string_of_fields argv')
    let sstr := parse_init src
    .ok ( s0
      , .EvalLoop 1 (.Mk sstr (some (stack_init ()))) src .Noninteractive .Subsidiary
      , true )

/-- Lem: builtin_source -/
def builtin_source [OS α]
    (argv0 : String) (s0 : os_state α) (argv : fields) (_env : env) : builtin_ret α :=
  match strip_double_dash argv with
  | [] => .error (s0, "usage: " ++ argv0 ++ " filename")
  | sfile :: _ =>
    match try_concrete sfile with
    | none => .error (s0, "couldn't handle symbolic argument " ++ string_of_symbolic_string sfile)
    | some file =>
      let mpath : Except String String :=
        if List.elem '/' (toCharList file) && file_exists s0 file then
          if is_readable s0 file then
            .ok file
          else
            .error "unreadable"
        else
          match lookup_concrete_param s0 "PATH" with
          | .ok none => .error "no PATH"
          | .ok (some pathvar) =>
            let paths := split_string_on true ':' pathvar
            match resolve_path_with (is_readable s0) paths file with
            | none      => .error "not found"
            | some path => .ok path
          | .error msg => .error msg
      match mpath with
      | .error msg =>
        /-
         If no readable file is found, a non-interactive shell
         shall abort; an interactive shell shall write a
         diagnostic message to standard error, but this condition
         shall not be considered a syntax error.
        -/
        .error (s0, file ++ ": " ++ msg)
      | .ok path =>
        let src := .ParseFile path .PushFile
        let sstr := parse_init src
        .ok (s0, .EvalLoop 1 (.Mk sstr none) src .Noninteractive .Subsidiary, true)

/-- Lem: builtin_exec -/
def builtin_exec [OS α]
    (s0 : os_state α) (argv : fields) (env : env) : builtin_ret α :=
  match strip_double_dash argv with
  | [] =>
    /-
     one might worry that this ec will override whatever the
     redirects brought. but there's no way we'd even run the
     command if the redirs failed!

     we'll exit in a noninteractive shell, or just fail
     interactively or with command exec
    -/
    .ok (exit_with 0 s0, .Done, false)   -- don't restore
  | scmd :: args =>
    match try_concrete scmd with
    | none => .error (s0, "couldn't handle symbolic argument " ++ string_of_symbolic_string scmd)
    | some cmd =>
      match check_execve (some "exec") s0 cmd with
      | (s1, none) => .ok (s1, .Done, true)
      | (s1, some executable) =>
        match exported_set_vars s1 with
        | .error e => .error (s1, "exec: " ++ e)
        | .ok exported =>
          let exec_env := Map.union exported env
          -- use env to override exports---impl as Pmap.(union)
          .ok (s1
            , .Exec (symbolic_string_of_string executable) scmd args exec_env .NoBinSh
            , false)

/-- Lem: set_getopt_longopt -/
def set_getopt_longopt (fs : fields) : Option (sh_opt × fields) :=
  match fs with
  | [] => none   -- handled raw "set -o" already
  | name :: fs' =>
    match try_concrete name with
    | none => none
    | some longopt =>
      match sh_opt_of_longopt longopt with
      | none     => none
      | some opt => some (opt, fs')

/-- Lem: set_getopt_shortopt -/
def set_getopt_shortopt (c : Char) (cs : List Char) (fs : fields) : Option (sh_opt × fields) :=
  match sh_opt_of_shortopt c with
  | none => none
  | some opt =>
    -- support multiple args, as in -xv
    let argrest : fields :=
      match cs with
      | [] => fs
      | _  => ((.C '-') :: (List.map .C cs)) :: fs
    some (opt, argrest)

/-- Lem: val set_add_opt :
  list sh_opt * list sh_opt -> bool ->
  maybe (sh_opt * fields) ->
  maybe (maybe (list sh_opt * list sh_opt) * fields * bool)
-/
def set_add_opt
    (opts : List sh_opt × List sh_opt)
    (add_to_on : Bool)
    (res : Option (sh_opt × fields)) :
    Option (Option (List sh_opt × List sh_opt) × fields × Bool) :=
  let (on, off) := opts
  match res with
  | none => none
  | some (opt, fs) =>
    let opts' : (List sh_opt × List sh_opt) :=
      if add_to_on then
        (opt :: on, off.erase opt)
      else
        (on.erase opt, opt :: off)
    some (some opts', fs, false)

/-- Lem: val set_getopt :
  list sh_opt * list sh_opt -> fields ->
  maybe (maybe (list sh_opt * list sh_opt) * fields * bool)
-/
def set_getopt
    (opts : List sh_opt × List sh_opt)
    (fs : fields) :
    Option (Option (List sh_opt × List sh_opt) × fields × Bool) :=
  match fs with
  | [] => some (none, [], false)
  | arg :: fs' =>
    match try_concrete arg with
    | none => none
    | some s =>
      match toCharList s with
      | '-' :: '-' :: [] => some (none, fs', true)
      -- - means turn it ON
      | '-' :: 'o' :: [] => set_add_opt opts true (set_getopt_longopt fs')
      | '-' :: c :: cs => set_add_opt opts true (set_getopt_shortopt c cs fs')
      -- + means turn it OFF
      | '+' :: 'o' :: [] => set_add_opt opts false (set_getopt_longopt fs')
      | '+' :: c :: cs => set_add_opt opts false (set_getopt_shortopt c cs fs')
      | _ => some (none, arg :: fs', true)

/-- Lem: val set_getopts :
  list sh_opt * list sh_opt -> fields ->
  maybe ((list sh_opt * list sh_opt) * fields * bool)
-/
partial def set_getopts
    (opts : List sh_opt × List sh_opt)
    (fs : fields) :
    Option ((List sh_opt × List sh_opt) × fields × Bool) :=
  match set_getopt opts fs with
  | none => none -- bad parse is failure; need explicit -- for args
  | some (none, fs', set_param) =>
      /-
       stop! we hit -- or some such
       set_param will be true if we have (0 or more) params to set
      -/
      some (opts, fs', set_param)
  | some (some opts', fs', _set_param) => set_getopts opts' fs'

/-- Lem： set_showopts -/
def set_showopts [OS α]
    (s0 : os_state α)
    (shows : os_state α → (sh_opt × Bool) → os_state α) :
    builtin_ret α :=
  let opt_vals := List.map (fun opt => (opt, Set.Set.member opt s0.sh.opts)) all_sh_opts
  .ok (List.foldl shows s0 opt_vals, .Done, true)

/-- Lem： val string_of_sh_opt_max_len : nat -/
def string_of_sh_opt_max_len : Nat :=
  maximum (List.map (Function.comp stringLength string_of_sh_opt) all_sh_opts)

/-- Lem： builtin_set
  set [-abCefhmnuvx] [-o option] [argument...]
  set [+abCefhmnuvx] [+o option] [argument...]
  set -- [argument...]
OR
  set -o
OR
  set +o
-/
def builtin_set [OS α]
    (s0 : os_state α) (argv : fields) (_env : env) : builtin_ret α :=
  let s1 := exit_with 0 s0
  match argv with
  | [] =>
    -- dump env
    .ok (safe_write_stdout "set" (printable_shell_env s1) s1, .Done, true)
  | [[.C '-']] =>
    /-
     OVERFIT
     See Assertion 105 in section 3.14.11 of standard P1003.3.2/D8.
     Technically, this behavior is unspecified... but this is what
     the testers want, I guess?
    -/
    .ok (unset_sh_opt (unset_sh_opt s1 .Sh_xtrace) .Sh_verbose, .Done, true)
  | [[.C '-', .C 'o']] =>
    -- print human readable; following dash
    set_showopts s1 (fun os (opt, is_set) =>
      let msg := pad_right (string_of_sh_opt opt) string_of_sh_opt_max_len ++
        "\t" ++ (if is_set then "on" else "off")
      safe_write_stdout "set" (msg ++ "\n") os)
  | [[.C '+', .C 'o']] =>
    -- print shell readable
    set_showopts s1 (fun os (opt, is_set) =>
      match char_of_sh_opt opt with
      | none => os
      | some c =>
        let switch : Char := if is_set then '-' else '+'
        let flag := toString [switch, c]
        let msg := "set " ++ flag
        safe_write_stdout "set" (msg ++ "\n") os)
  | _ =>
    match set_getopts ([], []) argv with
    | none =>
      /-
       While an erroneous condition, we don't want to actually
       exit when set is given a bad option. The standard doesn't
       say that it's an error, it does say we'll set the
       ec. Weird.
      -/
      .ok (fail_with "set: illegal option" s1, .Done, true)
    | some ((on, off), params, set_param) =>
      let s2 := List.foldr (fun opt os => set_sh_opt os opt) s1 on
      let s3 := List.foldr (fun opt os => unset_sh_opt os opt) s2 off
      let s4 :=
        if set_param then
          set_function_params s3.sh.loop_nest params s3
        else
          s3
      .ok (s4, .Done, true)

abbrev platform_int := Int
opaque signal_of_platform_int : platform_int → Option signal
opaque platform_int_of_signal : signal → platform_int

/-- Lem: trap_parse_signal -/
def trap_parse_signal (arg : symbolic_string) : Except String signal :=
  match try_concrete arg with
  | none => .error ("couldn't recognize symbolic signal " ++ string_of_symbolic_string arg)
  | some sig_name =>
    match Num.readNat (toCharList sig_name) with
    | .ok num =>
      match signal_of_platform_int num with
      | none => .error ("couldn't recognize signal number " ++ sig_name)
      | some sig => .ok sig
    | .error _ =>
      match signal_of_string sig_name with
      | none => .error ("couldn't recognize signal " ++ sig_name)
      | some sig => .ok sig

/-- Lem: trap_parse_signals -/
def trap_parse_signals (argv : fields) : Except String (List signal) :=
  match argv with
  | [] => .ok []
  | arg :: argv' =>
    match trap_parse_signal arg with
    | .error err => .error err
    | .ok sig =>
      match trap_parse_signals argv' with
      | .error err => .error err
      | .ok rest => .ok (sig :: rest)

/-- Lem: trap_handle_signal -/
def trap_handle_signal [OS α]
    (s0 : os_state α) (cond : signal) (handler : Option symbolic_string) : os_state α :=
  if List.elem cond undefined_traps then
    log_trace .Trace_undef
      "Setting a trap for SIGKILL or SIGSTOP produces undefined results."
      s0
  else
    let s1 := update_trap s0 cond handler
    handle_signal s1 cond handler

/-- Lem: builtin_trap -/
def builtin_trap [OS α]
    (s0 : os_state α) (argv : fields) (_env : env) : builtin_ret α :=
  let s1 :=
    if List.isEmpty argv then
      exit_with 0 s0
    else
      clear_supershell_traps (exit_with 0 s0)
  match strip_double_dash argv with
  | [] =>
    let shows (tr : signal × symbolic_string) (os : os_state α) :=
      let (trapSig, cmd) := tr
      let quoted_cmd := "'" ++ string_of_symbolic_string cmd ++ "'"
      let msg := "trap -- " ++ quoted_cmd ++ " " ++ string_of_signal trapSig
      safe_write_stdout "trap" (msg ++ "\n") os
    let traps :=
      match s1.sh.supershell_traps with
      | none => s1.sh.traps
      | some super_traps => super_traps
    let s2 := List.foldr (fun tr os => shows tr os) s1 (Map.toList traps)
    .ok (s2, .Done, true)
  | arg :: signals =>
    match Num.readNat (char_list_of_symbolic_string arg) with
    | .ok _n =>
      -- unset n and all other conditions
      match trap_parse_signals (arg :: signals) with
      | .error err =>
        .ok (fail_with ("trap: " ++ err) s1, .Done, true)
      | .ok conds =>
        let s2 := List.foldr (fun cond os => trap_handle_signal os cond none) s1 conds
        .ok (exit_with 0 s2, .Done, true)
    | .error _ =>
      match (try_concrete arg, trap_parse_signals signals) with
      | (none, _) =>
        .error (s1, "couldn't set symbolic trap: " ++ string_of_symbolic_string arg)
      | (_, .error err) =>
        .ok (fail_with ("trap: " ++ err) s1, .Done, true)
      | (some "-", .ok conds) =>
        let s2 := List.foldr (fun cond os => trap_handle_signal os cond none) s1 conds
        .ok (exit_with 0 s2, .Done, true)
      | (some _, .ok conds) =>
        let s2 := List.foldr (fun cond os => trap_handle_signal os cond (some arg)) s1 conds
        .ok (exit_with 0 s2, .Done, true)

/-- Lem: special_builtins -/
def special_builtins [OS α] :
    Map.map String (os_state α → fields → env → builtin_ret α) :=
  Map.fromList
    [ (".",       builtin_source ".")
    , (":",       builtin_colon)
    , ("break",   builtin_break)
    , ("continue",builtin_continue)
    , ("eval",    builtin_eval)
    , ("exec",    builtin_exec)
    , ("exit",    builtin_exit)
    , ("export",  builtin_export)
    , ("local",   builtin_local)   -- cheating!
    , ("readonly",builtin_readonly)
    , ("return",  builtin_return)
    , ("shift",   builtin_shift)
    , ("source",  builtin_source "source")
    , ("set",     builtin_set)
    , ("times",   builtin_times)
    , ("trap",    builtin_trap)
    , ("unset",   builtin_unset)
    ]




-- ORDINARY BUILTINS
/-- Lem: either (os_state * string) (os_state * stmt) -/
abbrev builtin_ret_stmt (α : Type u) :=
  Except (os_state α × String) (os_state α × stmt)

/-- Lem: builtin_true -/
def builtin_true [OS α]
    (s0 : os_state α) (_argv : fields) (_env : env) : builtin_ret_stmt α :=
  .ok (exit_with 0 s0, .Done)

/-- Lem: builtin_false -/
def builtin_false [OS α]
    (s0 : os_state α) (_argv : fields) (_env : env) : builtin_ret_stmt α :=
  .ok (exit_with 1 s0, .Done)

/-- Lem: path_mode type -/
inductive path_mode where
  | Link
  | Physical
deriving DecidableEq, Repr

/-- Lem: path_mode : list char -> path_mode -/
def path_mode_of_opts : List Char → path_mode
  | []        => .Link
  | 'P' :: _  => .Physical
  | 'L' :: _  => .Link
  | _   :: os => path_mode_of_opts os

/-- Lem: val resolve_path_mode : forall 'a. OS 'a => os_state 'a -> path_mode -> os_state 'a * string -/
def resolve_path_mode [OS α]
    (s0 : os_state α) (mode : path_mode) : os_state α × String :=
  let (s1, pwd) :=
    match mode with
    | .Link     => (s0, s0.sh.cwd)
    | .Physical =>
      let pwd := physical_cwd s0
      let s1  := { s0 with sh := { s0.sh with cwd := pwd } }
      (s1, pwd)
  let s2 := internal_set_param "PWD" (symbolic_string_of_string pwd) s1
  (s2, pwd)

/-- Lem: builtin_pwd -/
def builtin_pwd [OS α]
    (s0 : os_state α) (argv : fields) (_env : env) : builtin_ret_stmt α :=
  let (opts, _argv') := getopts ['L', 'P'] argv
  let mode := path_mode_of_opts opts
  let (s1, pwd) := resolve_path_mode (exit_with 0 s0) mode
  .ok (safe_write_stdout "pwd" (pwd ++ "\n") s1, .Done)

/-- Lem: write_many_stdout -/
def write_many_stdout [OS α]
    (f : fields) (s0 : os_state α) : os_state α :=
  let (s1, _ignored, s) := concretize_fields s0 f
  safe_write_stdout "echo" s s1

/-- Lem: builtin_echo -/
def builtin_echo [OS α]
    (s0 : os_state α) (argv : fields) (_env : env) : builtin_ret_stmt α :=
  -- TODO backslash escapes
  let (terminator, ss) :=
    match argv with
    | [.C '-', .C 'n'] :: argv' => ("",  argv')
    | _                         => ("\n", argv)
  let s1 := write_many_stdout ss (exit_with 0 s0)
  let s2 := safe_write_stdout "echo" terminator s1
  .ok (s2, .Done)

/-- Lem: do_cd -/
def do_cd [OS α]
    (s0 : os_state α) (mode : path_mode) (dir : String) : builtin_ret_stmt α :=
  let (curpath, need_print) :=
    if first_is_slash dir then
      /-
       3. If the directory operand begins with a <slash> character,
       set curpath to the operand and proceed to step 7. *)
      -/
      (dir, false)
    else if dir = "." || dir = ".." ||
            toString (List.take 2 (toCharList dir)) = "./" ||
            toString (List.take 3 (toCharList dir)) = "../"
    then
      /-
       4. If the first component of the directory operand is dot or
       dot-dot, proceed to step 6.
       6. Set curpath to the directory operand.
       onward!
      -/
      (dir, false)
    else

        -- 5. Starting with the first pathname in the <colon>-separated
        -- pathnames of CDPATH (see the ENVIRONMENT VARIABLES section) if
        -- the pathname is non-null, test if the concatenation of that
        -- pathname, a <slash> character if that pathname did not end with a
        -- <slash> character, and the directory operand names a
        -- directory. If the pathname is null, test if the concatenation of
        -- dot, a <slash> character, and the operand names a directory. In
        -- either case, if the resulting string names an existing directory,
        -- set curpath to that string and proceed to step 7. Otherwise,
        -- repeat this step with the next pathname in CDPATH until all
        -- pathnames have been tested.

      match lookup_concrete_param s0 "CDPATH" with
      | .error _ => (dir, false)
      | .ok none => (dir, false)
      | .ok (some cdpath) =>
        let cdpaths := split_string_on true ':' cdpath
        match resolve_path_with (is_dir s0) cdpaths dir with
        | none      => (dir, false)
        | some dir' => (dir', true)
  /-
   7. If the -P option is in effect, proceed to step 10. If
    curpath does not begin with a <slash> character, set curpath to
    the string formed by the concatenation of the value of PWD, a
    <slash> character if the value of PWD did not end with a
    <slash> character, and curpath. *)
  -/

  let curpath' : Option String :=
    match mode with
    | .Physical => some curpath
    | .Link =>
      let curpath'' :=
        if first_is_slash curpath
        then curpath
        else join_path s0.sh.cwd curpath
      canonicalize_path s0 curpath''
  match curpath' with
  | none => .error (s0, "illegal path " ++ curpath)
  | some curpath'' =>
    let old := s0.sh.cwd
    let (s1, res) := chdir s0 curpath''
    match res with
    | none =>
      let (s2, pwd) := resolve_path_mode s1 mode   -- sets PWD
      let s3 := internal_set_param "OLDPWD" (symbolic_string_of_string old) s2
      let s4 :=
        if need_print
        then safe_write_stdout "cd" (pwd ++ "\n") s3
        else s3
      .ok (exit_with 0 s4, .Done)
    | some err => .error (s1, err)

/-- Lem: builtin_cd -/
def builtin_cd [OS α]
    (s0 : os_state α) (argv : fields) (_env : env) : builtin_ret_stmt α :=
  let (opts, argv') := getopts ['L', 'P'] argv
  let mode := path_mode_of_opts opts
  match argv' with
  | [] =>
    match lookup_concrete_param s0 "HOME" with
    | .error _ => .error (s0, "HOME unset")
    | .ok none =>
      /-
        1. If no directory operand is given and the HOME environment
        variable is empty or undefined, the default behavior is
        implementation-defined and no further steps shall be
        taken.
      -/
      .error (s0, "HOME unset")
    | .ok (some homedir) =>
      /-
        2. If no directory operand is given and the HOME environment
        variable is set to a non-empty value, the cd utility shall
        behave as if the directory named in the HOME environment
        variable was specified as the directory operand. *)
      -/
      do_cd s0 mode homedir
  | (.C '-' :: []) :: _ =>
    match lookup_concrete_param s0 "OLDPWD" with
    | .error _ => .error (s0, "can't move back to missing OLDPWD")
    | .ok none => .error (s0, "can't move back to missing OLDPWD")
    | .ok (some path) =>
      match do_cd s0 mode path with
      | .error (s1, msg) => .error (s1, msg)
      | .ok (s1, _stmt) => .ok (safe_write_stdout "cd" (path ++ "\n") s1, .Done)
  | path :: _ =>
    match try_concrete path with
    | none => .error (s0, "can't cd to symbolic path")
    | some path => do_cd s0 mode path

/-
   Once a utility has been searched for and found (either as a result
   of this specific search or as part of an unspecified shell start-up
   activity), an implementation may remember its location and need not
   search for the utility again unless the PATH variable has been the
   subject of an assignment. If the remembered location fails for a
   subsequent invocation, the shell shall repeat the search to find
   the new location for the utility, if any.
-/
/-- Lem: builtin_hash -/
def builtin_hash {α : Type u} [OS α]
    (s0 : os_state α) (argv : fields) (_env : env) : builtin_ret_stmt α :=
  let s1 := exit_with 0 s0
  match argv with
  | [] =>
    let msg :=
      if Map.null s1.sh.hashes then
        "No commands hashed."
      else
        let shows : (String × (String × Nat)) → String
            | (_cmd, (path, hits)) => pad_left (stringFromNat hits) 4 ++ "\t" ++ path
        let header := "hits\tcommand\n"
        header ++ String.intercalate "\n" (List.map shows (Map.toList s1.sh.hashes))
    .ok (safe_write_stdout "hash" (msg ++ "\n") s1, .Done)
  | [.C '-', .C 'r'] :: _ => .ok (clear_hash s1, .Done)
  | _ => .ok (s1, .Done)

/-- Lem: command_type type -/
inductive command_type where
  | CmdSymbolic
  | CmdSpecial
  | CmdBuiltin
  | CmdFunction
  | CmdAlias (s : String)
  | CmdPath  (p : String)
  | CmdKeyword
  | CmdNotFound
deriving DecidableEq, Repr

/-- Lem: val shell_keywords : list string -/
def shell_keywords : List String :=
  ["!", "{", "}", "case", "do", "done", "elif", "else",
   "esac", "fi", "for", "if", "in", "then", "until", "while"]

/-- Lem: command_type -/
def command_type_of [OS α]
    (s0 : os_state α) (path : path) (cmd : String) : os_state α × command_type :=
  if List.elem cmd shell_keywords then
    (s0, .CmdKeyword)
  else if is_special_builtin cmd then
    (s0, .CmdSpecial)
  else if is_builtin cmd then
    (s0, .CmdBuiltin)
  else
    match Map.lookup cmd s0.sh.aliases with
    | some mapping => (s0, .CmdAlias mapping)
    | none =>
      if Map.map.contains cmd s0.sh.funcs then
        (s0, .CmdFunction)
      else
        let (s1, m_path) := resolve_command_name_in_path s0 path cmd
        let ct :=
          match m_path with
          | some executable =>
            if file_exists s1 executable then .CmdPath executable else .CmdNotFound
          | none => .CmdNotFound
        (s1, ct)

/-- Lem: command_type_symbolic -/
def command_type_symbolic [OS α]
    (s0 : os_state α) (path : path) (scmd : symbolic_string) : os_state α × command_type :=
  match try_concrete scmd with
  | none      => (s0, .CmdSymbolic)
  | some cmd  => command_type_of s0 path cmd

/-- Lem: concise_command_type -/
def concise_command_type (ct : command_type) (s_name : symbolic_string) : String :=
  let name := string_of_symbolic_string s_name
  match ct with
  | .CmdSymbolic  => name ++ "\n"
  | .CmdKeyword   => name ++ "\n"
  | .CmdSpecial   => name ++ "\n"
  | .CmdBuiltin   => name ++ "\n"
  | .CmdFunction  => name ++ "\n"
  | .CmdPath p    => p ++ "\n"
  | .CmdAlias exp => "alias " ++ name ++ "='" ++ exp ++ "'\n"
  | .CmdNotFound  => ""

/-- Lem: human_readable_command_type -/
def human_readable_command_type (ct : command_type) (s_name : symbolic_string) : String :=
  let msg :=
    match ct with
    | .CmdSymbolic  => " is a symbolic command"
    | .CmdKeyword   => " is a shell keyword"
    | .CmdSpecial   => " is a special shell builtin"
    | .CmdBuiltin   => " is a shell builtin"
    | .CmdFunction  => " is a shell function"
    | .CmdPath p    => " is " ++ p
    | .CmdAlias exp => " is an alias for " ++ exp
    | .CmdNotFound  => ": not found"
  string_of_symbolic_string s_name ++ msg ++ "\n"

-- technically part of XSI, but useful
/-- Lem: builtin_type -/
def builtin_type [OS α]
    (s0 : os_state α) (argv : fields) (_env : env) : builtin_ret_stmt α :=
  let s1 := exit_with 0 s0
  match argv with
  | [] => .ok (s1, .Done)
  | cmd :: argv' =>
    let (s2, ct) := command_type_symbolic s1 (get_path s1) cmd
    let msg := human_readable_command_type ct cmd
    let s3 := safe_write_stdout "type" msg s2
    if s3.sh.exit_code = 0 then
      builtin_type s3 argv' _env
    else
      .ok (s3, .Done)

/-- Lem: command_path type -/
inductive command_path where
  | CPAmbient
  | CPDefault
deriving DecidableEq, Repr

/-- Lem: platform_default_path -/
def platform_default_path : String :=
  "/usr/bin:/bin:/usr/sbin:/sbin"

/-- Lem: command_path type -/
def command_path_of [OS α]
    (s0 : os_state α) (cp : command_path) : String :=
  match cp with
  | .CPAmbient => get_path s0
  | .CPDefault => platform_default_path

/-- Lem: command_mode type -/
inductive command_mode where
  | CMRun
  | CMVerbose (human : Bool)   -- -v = false; -V = true
deriving DecidableEq, Repr

/-- Lem: command_mode -/
def command_mode_of_opts (opts : List Char) : command_mode × command_path :=
  let cp := if List.elem 'p' opts then command_path.CPDefault else command_path.CPAmbient
  let cm :=
    if List.elem 'v' opts then
      .CMVerbose false
    else if List.elem 'V' opts then
      .CMVerbose true
    else
      .CMRun
  (cm, cp)

/-- Lem: show_commands -/
def show_commands [OS α]
    (render : command_type → symbolic_string → String)
    (s0 : os_state α) (path : path) (argv : fields) : builtin_ret α :=
  match argv with
  | [] => .ok (s0, .Done, true)
  | name :: argv' =>
      let (s1, ct) := command_type_symbolic s0 path name
      let msg := render ct name
      let s2 := safe_write_stdout "command" msg s1
      let s3 :=
        if ct = .CmdNotFound then exit_with 127 s2 else s2
      show_commands render s3 path argv'

/-- Lem: val builtin_command : forall 'a. OS 'a => os_state 'a -> fields -> env ->
      either (os_state 'a * string) (os_state 'a * stmt) -/
def builtin_command [OS α]
    (s0 : os_state α) (argv : fields) (env : env) : builtin_ret_stmt α :=
  let (opts, argv') := getopts ['p', 'v', 'V'] argv
  let (mode, cp) := command_mode_of_opts opts
  match mode, argv' with
  | .CMRun, [] => .ok (exit_with 0 s0, .Done)
  | .CMRun, cmd :: args =>
      .ok (s0,
        .CommandReady (assigns_of_env env) cmd args []
          { default_cmd_opts with force_simple_command := true })
  | .CMVerbose human_readable, _ =>
    match show_commands
            (if human_readable then human_readable_command_type else concise_command_type)
            (exit_with 0 s0)
            (command_path_of s0 cp)
            argv' with
    | .error e => .error e
    | .ok (s1, st, _rr) => .ok (s1, st)

/-- Lem: umask_fix_flag -/
def umask_fix_flag (flag : perms_flag) : Option file_perm :=
  match flag with
  | .PermR    => some .Read
  | .PermW    => some .Write
  | .PermX    => some .Execute
  | .PermBigX => some .Execute    -- following dash
  | .PermS    => none
  | .PermT    => none

/-- Lem: umask_add_flags -/
def umask_add_flags (who : Set.Set perms_who) (flags : Set.Set perms_flag) (perms : perms) : Smoosh.perms :=
  perms_for_many
    (fun old => Set.Set.union old (Set.Set.mapMaybe umask_fix_flag flags))
    who
    perms

/-- Lem: umask_delete_flags -/
def umask_delete_flags (who : Set.Set perms_who) (flags : Set.Set perms_flag) (perms : perms) : Smoosh.perms :=
  perms_for_many
    (fun old => Set.Set.difference old (Set.Set.mapMaybe umask_fix_flag flags))
    who
    perms

/-- Lem: umask_eval_action -/
def umask_eval_action (who : Set.Set perms_who) (action : perms_action) (perms : perms) : Smoosh.perms :=
  match action with
  -- ACTOP
  -- plain + and - do nothing
  | .ActOp .OpPlus  => perms
  | .ActOp .OpMinus => perms
  -- plain = resets all of the bits in who
  | .ActOp .OpEqual => perms_clear who perms
  -- ACTPERMS
  | .ActPerms .OpPlus flags  => umask_add_flags who flags perms
  | .ActPerms .OpMinus flags => umask_delete_flags who flags perms
  | .ActPerms .OpEqual flags => umask_add_flags who flags (perms_clear who perms)
  -- ACTCOPY
  | .ActCopy .OpPlus src =>
      umask_add_flags who (Set.Set.map flag_of_file_perm (perms_Who src perms)) perms
  | .ActCopy .OpMinus src =>
      umask_delete_flags who (Set.Set.map flag_of_file_perm (perms_Who src perms)) perms
  | .ActCopy .OpEqual src =>
      umask_add_flags who
        (Set.Set.map flag_of_file_perm (perms_Who src perms))
        (perms_clear who perms)

/-- Lem: umask_eval_actions -/
def umask_eval_actions (who : Set.Set perms_who) (actions : List perms_action) (perms : perms) : Smoosh.perms :=
  match actions with
  | [] => perms
  | action :: actions' =>
      let perms' := umask_eval_action who action perms
      umask_eval_actions who actions' perms'

/-- Lem: umask_eval_symbolic -/
def umask_eval_symbolic (clauses : List ((Set.Set perms_who) × List perms_action)) (perms : perms) : Smoosh.perms :=
  match clauses with
  | [] => perms
  | (who, actions) :: clauses' =>
      umask_eval_symbolic clauses' (umask_eval_actions who actions perms)

/-- Lem: builtin_umask -/
def builtin_umask [OS α]
    (s0 : os_state α) (argv : fields) (_env : env) : builtin_ret_stmt α :=
  let (opts, argv') := getopts ['S'] argv
  match argv' with
  | [] =>
      let umask := get_umask s0
      let umask_str :=
        if List.elem 'S' opts then
          /-
            If -S is specified, the message shall be in the following
            format:

           "u=%s,g=%s,o=%s\n", <owner permissions>, <group
            permissions>, <other permissions>

            where the three values shall be combinations of letters
            from the set { r, w, x }; the presence of a letter shall
            indicate that the corresponding bit is clear in the file
            mode creation mask.
          -/
          string_of_perms (invert_perms umask)
        else
          octal_string_of_perms umask
      .ok (safe_write_stdout "umask" (umask_str ++ "\n") (exit_with 0 s0), .Done)
  | smask :: _ =>
      match try_concrete smask with
      | none => .error (s0, "can't set symbolic mask")
      | some mask =>
        -- try to convert the string to an octal number
        match Num.readUnsignedInteger 8 (toCharList mask) with
        | .ok octal =>
          -- convert the number to permissions
          let new_mask := perms_of_nat (octal.toNat)
          -- set the permissions
          let s1 := set_umask s0 new_mask
          .ok (exit_with 0 s1, .Done)
        | .error _ =>
          match perms_symbolic_of_string mask with
          | .error msg => .error (s0, msg)
          | .ok ps =>
            -- load the mask and invert to permissions
            let mask0 := get_umask s0
            let perms := invert_perms mask0
            -- evaluate the permissions
            let new_perms := umask_eval_symbolic ps perms
            -- invert back and set
            let new_mask := invert_perms new_perms
            let s1 := set_umask s0 new_mask
            .ok (exit_with 0 s1, .Done)

/-
 just like dash, we'll implement newgrp with the executable;
 just call 'exec'
-/
/-- Lem: builtin_newgrp -/
def builtin_newgrp [OS α]
    (s0 : os_state α) (argv : fields) (env : env) : builtin_ret_stmt α :=
  match builtin_exec s0 (symbolic_string_of_string "newgrp" :: argv) env with
  | .error err => .error err
  | .ok (s1, st, _restore) => .ok (s1, st)

/-- Lem: show_alias -/
def show_alias [OS α]
    (os : os_state α) (p : String × String) : os_state α :=
  let (name, mapping) := p
  safe_write_stdout "alias" (name ++ "=" ++ mapping ++ "\n") os

/-- Lem: add_aliases -/
def add_aliases [OS α]
    (s0 : os_state α) (args : fields) : builtin_ret_stmt α :=
  match args with
  | [] => .ok (exit_with 0 s0, .Done)
  | arg :: args' =>
    match try_split_assign arg with
    | (name, some smapping) =>
      match try_concrete smapping with
      | none =>
        .error (s0,
          "couldn't symbolically alias " ++ name ++ " to " ++
          string_of_symbolic_string smapping)
      | some mapping => add_aliases (set_alias s0 name mapping) args'
    | (name, none) =>
      match Map.lookup name s0.sh.aliases with
      | none => .error (s0, name ++ " not found")
      | some mapping =>
        let s1 := show_alias s0 (name, mapping)
        if s1.sh.exit_code = 0 then add_aliases s1 args' else .ok (s1, .Done)

/-- Lem: builtin_alias -/
def builtin_alias [OS α]
    (s0 : os_state α) (argv : fields) (_env : env) : builtin_ret_stmt α :=
  match argv with
  | [] =>
    let aliases := Set.Set.toList (Map.toSet s0.sh.aliases)
    let s1 := List.foldl show_alias (exit_with 0 s0) aliases
    .ok (s1, .Done)
  | _ => add_aliases s0 argv

/-- Lem: remove_aliases -/
def remove_aliases [OS α]
    (s0 : os_state α) (names : fields) : builtin_ret_stmt α :=
  match names with
  | [] => .ok (s0, .Done)
  | sname :: names' =>
    match try_concrete sname with
    | none =>
      let s1 :=
        safe_write_stderr
          ("unalias: can't remove symbolic alias '" ++ string_of_symbolic_string sname ++ "'")
          s0
      if s1.sh.exit_code = 0 then remove_aliases s1 names' else .ok (s1, .Done)
    | some name =>
      let s1 :=
        if Map.map.contains name s0.sh.aliases then
          free_alias s0 name
        else
          fail_with ("unalias: " ++ name ++ " not found\n") s0
      remove_aliases s1 names'

/-- Lem: builtin_unalias -/
def builtin_unalias [OS α]
    (s0 : os_state α) (argv : fields) (_env : env) : builtin_ret_stmt α :=
  match argv with
  | [[.C '-', .C 'a']] =>
    let all_aliases := Set.Set.toList (Map.domain s0.sh.aliases)
    remove_aliases (exit_with 0 s0) (List.map symbolic_string_of_string all_aliases)
  | _ => remove_aliases (exit_with 0 s0) argv

/-
   When a signal for which a trap has been set is received while the
   shell is waiting for the completion of a utility executing a
   foreground command, the trap associated with that signal shall not
   be executed until after the foreground command has completed. When
   the shell is waiting, by means of the wait utility, for
   asynchronous commands to complete, the reception of a signal for
   which a trap has been set shall cause the wait utility to return
   immediately with an exit status >128, immediately after which the
   trap associated with that signal shall be taken.
-/
/-- Lem: builtin_wait -/
def builtin_wait [OS α]
    (s0 : os_state α) (argv : fields) (env : env) : builtin_ret_stmt α :=
  match argv with
  | [] =>
    let (s1, jobs) := active_jobs s0
    let waits := List.map (fun job => stmt.Wait job.pid .Unchecked none .WaitCommand) jobs
    -- the skip on the end makes sure we return 0
    .ok (s1, sequence (waits ++ [skip]))
  | pid :: pids' =>
    match pid_of_symbolic_string s0 pid with
    | .error msg => .error (s0, msg)
    | .ok (pid, _mode) =>
      /-
       some indirect recursion...
       waitpid in os.lem needs step_eval, which we don't have access to
       this also gives us the delayed parsing errors that both bash and dash do
      -/
      let next :=
        if List.isEmpty pids' then
          stmt.Wait pid .Unchecked none .WaitCommand
        else
          stmt.Semi
            (stmt.Wait pid .Unchecked none .WaitCommand)
            (simple_command "wait" pids' env)
      .ok (s0, next)

-- Lem: jobs_mode -/
def jobs_mode (opts : List Char) : jobs_mode :=
  match opts with
  | [] => .JobsNormal
  | 'l' :: _ => .JobsLong
  | 'p' :: _ => .JobsTerse
  | _ :: opts' => jobs_mode opts'

/-- Lem: show_job_specs -/
def show_job_specs [OS α]
    (mode : jobs_mode) (cur_prev : pid × pid)
    (specs : fields) (s0 : os_state α) : builtin_ret_stmt α :=
  match specs with
  | [] => .ok (exit_with 0 s0, .Done)
  | spec :: specs' =>
    match job_of_symbolic_string s0 spec with
    | .error msg => .error (s0, msg)
    | .ok job =>
      let s1 := show_job mode cur_prev job s0
      if s1.sh.exit_code = 0 then
        show_job_specs mode cur_prev specs' s1
      else
        .ok (s1, .Done)

/-- Lem: builtin_jobs -/
def builtin_jobs [OS α]
    (s0 : os_state α) (argv : fields) (_env : env) : builtin_ret_stmt α :=
  let (opts, argv') := getopts ['l', 'p'] argv
  let mode := jobs_mode opts
  let (s1, jobs) := active_jobs s0
  let cur_prev := cur_prev_jobs jobs
  match argv' with
  | [] =>
    let s2 := show_jobs none mode cur_prev jobs s1
    .ok (exit_with 0 s2, .Done)
  | _ => show_job_specs mode cur_prev argv' s1

/-- Lem: read_set_empty_vars -/
def read_set_empty_vars [OS α]
    (s0 : os_state α) (vars : List String) : builtin_ret_stmt α :=
  match vars with
  | [] => .ok (s0, .Done)
  | var :: vars' =>
    match set_param var [] s0 with
    | .error msg => .error (s0, msg)
    | .ok s1 => read_set_empty_vars s1 vars'

/-- Lem: read_assign_vars -/
def read_assign_vars [OS α]
    (s0 : os_state α) (vars : List String) (fs : fields) : builtin_ret_stmt α :=
  match vars, fs with
  | [], _ => .error (s0, "no variables specified")
  | _, [] => read_set_empty_vars s0 vars
  | [var], fs =>
    match set_param var (symbolic_string_of_fields fs) s0 with
    | .error msg => .error (s0, msg)
    | .ok s1 => .ok (s1, .Done)
  | var :: vars', ss :: fs' =>
    match set_param var ss s0 with
    | .error msg => .error (s0, msg)
    | .ok s1 => read_assign_vars s1 vars' fs'

/-- Lem: builtin_read -/
def builtin_read [OS α]
    (s0 : os_state α) (argv : fields) (env : env) : builtin_ret_stmt α :=
  let (opts, argv') := getopts ['r'] argv
  let escapes := if List.elem 'r' opts then .NoEscapes else .BackslashEscapes
  match try_concrete_fields_list argv' with
  | none =>
      .error (s0, "couldn't handle symbolic variable names: " ++ string_of_fields argv)
  | some [] => .error (s0, "no variables specified")
  | some vars =>
    match read_line_fd s0 STDIN escapes with
    | (s1, .ReadError msg) => .error (s1, msg)
    | (s1, .ReadBlocked pid) =>
      .ok (s1,
        stmt.Semi
          (stmt.Wait pid .Unchecked (some default_block) .WaitInternal)
          (simple_command "read" argv env))
    | (s1, .ReadSuccess line hit_eof) =>
      let trimmed := trimr_one_newline line
      let w := [.ExpS trimmed]
      let ifs := field_splitting s1 w
      match ifs with
      | .error msg => .error (s1, msg)
      | .ok ifs' =>
        match finalize_fields (combine_fields ifs') with
        | .error msg => .error (s1, msg)
        | .ok f =>
          let ec := if read_eof_toBool hit_eof then 1 else 0
          read_assign_vars (exit_with ec s1) vars f

/-- Lem: builtin_test -/
def builtin_test [OS α]
    (s0 : os_state α) (argv : fields) (_env : env) : builtin_ret_stmt α :=
  match try_concrete_fields_list argv with
  | none =>
    .error (s0, "couldn't handle symbolic test expression: " ++ string_of_fields argv)
  -- shortcut
  | some [] => .ok (exit_with 1 s0, .Done)
  | some strs =>
    match parse_test_expr strs with
    | .error msg =>
      -- we do the error message manually so we can exit with 2
      -- (run_command returning Left will usually exit with 1)
      let s1 := safe_write_stderr ("test: parse error: " ++ msg ++ "\n") s0
      let s2 := exit_with 2 s1
      .ok (s2, .Done)
    | .ok expr =>
      let result := eval_test_expr s0 expr
      .ok (exit_with (if result then 0 else 1) s0, .Done)

/-- Lem: builtin_bracket -/
def builtin_bracket [OS α]
    (s0 : os_state α) (argv : fields) (env : env) : builtin_ret_stmt α :=
  match argv.reverse with
  | [.C ']'] :: rev_argv' => builtin_test s0 (List.reverse rev_argv') env
  | _ => .error (s0, "expected matching ']'")

/-- Lem: ascii_bell -/
def ascii_bell : Char := Char.ofNat 7
/-- Lem: ascii_formfeed -/
def ascii_formfeed : Char := Char.ofNat 12
/-- Lem: ascii_verticaltab -/
def ascii_verticaltab : Char := Char.ofNat 11

def is_octal_digit (c : Char) : Bool :=
  c ≥ '0' && c ≤ '7'

/-- Lem: sprintf_esc -/
def sprintf_esc (fmt : List Char) : String × List Char :=
  match fmt with
  | '\\' :: fmt' => ("\\", fmt')
  | 'a'  :: fmt' => (toString [ascii_bell], fmt')
  | 'b'  :: fmt' => ("\x08", fmt')
  | 'f'  :: fmt' => (toString [ascii_formfeed], fmt')
  | 'n'  :: fmt' => ("\n", fmt')
  | 'r'  :: fmt' => ("\r", fmt')
  | 't'  :: fmt' => ("\t", fmt')
  | 'v'  :: fmt' => (toString [ascii_verticaltab], fmt')
  | d1 :: d2 :: d3 :: fmt' =>
    if is_octal_digit d1 then
      let (other_digits, rest) := List.span is_octal_digit [d2, d3]
      let num_cs := d1 :: other_digits
      match Num.readUnsignedInteger 8 num_cs with
      | .error msg =>
        panic! ("!!! couldn't read octal digits: " ++
          toString num_cs ++ "(" ++ msg ++ ")")
      | .ok n => (toString [Char.ofNat (n.toNat)], rest ++ fmt')
    else
      -- no octal digits... just write the unrecognized character
      ("\\" ++ toString [d1], d2 :: d3 :: fmt')
  | c :: fmt' =>
    -- TODO 2019-05-21 unspec
    ("\\" ++ toString [c], fmt')
  | [] => ("\\", [])

/-
Each conversion specification is introduced by the <percent-sign> character ( '%' ).
After the character '%', the following shall appear in sequence:
The conversion specifiers and their meanings are:
d,i,o,u,x,X
The integer argument shall be written as signed decimal ( d or i ), unsigned octal ( o ), unsigned decimal ( u ), or unsigned hexadecimal notation ( x and X ). The d and i specifiers shall convert to signed decimal in the style "[-]dddd". The x conversion specifier shall use the numbers and letters "0123456789abcdef" and the X conversion specifier shall use the numbers and letters "0123456789ABCDEF". The precision component of the argument shall specify the minimum number of digits to appear. If the value being converted can be represented in fewer digits than the specified minimum, it shall be expanded with leading zeros. The default precision shall be 1. The result of converting a zero value with a precision of 0 shall be no characters. If both the field width and precision are omitted, the implementation may precede, follow, or precede and follow numeric arguments of types d, i, and u with <blank> characters; arguments of type o (octal) may be preceded with leading zeros.
BUT: The implementation shall not precede or follow output from the d or u conversion specifiers with <blank> characters not specified by the format operand.
BUT: The implementation shall not precede output from the o conversion specifier with zeros not specified by the format operand.
The format operand shall be reused as often as necessary to satisfy the argument operands. Any extra b, c, or s conversion specifiers shall be evaluated as if a null string argument were supplied; other extra conversion specifications shall be evaluated as if a zero argument were supplied. If the format operand contains no conversion specifications and argument operands are present, the results are unspecified.
If a character sequence in the format operand begins with a '%' character, but does not form a valid conversion specification, the behavior is unspecified.
-/

/-- Lem: sprintf_format_b -/
partial def sprintf_format_b
    (fmt : List Char) (args : fields) (arg : List Char) (s : String) :
    String × List Char × fields :=
  match arg with
  | [] => (s, fmt, args)
  | '\\' :: 'c' :: _ignored =>
  /-
   '\c', which shall not be written and shall cause printf to
   ignore any remaining characters in the string operand
   containing it, any remaining string operands, and any
   additional characters in the format operand *)
  -/
    (s, [], [])
  | '\\' :: arg' =>
    let (esc, arg'') := sprintf_esc arg'
    sprintf_format_b fmt args arg'' (s ++ esc)
  | c :: arg' =>
    sprintf_format_b fmt args arg' (s ++ toString [c])

/-- Lem: printf_justification type -/
inductive printf_justification where
  | JustifyLeft
  | JustifyRight
deriving DecidableEq, Repr

/-- Lem: printf_padding type -/
inductive printf_padding where
  | PadSpace
  | PadZero
deriving DecidableEq, Repr

/-- Lem: printf_padding -/
def printf_padding_fn (justify : printf_justification) :=
  match justify with
  | .JustifyLeft  => pad_right_with
  | .JustifyRight => pad_left_with

/-- Lem: printf_sign type -/
inductive printf_sign where
  | SignNone
  | SignSpace
  | SignAlways
deriving DecidableEq, Repr

/-- Lem: printf_spec type -/
structure printf_spec where
  justify      : printf_justification   -- '-' or not
  sign         : printf_sign            -- '+' or ' '
  alternative  : Bool                   -- '#'
  padding      : printf_padding         -- '0'
  width        : Option Nat
  precision    : Option Nat
deriving Repr, DecidableEq

/-- Lem: printf_default_spec -/
def printf_default_spec : printf_spec :=
  { justify     := .JustifyRight
    sign        := .SignNone
    alternative := false
    padding     := .PadSpace
    width       := none
    precision   := none }

/-- Lem: printf_parse_flags -/
partial def printf_parse_flags : printf_spec × List Char → printf_spec × List Char
  | (spec, fmt) =>
    match fmt with
    | '-' :: fmt' =>
      printf_parse_flags ({ spec with justify := .JustifyLeft, padding := .PadSpace }, fmt')
    | ' ' :: fmt' => printf_parse_flags ({ spec with sign := .SignSpace }, fmt')
    | '+' :: fmt' => printf_parse_flags ({ spec with sign := .SignAlways }, fmt')
    | '#' :: fmt' => printf_parse_flags ({ spec with alternative := true }, fmt')
    | '0' :: fmt' =>
        /-
         If the '0' and '-' flags both appear, the '0' flag shall be
         ignored. For d, i , o, u, x, and X conversion specifiers, if a
         precision is specified, the '0' flag shall be ignored.
        -/
        let leftJust : Bool :=
          match spec.justify with
          | .JustifyLeft  => true
          | .JustifyRight => false
        let hasPrec : Bool := spec.precision.isSome
        if leftJust || hasPrec then
          printf_parse_flags (spec, fmt')
        else
          printf_parse_flags ({ spec with padding := .PadZero }, fmt')
    | _ => (spec, fmt)

/-- Lem: printf_parse_field_width -/
def printf_parse_field_width : printf_spec × List Char → printf_spec × List Char
  | (spec, fmt) =>
    match Num.parse_nat fmt with
    | .error _ => (spec, fmt)
    | .ok (width, fmt') => ({ spec with width := some width }, fmt')

/-- Lem: printf_parse_precision -/
def printf_parse_precision : printf_spec × List Char → printf_spec × List Char
  | (spec, fmt) =>
    match fmt with
    | '.' :: fmt' =>
      let (precision, fmt'') :=
        match Num.parse_nat fmt' with
        | .error _ => (0, fmt')
        | .ok (p, rest) => (p, rest)
      ({ spec with precision := some precision }, fmt'')
    | _ => (spec, fmt)

/-- Lem: printf_parse_spec -/
def printf_parse_spec (fmt : List Char) : printf_spec × List Char :=
  printf_parse_precision <|
    printf_parse_field_width <|
      printf_parse_flags (printf_default_spec, fmt)

/-- Lem: printf_numeric type -/
inductive printf_numeric where
  | Decimal (signed : Bool) -- signed
  | Octal
  | Hex (uppercase : Bool) -- uppercase
deriving DecidableEq, Repr

/-- Lem: string_of_printf_numeric -/
def string_of_printf_numeric : printf_numeric → String
  | .Decimal true  => "%d"
  | .Decimal false => "%u"
  | .Octal         => "%o"
  | .Hex true      => "%X"
  | .Hex false     => "%x"

/-- Lem: printf_parse_numeric -/
def printf_parse_numeric : List Char → Option (printf_numeric × List Char)
  | 'd' :: fmt' => some (.Decimal true,  fmt')
  | 'i' :: fmt' => some (.Decimal true,  fmt')
  | 'u' :: fmt' => some (.Decimal false, fmt')
  | 'o' :: fmt' => some (.Octal,         fmt')
  | 'x' :: fmt' => some (.Hex false,     fmt')
  | 'X' :: fmt' => some (.Hex true,      fmt')
  | _           => none

/-- Lem: printf_pad_number -/
def printf_pad_number (spec : printf_spec) (prefixs num : String) : String :=
  let real_width : Nat :=
    match spec.width with
    | none        => 0
    | some width  => width - (stringLength prefixs)
  match spec.padding with
  | .PadSpace => printf_padding_fn spec.justify ' ' (prefixs ++ num) real_width
  | .PadZero  => prefixs ++ printf_padding_fn spec.justify '0' num real_width

/-- Lem: val sprintf_format_numeric : printf_spec -> printf_numeric -> integer -> string -/
def sprintf_format_numeric (spec : printf_spec) (mode : printf_numeric) (n : Int) : String :=
  match mode with
  | .Decimal true =>
    -- TODO 2018-10-06 UNSPEC spec.alternative
    let sign : String :=
      if n < 0 then
        "-"
      else
        match spec.sign with
        | .SignNone   => ""
        | .SignSpace  => " "
        | .SignAlways => "+"
    let abs_n : Int := if n < 0 then -n else n
    printf_pad_number spec sign (Num.unbounded_write_decimal abs_n)
  | .Decimal false =>
    printf_pad_number spec "" (Num.unbounded_write_decimal (Num.unbounded_unsigned64 n))
  | .Octal =>
    -- TODO 2018-10-06 octal and hex should be unsigned
    let prefixs := if spec.alternative then "0" else ""
    printf_pad_number spec prefixs (Num.unbounded_write_octal (Num.unbounded_unsigned64 n))
  | .Hex upper =>
    let prefixs := if spec.alternative then "0x" else ""
    let num    := Num.unbounded_write_hex (Num.unbounded_unsigned64 n)
    let res    := printf_pad_number spec prefixs num
    if upper then uppercase res else res

/-- Lem: printf_concrete_arg -/
def printf_concrete_arg (args : fields) : Option (Option String × fields) :=
  match args with
  | [] => none
  | arg :: args' =>
    match try_concrete arg with
    | none   => some (none, args')
    | some s => some (some s, args')

/-- Lem: val printf_format : forall 'a. OS 'a => os_state 'a -> list char -> fields -> os_state 'a * list char * fields -/
def printf_format [OS α]
    (s0 : os_state α) (fmt0 : List Char) (args0 : fields) :
    os_state α × List Char × fields :=
  let (spec, fmt1) := printf_parse_spec fmt0
  let string_precision (s : String) : String :=
    match spec.precision with
    | none => s
    | some width => toString (List.take width (toCharList s))
  /-
    The results are undefined if there are insufficient arguments for
    the format. If the format is exhausted while arguments remain,
    the excess arguments shall be ignored.
  -/
  let sprintf_res : Sum (String × String × Nat × List Char × fields) (String × List Char × fields) :=
    match fmt1, printf_parse_numeric fmt1, printf_concrete_arg args0 with
    | [], _, _ => Sum.inl ("", "%: missing format character", 1, [], args0)
    | '%' :: fmt2, _, _ =>
      match fmt0 with
      | '%' :: _ =>
        Sum.inr ("%", fmt2, args0)
      | _ =>
        Sum.inl ("", "%: conversion specifications cannot be applied to the %% escape", 1, [], args0)
    -- %s
    | 's' :: fmt2, _, some (some s, args1) =>
      Sum.inr (string_precision s, fmt2, args1)
    | 's' :: fmt2, _, some (none, args1) =>
      Sum.inl ("", "%s: symbolic argument", 2, fmt2, args1)
    | 's' :: fmt2, _, none => Sum.inr ("", fmt2, [])
    -- %b
    | 'b' :: fmt2, _, some (some s, args1) =>
      let (out, fmt3, args2) := sprintf_format_b fmt2 args1 (toCharList s) ""
      Sum.inr (string_precision out, fmt3, args2)
    | 'b' :: fmt2, _, some (none, args1) =>
      Sum.inl ("", "%b: symbolic argument", 2, fmt2, args1)
    | 'b' :: fmt2, _, none => Sum.inr ("", fmt2, [])
    -- %c (manual to avoid try_concrete overapprox)
    | 'c' :: fmt2, _, _ =>
      match args0 with
      | (.C c :: []) :: args1 => Sum.inr (toString [c], fmt2, args1)
      | [] => Sum.inr ("", fmt2, [])                 -- unspec, could be NUL
      | _ :: args1 => Sum.inl ("", "%c: symbolic argument", 2, fmt2, args1)
    -- numeric
    -- TODO 2019-05-21 The printf utility is required to notify the user
    -- when conversion errors are detected while producing numeric output
    | _, some (num_mode, fmt2), some (some s, args1) =>
      match Num.unbounded_read (toCharList s) with
      | .error msg =>
        Sum.inl ( sprintf_format_numeric spec num_mode 0
                , string_of_printf_numeric num_mode ++ ": invalid number: " ++ msg
                , 1
                , fmt2
                , args1 )
      | .ok n =>
        Sum.inr (sprintf_format_numeric spec num_mode n, fmt2, args1)
    | _, some (num_mode, fmt2), some (none, args1) =>
      Sum.inl ( sprintf_format_numeric spec num_mode 0
              , string_of_printf_numeric num_mode ++ ": symbolic argument"
              , 2
              , fmt2
              , args1 )
    | _, some (num_mode, fmt2), none =>
      Sum.inr (sprintf_format_numeric spec num_mode 0, fmt2, [])
    -- unrecognized
    | c :: fmt2, _, _ =>
      /-
        TODO 2019-05-21 If a character sequence in the format
        operand begins with a '%' character, but does not form a
        valid conversion specification, the behavior is
        unspecified.
      -/
      let f_str := toString ['%', c]
      Sum.inl (f_str, "unrecognized format " ++ f_str, 1, fmt2, args0)
  -- compute what we'll actually print
  let (s1, ok, out, fmt2, args1) : os_state α × Bool × String × List Char × fields :=
    match sprintf_res with
    | Sum.inl (out, msg, ec, fmt2, args1) =>
      let s1 := write_stderr (msg ++ "\n") s0
      (exit_with ec s1, out ≠ "", out, fmt2, args1)
    | Sum.inr (out, fmt2, args1) =>
      (s0, true, out, fmt2, args1)
  -- apply padding (numbers already padded; then this is a noop)
  let padded : String :=
    match spec.width with
    | none => out
    | some width => if ok then (printf_padding_fn spec.justify) ' ' out width else out
  (safe_write_stdout "printf" padded s1, fmt2, args1)

-- invariant: called with an exit code of 0, to be changed later
/-- Lem: printf_loop -/
partial def printf_loop [OS α]
    (s0 : os_state α)
    (orig_fmt : List Char) (orig_args : fields)
    (fmt : List Char) (args : fields)
    : builtin_ret_stmt α :=
  match fmt with
  | [] =>
    match args with
    | [] => .ok (s0, .Done)
    | _  =>
      /-
        The format operand shall be reused as often as necessary to
        satisfy the argument operands. Any extra b, c, or s
        conversion specifiers shall be evaluated as if a null
        string argument were supplied; other extra conversion
        specifications shall be evaluated as if a zero argument
        were supplied.
      -/
      if args.length = orig_args.length then
        /-
          If the format operand contains no conversion
          specifications and argument operands are present, the
          results are unspecified.  We'll avoid an infinite loop
          if we haven't actually consumed an arg.
        -/
        .ok (s0, .Done)
      else
        /-
          We _shouldn't_ need to reset args---if we got here, we
          consumed at least one arg and the whole process is
          deterministic. But here we are!
        -/
        printf_loop s0 orig_fmt args orig_fmt args
  | '\\' :: fmt' =>
    let (escaped, fmt'') := sprintf_esc fmt'
    let s1 := safe_write_stdout "printf" escaped s0
    printf_loop s1 orig_fmt orig_args fmt'' args
  | '%' :: fmt' =>
    let (s1, fmt'', args') := printf_format s0 fmt' args
    printf_loop s1 orig_fmt orig_args fmt'' args'
  | c :: fmt' =>
    let s1 := safe_write_stdout "printf" (String.ofList [c]) s0
    printf_loop s1 orig_fmt orig_args fmt' args



/-- Lem: builtin_printf -/
def builtin_printf [OS α]
    (s0 : os_state α) (argv : fields) (_env : env) : builtin_ret_stmt α :=
  match argv with
  | [] =>
    .ok (fail_with_code 2 "printf: usage printf format [arg...]\n" s0, .Done)
  | sfmt :: args =>
    match try_concrete sfmt with
    | none => .ok (fail_with_code 3 "printf: symbolic format string" s0, .Done)
    | some fmt =>
      let fmt_cl := toCharList fmt
      printf_loop (exit_with 0 s0) fmt_cl args fmt_cl args

/-- Lem: signal_pids
    INVARIANT: called with exit code 0; may change to 1 if any signal fails. -/
def signal_pids [OS α]
    (s0 : os_state α) (sig : signal) (spids : fields) : builtin_ret_stmt α :=
  match spids with
  | [] => .ok (s0, .Done)
  | ss_pid :: spids' =>
    match pid_of_symbolic_string s0 ss_pid with
    | .error msg => .error (s0, msg)
    | .ok (pid, smode) =>
      let (s1, ok) := signal_pid s0 sig pid smode
      let s2 := if !ok then exit_with 1 s1 else s1
      signal_pids s2 sig spids'

/-- Lem: kill_signal_of_num -/
def kill_signal_of_num [OS α]
    (s0 : os_state α) (s_signal : String) : (os_state α × Option signal) :=
  match Num.readNat (toCharList s_signal) with
  | .error _ => (s0, none)
  | .ok 0    => (s0, some .EXIT)
  | .ok 1    => (s0, some .SIGHUP)
  | .ok 2    => (s0, some .SIGINT)
  | .ok 3    => (s0, some .SIGQUIT)
  | .ok 6    => (s0, some .SIGABRT)
  | .ok 9    => (s0, some .SIGKILL)
  | .ok 14   => (s0, some .SIGALRM)
  | .ok 15   => (s0, some .SIGTERM)
  | .ok n    =>
    match signal_of_platform_int n with
    | none => (s0, none)
    | some s =>
      let s1 :=
        log_trace .Trace_undef
          "The effects of specifying any signal_number other than those listed below are undefined. [0, 1, 2, 3, 6, 9, 14, 15]"
          s0
      (s1, some s)

/-- Lem: builtin_kill
  kill -s signal_name pid...
  kill -l [signal_number | exit_status]


XSI
  kill [-signal_name] pid...
  kill [-signal_number] pid... -/
def builtin_kill {α : Type u} [OS α]
    (s0 : os_state α) (argv : fields) (_env : env) : builtin_ret_stmt α :=
  let usage_msg := "usage: kill [-s signal | -signal] pid ... or kill -l signal"
  match argv with
  | [.C '-', .C 'l'] :: argv' =>
    match argv' with
    | [] =>
      let sorted_signals :=
        sortBy
          (fun s1 s2 => platform_int_of_signal s1 <= platform_int_of_signal s2)
          all_signals
      let names := List.map string_of_signal sorted_signals
      let s1 := safe_write_stdout "kill" (String.intercalate "\n" names ++ "\n") (exit_with 0 s0)
      .ok (s1, .Done)
    | [ss_num] =>
      let s_num := string_of_symbolic_string ss_num
      match Num.readNat (toCharList s_num) with
      | .error msg =>
        .error (s0,
          "non-numeric signal number or exit code '" ++ s_num ++ "'" ++
          " (" ++ msg ++ ")")
      | .ok n =>
          let (signum, was_retval) := if n > 128 then (n - 128, true) else (n, false)
          match signal_of_platform_int signum with
          | none =>
            let ec_text := if was_retval then " (from " ++ s_num ++ ")" else ""
            .error (s0, (stringFromNat signum) ++ ec_text ++ " is not a valid signal number")
          | some sig =>
            let s1 := safe_write_stdout "kill" (string_of_signal sig ++ "\n") (exit_with 0 s0)
            .ok (s1, .Done)
    | _ => .error (s0, usage_msg)
  | [.C '-', .C 's'] :: argv' =>
    match strip_double_dash argv' with
    | ss_signal :: pids =>
      let (s1, _concretized, s_signal) := concretize s0 ss_signal
      match (s_signal, signal_of_string s_signal) with
      | (_, some sig) => signal_pids (exit_with 0 s1) sig pids
      | ("0", _) => signal_pids (exit_with 0 s1) .EXIT pids
      | (_, none) => .error (s0, "no such signal " ++ s_signal)
    | _ => .error (s0, usage_msg)
  | (.C '-' :: ss_signal) :: argv' =>
    let (s1, _concretized, s_signal) := concretize s0 ss_signal
    let (s2, m1) := kill_signal_of_num s1 s_signal
    let m_signal :=
      match m1 with
      | none      => signal_of_string s_signal
      | some sig  => some sig
    match m_signal with
    | none => .error (s2, "no such signal " ++ s_signal)
    | some sig => signal_pids (exit_with 0 s2) sig (strip_double_dash argv')
  | pids => signal_pids (exit_with 0 s0) .SIGTERM (strip_double_dash pids)

def OPTIND : String := "OPTIND"
def OPTARG : String := "OPTARG"
def QMARK  : symbolic_string := symbolic_string_of_string "?"

/-- Lem: getopts_OPTIND -/
def getopts_OPTIND [OS α] (os0 : os_state α) : Nat :=
  match Map.lookup OPTIND os0.sh.env with
  | none => 1
  | some ss =>
    match nat_of_symbolic_string ss with
    | .error _ => 1
    | .ok n    => n

/-- Lem: getopts_incr_OPTIND -/
def getopts_incr_OPTIND [OS α] (os0 : os_state α) : os_state α :=
  internal_set_param OPTIND
    (symbolic_string_of_nat (getopts_OPTIND os0 + 1))
    os0

/-- Lem: getopts_incr_optoff -/
def getopts_incr_optoff [OS α] (os0 : os_state α) : os_state α :=
  match os0.sh.optoff with
  | none => getopts_incr_OPTIND { os0 with sh := { os0.sh with optoff := some 1 } }
  | some n => { os0 with sh := { os0.sh with optoff := some (n + 1) } }

/-- Lem: getopts_reset_optoff -/
def getopts_reset_optoff [OS α] (os0 : os_state α) : os_state α :=
  { os0 with sh := { os0.sh with optoff := none } }



/-- Lem: elemIndex : Char -> List Char -> Option Nat -/
private def elemIndex (c : Char) : List Char → Option Nat
  | []      => none
  | x :: xs => if x = c then some 0 else (elemIndex c xs).map (· + 1)



/-- Lem: val getopts_maybe_reset_optoff :
  forall 'a. OS 'a => symbolic_string -> os_state 'a -> os_state 'a -/
def getopts_maybe_reset_optoff [OS α]
    (opt_rest : symbolic_string) (os0 : os_state α) : os_state α :=
  if opt_rest.isEmpty then
    getopts_reset_optoff os0
  else
    os0

/-- Lem: val getopts_loop :
  forall 'a. OS 'a =>
    os_state 'a -> list char -> string -> nat -> fields ->
    either (os_state 'a * string) (os_state 'a * stmt) -/
partial def getopts_loop [OS α]
    (os0 : os_state α) (opts : List Char) (optvar : String) (ind : Nat) (args : fields)
    : builtin_ret_stmt α :=
  -- when optoff is set, OPTIND (and so ind) will point 1 _past_ where we are
  let optoff_correction :=
    match os0.sh.optoff with
    | none   => 0
    | some _ => 1
  match args.drop (ind - optoff_correction - 1) with
  | [.C '-', .C '-'] :: _ =>
    -- make sure to increment OPTIND, because -- isn't a param
    let os1 :=
      unset_param OPTARG os0
      |> getopts_reset_optoff
      |> getopts_incr_OPTIND
      |> internal_set_param optvar QMARK
    .ok (exit_with 1 os1, .Done)
  | (.C '-' :: arg_opts) :: args' =>
    -- use OPTIND/ind and optoff to find out if we have another character
    let (os1, m_c, opt_rest) : os_state α × Option Char × symbolic_string :=
      match os0.sh.optoff, arg_opts with
      | none, (.C c :: rest) =>
        (getopts_incr_optoff os0, some c, rest)
      | some n, cs =>
        match cs.drop n with
        | [] => (os0, none, [])
        | (.C c :: rest) => (getopts_incr_optoff os0, some c, rest)
        | _ =>
          let os1 :=
            log_trace .Trace_symbolic
              ("couldn't parse symbolic option '" ++ string_of_symbolic_string arg_opts ++ "'")
              os0
          (os1, none, [])
      | _, _ =>
        let os1 :=
          log_trace .Trace_symbolic
            ("couldn't parse symbolic option '" ++ string_of_symbolic_string arg_opts ++ "'")
            os0
        (os1, none, [])
    match m_c with
    | none =>
      -- index pushed past the end; move on
      getopts_loop (getopts_reset_optoff os1) opts optvar ind args
    | some c =>
      -- got a character. see if we can parse it from the options
      let os2 :=
        if Smoosh.is_alphanumeric c then os1
        else
          log_trace .Trace_unspec
            "The use of other option characters that are not alphanumeric produces unspecified results."
            os1
      let s_opt  := toString [c]
      let ss_opt := symbolic_string_of_string s_opt
      match elemIndex c opts with
      | none =>
        let os3 :=

          -- If an option character not contained in the optstring
          -- operand is found where an option character is
          -- expected, the shell variable specified by name shall
          -- be set to the <question-mark> ( '?' ) character. In
          -- this case, if the first character in optstring is a
          -- <colon> ( ':' ), the shell variable OPTARG shall be
          -- set to the option character found, but no output shall
          -- be written to standard error; otherwise, the shell
          -- variable OPTARG shall be unset and a diagnostic
          -- message shall be written to standard error.

          match opts with
          | ':' :: _ =>
            internal_set_param OPTARG ss_opt os2
          | _ =>
            let os3 := safe_write_stderr ("illegal option -- '" ++ s_opt ++ "'\n") os2
            getopts_maybe_reset_optoff opt_rest (unset_param OPTARG os3)
        .ok (exit_with 0 (internal_set_param optvar QMARK os3), .Done)
      | some n =>
        -- set the specified variable
        let os3 := unset_param OPTARG
          (internal_set_param optvar ss_opt os2)
        -- check to see if we need to set OPTARG
        match List.drop (n + 1) opts with
        | ':' :: _ =>
          let os4 :=
            match opt_rest, args' with
            | [], [] =>

              -- If the first character of optstring is a <colon>,
              -- the shell variable specified by name shall be set
              -- to the <colon> character and the shell variable
              -- OPTARG shall be set to the option character
              -- found.

              match opts with
              | ':' :: _ =>
                internal_set_param OPTARG ss_opt
                  (internal_set_param optvar (symbolic_string_of_string ":") os3)
              | _ =>
                let msg := "option requires an argument -- '" ++ s_opt ++ "'\n"
                internal_set_param OPTARG QMARK (safe_write_stderr msg os3)
            | [], (arg :: _) =>
              getopts_incr_OPTIND (internal_set_param OPTARG arg os3)
            | _, _ => internal_set_param OPTARG opt_rest os3
          .ok (exit_with 0 (getopts_reset_optoff os4), .Done)
        | _ => .ok (exit_with 0 (getopts_maybe_reset_optoff opt_rest os3), .Done)
  | _ =>
    let os1 := unset_param OPTARG os0 |> internal_set_param optvar QMARK
    .ok (exit_with 1 os1, .Done)

/-- Lem: builtin_getopts -/
def builtin_getopts [OS α]
    (os0 : os_state α) (argv : fields) (_env : env) : builtin_ret_stmt α :=
  match argv with
  | ss_optstring :: ss_name :: argv' =>
    /-
      initialize our working info:
      what's the option string and variable?
      were args specified, or do we use positional params?
    -/
    let (os1, _, optstring) := concretize os0 ss_optstring
    let (os2, _, name)      := concretize os1 ss_name
    let args : fields :=
      match argv' with
      | [] =>
        match os2.sh.positional_params with
        | []        => []
        | _ :: ps   => ps
      | _  => argv'
    -- index in and see whether we have an argument
    getopts_loop os2 (toCharList optstring) name (getopts_OPTIND os2) args
  | _ => .error (os0, "usage: getopts optstring name [arg...]")

/-- Lem: send_sigcont -/
def send_sigcont [OS α]
    (os0 : os_state α) (cmd_name : String) (job : job_info) (bg_mode : bg_mode) : os_state α :=
  let curprev := cur_prev_jobs os0.sh.jobs
  let mode    := if is_fg bg_mode then .JobsFGCommand else .JobsBGCommand
  let os1     := safe_write_stdout cmd_name (string_of_job mode curprev job) os0
  let (os2, _tc_ok) := if is_fg bg_mode then tc_setfg os0 job.pid else (os1, true)
  let (os3, _sig_ok) := signal_pid os2 .SIGCONT job.pid .SignalProcessGroup
  os3

/-- Lem: builtin_fg -/
def builtin_fg [OS α]
    (os0 : os_state α) (argv : fields) (_env : env) : builtin_ret_stmt α :=
  if !Set.Set.member .Sh_monitor os0.sh.opts then
    .error (os0, "job control is disabled")
  else
    let m_job : Except String job_info :=
      match argv with
      | [] =>
        match os0.sh.jobs with
        | []      => .error "no current job"
        | job::_  => .ok job
      | [ss_spec] => job_of_symbolic_string os0 ss_spec
      | _ => .error "expects just one job spec"
    match m_job with
    | .error err => .error (os0, err)
    | .ok job =>
      let os1 := send_sigcont os0 "fg" job .FG
      .ok (os1, .Wait job.pid .Unchecked none .WaitInternal)



/-- Lem: collect_either for Except String -/
private def collect_except : List (Except String β) → (List String × List β)
  | [] => ([], [])
  | x :: xs =>
      let (es, ys) := collect_except xs
      match x with
      | .error e => (e :: es, ys)
      | .ok y    => (es, y :: ys)



/-- Lem: jobs_of_argv -/
def jobs_of_argv [OS α]
    (os0 : os_state α) (argv : fields) : (List String × List job_info) :=
  let specs : List (Except String job_info) :=
    argv.map (job_of_symbolic_string os0)
  let (errors, jobs) := collect_except specs
  if errors.isEmpty && jobs.isEmpty then
    match os0.sh.jobs with
    | []      => (["no current job"], [])
    | job::_  => ([], [job])
  else (errors, jobs)

/-- Lem: builtin_bg -/
def builtin_bg [OS α]
    (os0 : os_state α) (argv : fields) (_env : env) : builtin_ret_stmt α :=
  if !Set.Set.member .Sh_monitor os0.sh.opts then
    .error (os0, "job control is disabled")
  else
    let (errors, jobs) := jobs_of_argv os0 argv
    match errors, jobs with
    | [], [] => .error (os0, "no current job")
    | errors, jobs =>
      let os1 := jobs.foldl (fun os job => send_sigcont os "bg" job .BG) os0
      match errors with
      | [] => .ok (os1, .Done)
      | _  => .error (os1, "couldn't parse job specs:\n" ++ String.intercalate "\n  " errors)



def reverseMap (f : α → β) (xs : List α) : List β :=
  xs.foldl (fun acc x => f x :: acc) []



/-- Lem: builtin_help -/
def builtin_help [OS α]
    (os0 : os_state α) (argv : fields) (_env : env) : builtin_ret_stmt α :=
  let show_list (ls : List String) (os : os_state α) : os_state α :=
    safe_write_stdout "help" (String.intercalate "\n" ls ++ "\n") (exit_with 0 os)
  match argv with
  | [] =>
    let usage :=
      Version.smoosh_info ++
      "usage:\n" ++
      "    help builtins    list implemented builtins\n" ++
      "    help version     show smoosh version number\n" ++
      "    help steps       show evaluation steps\n" ++
      "    help spec        show unspecified/undefined behaviors\n" ++
      "    help trace       show full trace\n"
    .ok (exit_with 1 (write_stderr usage os0), .Done)
  | [ss_arg] =>
    let (os1, _, s_arg) := concretize os0 ss_arg
    match s_arg with
    | "builtins" =>
      let os2 := safe_write_stdout "help" "implemented builtins:\n" os1
      .ok (show_list builtin_names os2, .Done)
    | "version" =>
      let os2 := safe_write_stdout "help" Version.smoosh_info (exit_with 0 os1)
      .ok (os2, .Done)
    | "steps" =>
      let steps := reverseMap string_of_evaluation_step (extract_trace os1)
      .ok (show_list steps os1, .Done)
    | "trace" =>
      let trace := reverseMap string_of_log_entry os1.log
      .ok (show_list trace os1, .Done)
    | "spec" =>
      if in_unspecified_state os1 then
        let steps := List.reverse (extract_unspec os1)
        .ok (show_list steps os1, .Done)
      else
        .ok (safe_write_stdout "help" "no unspecified/undefined behavior\n" (exit_with 0 os1), .Done)
    | _ => .error (os0, "unknown argument: " ++ s_arg)
  | _ =>
    .error (os0, "unknown arguments: " ++ string_of_fields argv)



-- history

/-
bash
history: history [-c] [-d offset] [n] or history -awrn [filename] or history -ps arg [arg...]
    Display the history list with line numbers.  Lines listed with
    with a `*' have been modified.  Argument of N says to list only
    the last N lines.  The `-c' option causes the history list to be
    cleared by deleting all of the entries.  The `-d' option deletes
    the history entry at offset OFFSET.  The `-w' option writes out the
    current history to the history file;  `-r' means to read the file and
    append the contents to the history list instead.  `-a' means
    to append history lines from this session to the history file.
    Argument `-n' means to read all history lines not already read
    from the history file and append them to the history list.

    If FILENAME is given, then that is used as the history file else
    if $HISTFILE has a value, that is used, else ~/.bash_history.
    If the -s option is supplied, the non-option ARGs are appended to
    the history list as a single entry.  The -p option means to perform
    history expansion on each ARG and display the result, without storing
    anything in the history list.

    If the $HISTTIMEFORMAT variable is set and not null, its value is used
    as a format string for strftime(3) to print the time stamp associated
    with each displayed history entry.  No time stamps are printed otherwise.
yash
history: manage command history

Syntax:
	history [-cF] [-d entry] [-s command] [-r file] [-w file] [count]

Options:
	-c       --clear
	-d ...   --delete=...
	-r ...   --read=...
	-s ...   --set=...
	-w ...   --write=...
	-F       --flush-file

Try `man yash' for details.
-/

/-- Lem: builtin_history -/
def builtin_history [OS α]
    (s0 : os_state α) (argv : fields) (_env : env) : builtin_ret_stmt α :=
  match strip_double_dash argv with
  | [] =>
    let maxnum : Nat :=
      match s0.sh.history with
      | [] => 0
      | hs => maximum (hs.map Prod.fst)
    let numwidth : Nat := stringLength (stringFromNat maxnum)
    let shows : (Nat × stmt) → String
        | (num, c) => pad_left (stringFromNat num) numwidth ++ "\t" ++ string_of_stmt c
    let msgs : List String := (s0.sh.history.map shows).reverse
    let out : String := String.intercalate "\n" msgs ++ "\n"
    let s1 := safe_write_stdout "history" out (exit_with 0 s0)
    .ok (s1, .Done)
  | [[.C '-', .C 'c']] =>
    let s1 : os_state α := { s0 with sh := { s0.sh with history := [] } }
    .ok (exit_with 0 s1, .Done)
  | argv' => .error (s0, "unimplemented option: " ++ string_of_fields argv')

/-
  fc [-r] [-e editor] [first [last]]
  fc -l [-nr] [first [last]]
  fc -s [old=new] [first]
-/
/-- Lem: fc_mode type -/
inductive fc_mode where
  | FC_Edit (editor : symbolic_string)   -- default; -e
  | FC_List                              -- -l
  | FC_NoEdit                            -- -s

/-
  "The value in the FCEDIT variable shall be used as a default when
  -e is not specified. If FCEDIT is null or unset, ed shall be used
  as the editor."
-/
/-- Lem: val fc_default_mode : forall 'a. OS 'a => os_state 'a -> fc_mode -/
def fc_default_mode {α : Type u} [OS α] (s0 : os_state α) : Except String fc_mode :=
  match Smoosh.lookup_string_param s0 "FCEDIT" with
  | .ok (some ss) => .ok (.FC_Edit ss)
  | .ok none      => .ok (.FC_Edit (symbolic_string_of_string "ed"))
  | .error e      => .error e

/-- Lem: val string_of_fc_mode : fc_mode -> string -/
def string_of_fc_mode : fc_mode → String
  | .FC_Edit ss => "-e " ++ string_of_symbolic_string ss
  | .FC_List    => "-l"
  | .FC_NoEdit  => "-s"

/-- Lem: fc_opt -/
inductive fc_opt where
  | FC_Reverse    -- -r
  | FC_NoNumber   -- -n
deriving Repr, DecidableEq

/-- Lem: val string_of_fc_opt : fc_opt -> string -/
def string_of_fc_opt : fc_opt → String
  | .FC_Reverse  => "-r"
  | .FC_NoNumber => "-n"

/-- Lem: val fc_optchars : list char -/
def fc_optchars : List Char := "elsrn".toList

/-- Lem: val fc_options_loop : fields -> fc_mode -> set fc_opt -> either string (fields * fc_mode * set fc_opt) -/
partial def fc_options_loop
    (argv : fields) (mode : fc_mode) (opts : Set.Set fc_opt)
    : Except String (fields × fc_mode × Set.Set fc_opt) :=
  match getopt fc_optchars argv with
  | none => .ok (argv, mode, opts)
  | some (none, argv') => .ok (argv', mode, opts)
  | some (some opt, argv') =>
    match opt with
    | 'e' =>
      match argv' with
      | [] => .error "missing editor after -e"
      | ((.C '-') :: weird_editor) :: argv'' =>
        -- handle `fc -er foo` as error but `fc -e -weirdo` as OK
        let orig_arg :=
          match argv with
          | []      => []
          | x :: _  => x
        -- if orig_arg = .C '-':: (.C 'e') :: weird_editor then
        --   .error ("missing editor in grouped option '" ++
        --             string_of_symbolic_string orig_arg ++ "'")
        -- else
        --   fc_options_loop argv'' (.FC_Edit weird_editor) opts
        match orig_arg with
        | .C '-' :: .C 'e' :: weird_editor =>
          .error ("missing editor in grouped option '" ++
                   string_of_symbolic_string orig_arg ++ "'")
        | _ => fc_options_loop argv'' (.FC_Edit weird_editor) opts
      | editor :: argv'' => fc_options_loop argv'' (.FC_Edit editor) opts
    | 'l' => fc_options_loop argv' .FC_List opts
    | 's' => fc_options_loop argv' .FC_NoEdit opts
    | 'r' => fc_options_loop argv' mode (Set.Set.insert fc_opt.FC_Reverse opts)
    | 'n' => fc_options_loop argv' mode (Set.Set.insert fc_opt.FC_NoNumber opts)
    | _ => .error ("unrecognized option '" ++ toString [opt] ++ "'")

/-- Lem: fc_operand type -/
inductive fc_operand where
  | FC_CmdNumber (n : Nat)    -- [+]n
  | FC_Previous  (n : Nat)    -- -n
  | FC_Matching  (s : String) -- string
deriving Repr, DecidableEq

/-- Lem: string_of_fc_operand -/
def string_of_fc_operand : fc_operand → String
  | .FC_CmdNumber n => "+" ++ stringFromNat n
  | .FC_Previous n  => "~" ++ stringFromNat n
  | .FC_Matching s  => s

/-- Lem: val fc_operand : symbolic_string -> either string fc_operand -/
def fc_Operand (ss_arg : symbolic_string) : Except String fc_operand :=
  match try_concrete ss_arg with
  | none => .error ("couldn't handle symbolic operand '" ++
                     string_of_symbolic_string ss_arg ++ "'")
  | some arg =>
    match Num.readSignedInteger 10 (toCharList arg) with
    | .ok n =>
      if n < (Int.ofNat 0) then
        .ok (.FC_Previous (Int.toNat (-n)))
      else if n > (Int.ofNat 0) then
        .ok (.FC_CmdNumber (Int.toNat n))
      else
        .error ("invalid operand '" ++ arg ++ "'")
    | .error _ => .ok (.FC_Matching arg)

/-- Lem: fc_noedit_operands type -/
structure fc_noedit_operands where
  noedit_replace : Option (String × symbolic_string)
  noedit_first   : fc_operand

/-- Lem: fc_noedit_default_operands -/
def fc_noedit_default_operands : fc_noedit_operands :=
  { noedit_replace := none
  , noedit_first   := .FC_Previous 1
  }

/-- Lem: val fc_noedit_operand : symbolic_string -> fc_noedit_operands -> either string fc_noedit_operands -/
def fc_noedit_operand (arg : symbolic_string) (ops : fc_noedit_operands)
    : Except String fc_noedit_operands :=
  match try_split_assign arg with
  | (_, none) => -- no '=', must be a real operand
    match fc_Operand arg with
    | .error err => .error err
    | .ok op     => .ok { ops with noedit_first := op }
  | (s_old, some s_new) => .ok { ops with noedit_replace := some (s_old, s_new) }

/-- Lem: fc_noedit_operands -/
def fc_Noedit_Operands (argv : fields) : Except String fc_noedit_operands :=
  match argv with
  | [] => .ok fc_noedit_default_operands
  | [arg] => fc_noedit_operand arg fc_noedit_default_operands
  | [arg1, arg2] =>
    match fc_noedit_operand arg1 fc_noedit_default_operands with
    | .error err => .error err
    | .ok ops    => fc_noedit_operand arg2 ops
  | _ => .error ("expected [old=new] [first], got '" ++ string_of_fields argv ++ "'")

/-- Lem: fc_editlist_operands type -/
structure fc_editlist_operands where
  editlist_first : fc_operand
  editlist_last  : fc_operand
deriving Repr, DecidableEq

/-- Lem: fc_editlist_operands list_mode argv -/
def fc_Editlist_Operands (list_mode : Bool) (argv : fields)
    : Except String fc_editlist_operands :=
  match argv with
  | [] =>
    let first : fc_operand := .FC_Previous 1
    let last  : fc_operand := if list_mode then .FC_Previous 16 else .FC_Previous 1
    .ok { editlist_first := first, editlist_last := last }
  | [first_arg] =>
    match fc_Operand first_arg with
    | .error err => .error err
    | .ok first  =>
      let last := if list_mode then .FC_Previous 1 else first
      .ok { editlist_first := first, editlist_last := last }
  | [first_arg, last_arg] =>
    match fc_Operand first_arg with
    | .error err => .error err
    | .ok first  =>
      match fc_Operand last_arg with
      | .error err => .error err
      | .ok last   => .ok { editlist_first := first, editlist_last := last }
  | _ => .error ("expected [first [last]], got '" ++ string_of_fields argv)

private def isPrefixOfCharList : List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then isPrefixOfCharList as bs else false

/-- Lem: val fc_matches : string -> stmt -> bool -/
def fc_matches (s : String) (c : stmt) : Bool :=
  isPrefixOfCharList (toCharList s) (toCharList (string_of_stmt c))

/-
When a range of commands is used, it shall not be an error to specify first or last values that are not in the history list; fc shall substitute the value representing the oldest or newest command in the list, as appropriate.
returns an INDEX into the history along with the entry
-/
/-- Lem: val fc_find_matching_entry : fc_operand -> history -> maybe (nat * (nat * stmt) -/
def fc_find_matching_entry (op : fc_operand) (hist : history)
    : Option (Nat × (Nat × stmt)) :=
  let incr_index : Option (Nat × (Nat × stmt)) → Option (Nat × (Nat × stmt)) :=
    Option.map (fun (idx, entry) => (idx + 1, entry))
  match op, hist with
  | _, [] => none
  | .FC_CmdNumber n, (n', c) :: hist' =>
    if n = n' then
      some (0, (n', c))
    else
      incr_index (fc_find_matching_entry op hist')
  | .FC_Previous 0, (n, c) :: _ => some (0, (n, c))
  | .FC_Previous (Nat.succ k), _ :: hist' =>
    incr_index (fc_find_matching_entry (.FC_Previous k) hist')
  | .FC_Matching s, (n, c) :: hist' =>
    if fc_matches s c then
      some (0, (n, c))
    else
      incr_index (fc_find_matching_entry op hist')

/-- Lem: val fc_find_matching_index : fc_operand -> history -> maybe nat -/
def fc_find_matching_index (op : fc_operand) (hist : history) : Option Nat :=
  Option.map Prod.fst (fc_find_matching_entry op hist)

/-
"When commands are edited (when the -l option is not specified),
     the resulting lines shall be entered at the end of the history
     list and then re-executed by sh. The fc command that caused the
     editing shall not be entered into the history list." *)
TODO 2019-07-10 yash prints out the fc command on fc -l; other shells don't *)
"When a range of commands is used, it shall not be an error to
     specify first or last values that are not in the history list; fc
     shall substitute the value representing the oldest or newest
     command in the list, as appropriate." *)
TODO 2019-07-10 this may not _exactly_ right, since the range may
     not have been specified by the user explicitly. what's the right behavior?

     fc -16 -1 is behaving funny in the current regime.
-/
/-- Lem: fc_editlist_commands -/
def fc_editlist_commands (opts : Set.Set fc_opt) (ops : fc_editlist_operands) (hist : history)
    : history :=
  let first_idx : Nat := (fc_find_matching_index ops.editlist_first hist).getD 0
  let default_last : Nat :=
    match hist with
    | [] => 0
    | _  => hist.length - 1
  -- If first represents a newer command than last, the commands shall
  -- be listed or edited in reverse sequence.
  let last_idx : Nat := (fc_find_matching_index ops.editlist_last hist).getD default_last
  let (drop_amt, take_amt, should_reverse) : Nat × Nat × Bool :=
    -- NB we don't subtract 1 from the drop amount to avoid listing the fc command itself
    if last_idx < first_idx then
      (last_idx, (first_idx - last_idx) + 1, true)
    else
      (first_idx, (last_idx - first_idx) + 1, false)
  let cmds : history := (hist.drop drop_amt).take take_amt
  -- cmds is in HISTORY order, i.e., recent to less recent, i.e., ALREADY reversed
  if should_reverse || Set.Set.member .FC_Reverse opts then
    cmds
  else
    cmds.reverse

/-- Lem: fc_editlist_args -/
def fc_editlist_args [OS α]
    (s0 : os_state α) (fc_opts : Set.Set fc_opt) (fc_mode : fc_mode) (argv : fields)
    : Except String history :=
  let list_mode : Bool :=
    match fc_mode with
    | .FC_List => true
    | _        => false
  match fc_Editlist_Operands list_mode argv with
  | .error err => .error err
  | .ok ops =>
    let cmds := fc_editlist_commands fc_opts ops s0.sh.history
    if cmds.isEmpty then
      .error "history specification out of range"
    else
      .ok cmds

/-- Lem: builtin_fc -/
def builtin_fc [OS α]
    (s0 : os_state α) (argv : fields) (_env : env) : builtin_ret_stmt α :=
  match fc_default_mode s0 with
  | .error e => .error (s0, e)
  | .ok mode =>
    match fc_options_loop argv mode Set.Set.empty with
    | .error err => .error (s0, err)
    | .ok (argv', fc_mode, fc_opts) =>
      let s1 := s0
      match fc_mode with
      | .FC_NoEdit => -- fc -s [old=new] [first]
        match fc_Noedit_Operands argv' with
        | .error err => .error (s1, err)
        | .ok ops =>
          match fc_find_matching_entry ops.noedit_first s1.sh.history with
          | none => .error (s1, "history specification out of range")
          | some (_idx, (_n, c)) =>
            match ops.noedit_replace with
            | none => .ok (add_to_history c s1, c)
            | some (s_old, ss_new) =>
              let (s2, _concretized, s_new) := concretize s1 ss_new
              let s_orig := string_of_stmt c
              let s_replaced := replace_string s_old s_new s_orig
              let c' := command_eval (symbolic_string_of_string s_replaced)
              .ok (add_to_history c' s2, c')
      | .FC_List => -- fc -l [-nr] [first [last]]
        match fc_editlist_args s1 fc_opts fc_mode argv' with
        | .error err => .error (s1, err)
        | .ok cmds =>
          let show_cmd : (Nat × stmt) → String
              | (n, c) =>
                (if Smoosh.Set.Set.member .FC_NoNumber fc_opts then
                  ""
                else
                  stringFromNat n ++ "\t") ++
                  string_of_stmt c ++ "\n"
              let out := String.intercalate "" (cmds.map show_cmd)
              let s2 := safe_write_stdout "fc" out s1
              .ok (s2, .Done)
      | .FC_Edit _editor => -- fc [-r] [-e editor] [first [last]]
        match fc_editlist_args s1 fc_opts fc_mode argv' with
        | .error err => .error (s1, err)
        | .ok _cmds  => .error (s1, "editor usage is unimplemented")

/-- POSIX user control (XSI): `ulimit` is currently unimplemented.
 let builtin_ulimit = builtin_unimplemented (* XSI *) -/
def builtin_ulimit [OS α] :
    os_state α → fields → env → builtin_ret_stmt α :=
  fun s0 argv env =>
    drop_restore (builtin_unimplemented s0 argv env)

/-- Lem: val builtins :
  forall 'a. OS 'a =>
    Map.map string
      (os_state 'a -> fields (* argv *) -> env ->
       either (os_state 'a * string) (os_state 'a * stmt)) -/
def builtins [OS α] :
    Map.map String (os_state α → fields → env → builtin_ret_stmt α) :=
  Map.fromList
    [ ("[",       builtin_bracket)
    , ("alias",   builtin_alias)
    , ("bg",      builtin_bg)
    , ("cd",      builtin_cd)
    , ("command", builtin_command)
    , ("echo",    builtin_echo)
    , ("false",   builtin_false)
    , ("fc",      builtin_fc)
    , ("fg",      builtin_fg)
    , ("getopts", builtin_getopts)
    , ("hash",    builtin_hash)
    , ("help",    builtin_help)
    , ("history", builtin_history)
    , ("jobs",    builtin_jobs)
    , ("kill",    builtin_kill)
    -- , ("newgrp", builtin_newgrp)
    , ("printf",  builtin_printf)
    , ("pwd",     builtin_pwd)
    , ("read",    builtin_read)
    , ("test",    builtin_test)
    , ("true",    builtin_true)
    , ("type",    builtin_type)
    , ("ulimit",  builtin_ulimit)
    , ("umask",   builtin_umask)
    , ("unalias", builtin_unalias)
    , ("wait",    builtin_wait)
    ]

/-- Lem: run_command -/
def run_command [OS α]
    (s0 : os_state α)
    (opts : command_opts)
    (checked : checking_mode)
    (prog_name : symbolic_string)
    (argv : fields)
    (env : env)
    : Except (os_state α × String) (os_state α × stmt × Bool) :=
  match try_concrete prog_name with
  | none => .error (s0, "can't run symbolic command")
  | some prog =>
      -- 1a. If the command name matches the name of a special built-in utility, that special built-in utility shall be invoked.
      match Map.lookup prog special_builtins with
      | some fn => fn s0 argv env
      | none =>
        -- 1b. b. If the command name matches the name of a utility
        -- listed in the following table, the results are unspecified.
        let s1 :=
          if is_unspecified_utility prog then
            log_trace .Trace_unspec (prog ++ "is unspecified") s0
          else
            s0
          /-
          1c. If the command name matches the name of a function
             known to this shell, the function shall be invoked as
             described in Function Definition Command. If the
             implementation has provided a standard utility in the
             form of a function, it shall not be recognized at this
             point. It shall be invoked in conjunction with the path
             search in step 1e.
          -/
          match (opts.force_simple_command, lookup_function prog s1) with
          | (false, some body) =>
            let s2 := push_locals s1 env
            let s3 := set_function_params 0 argv s2
            .ok (s3,
                 .Call s1.sh.loop_nest (get_function_params s1) prog body body,
                 true)
          | _ =>
            /-
            1d. If the command name matches the name [XSI] [Option
                Start] of the type or ulimit utility, or [Option End]
                of a utility listed in the following table, that
                utility shall be invoked.
            -/
            match Map.lookup prog (builtins (α := α)) with
            | some fn =>
              let s2 := push_locals s1 env
              -- force a restore
              match fn s2 argv env with
              | .error (s2', err) =>
                match pop_locals s2' with
                | .error msg =>
                  .error (s2', msg)
                | .ok (s3, _locals) =>
                  .error (s3, err)
              | .ok (s2', st) =>
                let restore :=
                  match st with
                  | .CommandReady _env cmd [] [] _opts =>
                    decide (string_of_symbolic_string cmd ≠ "exec")
                  | _ => true
                match pop_locals s2' with
                | .error msg =>
                  .error (s2', msg)
                | .ok (s3, _locals) =>
                  .ok (s3, st, restore)
            | none =>
              match check_execve none s1 prog with
              | (s2, none) =>
                -- failed... and emitted an error message and set the ec
                .ok (s2, .Done, true)
              | (s2, some executable) =>
                let _ := symbolic_string_of_string executable
                match exported_set_vars s2 with
                | .error msg => .error (s2, msg)
                | .ok exported => -- use env to override exports---impl as Pmap.(union)
                  let cmd := symbolic_string_of_string executable
                  let exec_env := Map.union exported env
                  let exec := .Exec cmd prog_name argv exec_env .TryBinSh
                  if opts.should_fork then
                    let (s3, pid) := fork_and_subshell s2 exec .FG none true
                    let stmt0 := .CommandExpRedirs [] (prog_name :: argv) ([], none, []) default_cmd_opts
                    let (s4, _jobid) := add_job s3 [(pid, stmt0)] pid stmt0 .FG .JobRunning
                    .ok (s4, .Wait pid checked none .WaitInternal, true)
                  else .ok (s2, exec, true)
