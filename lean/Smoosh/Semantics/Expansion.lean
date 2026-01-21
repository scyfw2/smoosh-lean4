import Smoosh.Smoosh
import Smoosh.Fields
import Smoosh.Arith
import Smoosh.Pattern
import Smoosh.Command.All
import Smoosh.Semantics.SharedDecl
import Smoosh.Semantics.TrapManage
import Smoosh.OsSymbolic.All

open Smoosh
universe u
namespace Smoosh

abbrev exp_result (α : Type u) :=
  Except (expansion_step × os_state α × expanded_words)
         (expansion_step × os_state α × expanded_words × words)

-- (*
--  * Stage 1 Expansion: Word expansion
--  *)

/-- Lem: expand_param : os_state -> splitting_mode -> quoting_mode -> string -> format
    -> os_state * expanded_words * words
-/
def expand_param {α : Type u} [OS α]
    (s0 : os_state α) (split : splitting_mode) (q : quoting_mode)
    (str : String) (f : format) :
    Except String (os_state α × expanded_words × words) :=
  let tmp : Except String (os_state α × Option fields) :=
    if str = "*" && (q = .Quoted || !(should_split split)) then
      match lookup_string_param (α := α) s0 "IFS" with
      | .error e => .error e
      | .ok .none =>
          let sep : List symbolic_char := [symbolic_char.C ' ']
          let fs  : fields :=
            [symbolic_string_of_fields_sep sep (get_function_params s0)]
          .ok (s0, (some fs : Option fields))
      | .ok (.some ss) =>
          let (s1, _, ifs) := concretize s0 ss
          match toCharList ifs with
          | [] =>
              let sep : List symbolic_char := []
              let fs  : fields :=
                [symbolic_string_of_fields_sep sep (get_function_params s1)]
              .ok (s1, (some fs : Option fields))
          | c :: _ =>
              let sep : List symbolic_char := [symbolic_char.C c]
              let fs  : fields :=
                [symbolic_string_of_fields_sep sep (get_function_params s1)]
              .ok (s1, (some fs : Option fields))
    else
      match lookup_param (α := α) s0 str with
      | .error e => .error e
      | .ok v    => .ok (s0, (v : Option fields))
  match tmp with
  | .error e => .error e
  | .ok (s1, value) =>
      let cstr (s : String)  : (os_state α × expanded_words × words) := (s1, [.ExpS s], [])
      let ewfs (fs : fields) : (os_state α × expanded_words × words) := (s1, expanded_words_of_fields fs, [])
      let wrds (w : words)   : (os_state α × expanded_words × words) := (s1, [], w)
      let null  : (os_state α × expanded_words × words) := (s1, [], [])
      let ctrl (k : control) : (os_state α × expanded_words × words) := (s1, [], [.K k])
      let unst (o : os_state α × expanded_words × words) :=
        if !(List.elem str ["@", "*"]) && Set.Set.member .Sh_nounset s0.sh.opts then
          ctrl (.LError str [.ExpS "parameter not set"] [])
        else
          o
      let out : (os_state α × expanded_words × words) :=
        match value, f with
        -- NORMAL
        | .none,    .Normal      => unst null
        | .some fs, .Normal      => ewfs fs
        -- DEFAULT
        | .none,    .Default w   => wrds w
        | .some fs, .Default _   => ewfs fs
        | .none,    .NDefault w  => wrds w
        | .some fs, .NDefault w  =>
            match null_fields fs with
            | .none =>
                let s2 :=
                  log_trace .Trace_symbolic
                    "Unsoundly treating symbolic fields as non-empty" s1
                (s2, expanded_words_of_fields fs, [])
            | .some true  => wrds w
            | .some false => ewfs fs
        -- ASSIGN
        | .none,    .Assign w    => ctrl (.LAssign str [] w)
        | .some fs, .Assign _    => ewfs fs
        | .none,    .NAssign w   => ctrl (.LAssign str [] w)
        | .some fs, .NAssign w   =>
            match null_fields fs with
            | .none       => ewfs fs
            | .some true  => ctrl (.LAssign str [] w)
            | .some false => ewfs fs
        -- ERROR
        | .none,    .Error w     => ctrl (.LError str [] w)
        | .some fs, .Error _     => ewfs fs
        | .none,    .NError w    => ctrl (.LError str [] w)
        | .some fs, .NError w    =>
            match null_fields fs with
            | .none =>
                let s2 :=
                  log_trace .Trace_symbolic
                    "Unsoundly treating symbolic fields as non-empty" s1
                (s2, expanded_words_of_fields fs, [])
            | .some true  => ctrl (.LError str [] w)
            | .some false => ewfs fs
        -- LENGTH
        | .none,    .Length      => unst (cstr "0")
        | .some fs, .Length      =>
            match try_concrete_fields fs with
            | .none      => cstr "0"
            | .some strs => cstr (toString (stringLength strs))
        -- ALT
        | .none,    .Alt _       => null
        | .some _,  .Alt w       => wrds w
        | .none,    .NAlt _      => null
        | .some fs, .NAlt w      =>
            match null_fields fs with
            | .none =>
                let s2 :=
                  log_trace .Trace_symbolic
                    "Unsoundly treating symbolic fields as non-empty" s1
                (s2, [], w)
            | .some true  => null
            | .some false => wrds w
        -- SUBSTRINGS
        | .none,    .Substring _ _ _ => unst (cstr "")
        | .some fs, .Substring s m w => ctrl (.LMatch fs s m [] w)
      .ok out


def dest_init {α : Type u} : List α → Option (List α × α)
  | []      => none
  | x :: xs =>
    match dest_init xs with
    | some (init, last) => some (x :: init, last)
    | none              => some ([], x)

abbrev expand_err (α : Type u) :=
  expansion_step × os_state α × expanded_words

abbrev expand_ok (α : Type u) :=
  expansion_step × os_state α × expanded_words × words

abbrev expand_ret (α : Type u) :=
  Sum (expand_err α) (expand_ok α)

namespace Expand

@[inline] def retErr {α : Type u} (e : expand_err α) : Except String (expand_ret α) :=
  .ok (.inl e)

@[inline] def retOk {α : Type u} (x : expand_ok α) : Except String (expand_ret α) :=
  .ok (.inr x)

mutual

  partial def step_eval_default {α : Type u} [OS α]
      (s0 : os_state α) (checked : checking_mode) (st : stmt) :
      evaluation_step × os_state α × stmt :=
    match step_eval s0 checked st with
    | .ok t => t
    | .error msg =>
        ( .XSSimple ("internal step_eval error: " ++ msg)
        , fail_with msg s0
        , if is_interactive s0 then .Done else .Exit
        )

  partial def expand_control {α : Type u} [OS α]
      (s0 : os_state α) (split : splitting_mode) (q : quoting_mode) (k : control) :
      Except String (expand_ret α) :=
    match k with
    | .Tilde prefixs =>
        if prefixs = "" then
          -- lookup_concrete_param : Except String (Option String)
          match lookup_concrete_param s0 "HOME" with
          | .error msg =>
              -- failwith/内部错误：向外传播
              .error msg
          | .ok none =>
              let s1 :=
                log_trace .Trace_unspec
                  "unset HOME for ~ (unspec per 2.6.1)" s0
              let dir := .ExpS "~"
              retOk (.ESTilde "", s1, [dir], [])
          | .ok (some dir) =>
              let dirEW := .DQuo (symbolic_string_of_string dir)
              retOk (.ESTilde "", s0, [dirEW], [])
        else
          match getpwnam s0 prefixs with
          | none =>
              let s1 :=
                log_trace .Trace_unspec
                  ("defaulting to dash behavior for failed getpwnam " ++
                   "(unspec per 2.6.1)")
                  s0
              retOk (.ESTilde "", s1, [.ExpS ("~" ++ prefixs)], [])
          | some path =>
              retOk (.ESTilde "", s0, [.ExpS path], [])

    | .Param s f =>
        if s = "@" && q = .Quoted then
          -- 这一大段逻辑不涉及你新给的 Except 函数签名变化
          -- （里面调用 expand_words：见下方 expand_words 已改成 Except String (expand_ret α)）
          let param_vars := get_function_params s0

          let unspec : Bool :=
            match f with
            | .Length          => true
            | .Substring _ _ _ => true
            | _               => false

          let s1 :=
            if unspec then
              log_trace .Trace_unspec
                ("Unspecified parameter format: " ++ string_of_control (.Param s f))
                s0
            else s0

          let expand_more (w : words) : Except String (expand_ret α) :=
            expand_words s1 split q .GeneratedString ([], w)

          let build_at (v : fields) : Except String (expand_ret α) :=
            retOk (.ESParam "expanding @", s1, [.At v], [])

          match f with
          | .Default _  => build_at param_vars
          | .NDefault w => if List.isEmpty param_vars then expand_more w else build_at param_vars
          | .Assign _   => build_at param_vars
          | .NAssign _  =>
              if List.isEmpty param_vars then
                expand_more [.K (.LError "@" [.ExpS "bad variable name"] [])]
              else
                build_at param_vars
          | .Error _    => build_at param_vars
          | .NError w   =>
              if List.isEmpty param_vars then
                expand_more [.K (.LError "@" [] w)]
              else
                build_at param_vars
          | .Length     => expand_more [.K (.Param "*" .Length)]
          | .Alt w      => expand_more w
          | .NAlt w     => if List.isEmpty param_vars then build_at param_vars else expand_more w

          | .Substring .Prefix mode w =>
              match param_vars with
              | v1 :: vars =>
                  let v1' := .K (.Quote [] [.K (.LMatch [v1] .Prefix mode [] w)])
                  expand_more (v1' :: words_of_fields vars)
              | _ =>
                  build_at []

          | .Substring .Suffix mode w =>
              match dest_init param_vars with
              | some (vars', vn) =>
                  let vn' := .K (.Quote [] [.K (.LMatch [vn] .Suffix mode [] w)])
                  expand_more (words_of_fields vars' ++ [vn'])
              | none =>
                  build_at []

          | _ => build_at param_vars

        else
          -- expand_param : Except String (os_state × expanded_words × words)
          match expand_param s0 split q s f with
          | .error msg =>
              -- 这里没有 step 信息，按“failwith/内部错误”向外抛
              .error msg
          | .ok (s1, ew, w) =>
              expand_words s1 split q .GeneratedString (ew, w)

    | .LAssign s f [] =>
        -- concat_expanded 若你也是 Except String symbolic_string（常见做法）
        match concat_expanded f with
        | .error msg =>
            .error msg
        | .ok sym =>
            -- set_param : Except String (os_state α)
            -- 这里的错误在 Lem 里是“语义错误”（bad/readonly），所以我们把 Except.error 映射成 Sum.inl
            match set_param s sym s0 with
            | .error err =>
                retErr (.ESParam "bad or readonly variable", s0, (.ExpS err) :: f)
            | .ok s1 =>
                retOk (.ESParam "finished assignment", s1, f, [])

    | .LAssign s f w =>
        match expand_words s0 .NoSplit q .GeneratedString ([], w) with
        | .error msg =>
            .error msg
        | .ok (.inl err) =>
            retErr err
        | .ok (.inr (step, s1, f1, w1)) =>
            retOk
              ( .ESNested (.ESParam "assignment") step
              , s1
              , []
              , [.K (.LAssign s (f ++ f1) w1)]
              )

    | .LMatch str side mode f [] =>
        let sympat := symbolic_string_of_expanded_words true f
        let symstr := symbolic_string_of_fields str
        let (s1, _concretized, pat) := concretize s0 sympat
        let matched := try_match_substring s1.sh.locale side mode pat symstr
        retOk (.ESParam "finished match", s1, [], words_of_symbolic_string matched)

    | .LMatch s side mode f w =>
        match expand_words s0 .NoSplit .Unquoted .GeneratedString ([], w) with
        | .error msg =>
            .error msg
        | .ok (.inl err) =>
            retErr err
        | .ok (.inr (step, s1, f1, w1)) =>
            retOk
              ( .ESNested (.ESParam "match") step
              , s1
              , []
              , [.K (.LMatch s side mode (f ++ f1) w1)]
              )

    | .LError str f [] =>
        retErr (.ESParam "raising requested error", s0, (.ExpS (str ++ ": ")) :: f)

    | .LError str f w =>
        match expand_words s0 .NoSplit q .GeneratedString ([], w) with
        | .error msg =>
            .error msg
        | .ok (.inl err) =>
            retErr err
        | .ok (.inr (step, s1, f1, w1)) =>
            retOk
              ( .ESNested (.ESParam "error") step
              , s1
              , []
              , [.K (.LError str (f ++ f1) w1)]
              )


    | .Backtick c =>
        -- pipe : Except String (os_state × fd × fd)
        -- Lem 里 pipe 失败是语义错误（Left），所以这里把 Except.error 映射为 Sum.inl
        match pipe s0 with
        | .error err =>
            retErr (.ESCommand ("failed to set up pipe: " ++ err), s0, [])
        | .ok (s1, fd_read, fd_write) =>
            let redirs :=
              [ .ERDup .ToFD .CloseOrig STDOUT (some fd_write)
              , .ERDup .ToFD .CloseOrig fd_read none
              ]
            -- do_redirs 的类型你没给，我按你原来 Lem 结构保留：
            match do_redirs s1 redirs with
            | (s2, (.error _)) =>
                retErr (.ESCommand "failed to set up subshell", s2, [])
            | (s2, (.ok saved_fds)) =>
                let (s3, pid) :=
                  fork_and_subshell s2 c .FG none false
                let s4 := restore_fds s3 saved_fds
                let s5 := close_fd s4 fd_write
                retOk (.ESCommand "initializing subshell", s5, [], [.K (.LBacktick c pid fd_read)])

    | .LBacktick corig pid fd_read =>
        -- read_all_fd : os_state × Except evaluation_step (Option String)
        -- read_all_fd 需要 step_fun α（纯三元组），用 wrapper 把 Except 错误降级掉
        let step_eval_total : step_fun α :=
          fun os chk st =>
            match step_eval (α := α) os chk st with
            | .ok t => t
            | .error msg =>
              ( .XSSimple ("internal step_eval error: " ++ msg)
              , fail_with msg os
              , if is_interactive os then .Done else .Exit
              )

        let (s1, r) := read_all_fd step_eval_total s0 fd_read
        match r with
        | .error step =>
            retOk
              ( .ESEval (.ESCommand ("process with pid " ++ stringFromNat pid ++ " stepped")) step
              , s1
              , []
              , [.K (.LBacktick corig pid fd_read)]
              )
        | .ok none =>
            retErr (.ESCommand "broken pipe", s1, [])
        | .ok (some s) =>
            let s2 := close_fd s1 fd_read
            let s_trimmed := trimr_newlines s
            retOk
              ( .ESCommand "command exited successfully, waiting"
              , s2
              , []
              , [.K (.LBacktickWait corig pid s_trimmed)]
              )

    | .LBacktickWait corig pid s =>
        -- wait_for_pid：语义分支 ⇒ Sum
        let step_eval_total : step_fun α :=
          fun os chk st =>
            match step_eval (α := α) os chk st with
            | .ok t => t
            | .error msg =>
              ( .XSSimple ("internal step_eval error: " ++ msg)
              , fail_with msg os
              , if is_interactive os then .Done else .Exit
              )

        match wait_for_pid step_eval_total s0 pid with
        | (s1, none) =>
            retOk
              ( .ESCommand "command process vanished, leaving exit code unset"
              , s1
              , [.ExpS s]
              , []
              )

        | (s1, some (.error step)) =>
            retOk
              ( .ESEval (.ESCommand "command process stepped") step
              , s1
              , []
              , [.K (.LBacktickWait corig pid s)]
              )

        | (s1, some (.ok code)) =>
            retOk
              ( .ESCommand "command process terminated"
              , exit_with code s1
              , [.ExpS s]
              , []
              )
    | .Arith f [] =>
        -- concat_expanded：可能 failwith ⇒ Except
        match concat_expanded f with
        | .error msg =>
            .error msg
        | .ok sym =>
            -- arith64：语义失败 ⇒ Sum
            match Num.arith64 s0 sym with
            | .inr (s1, result) =>
                retOk (.ESArith "computed arithmetic result", s1, expanded_words_of_fields result, [])
            | .inl e =>
                retErr (.ESArith "arithmetic error", s0, [.ExpS e])

    | .Arith f w =>
        match expand_words s0 split q .GeneratedString ([], w) with
        | .error msg =>
            .error msg
        | .ok (.inl err) =>
            retErr err
        | .ok (.inr (step, s1, f1, w1)) =>
            retOk
              ( .ESNested (.ESArith "before arithmetic parsing") step
              , s1
              , []
              , [.K (.Arith (f ++ f1) w1)]
              )

    | .Quote f [] =>
        -- collapse_quoted 如果你把它做成 failwith(Except)，就像下面这样接；否则直接 okOk
        match collapse_quoted f with
        | .error msg => .error msg
        | .ok f'     => retOk (.ESQuote "finished quote expansion", s0, f', [])

    | .Quote f w =>
        match expand_words s0 split .Quoted .GeneratedString ([], w) with
        | .error msg =>
            .error msg
        | .ok (.inl err) =>
            retErr err
        | .ok (.inr (step, s1, [], w1)) =>
            -- null-fields special-case
            retOk (step, s1, [], [.K (.Quote (f ++ [.DQuo []]) w1)])
        | .ok (.inr (step, s1, f1, w1)) =>
            retOk (step, s1, [], [.K (.Quote (f ++ f1) w1)])

    | .Escape c =>
        retOk (.ESEscape "", s0, [.DQuo [.C c]], [])

  partial def expand_words {α : Type u} [OS α]
      (s0 : os_state α) (split : splitting_mode) (q : quoting_mode) (sm : string_mode)
      (fw : expanded_words × words) :
      Except String (expand_ret α) :=
    let (f, w) := fw
    match w with
    | [] =>
        retOk (.ESStep "done", s0, f, w)

    | .F :: ws =>
        retOk (.ESStep "user field separator", s0, f ++ [.UsrF], ws)

    | .S "" :: ws =>
        expand_words s0 split q sm (f, ws)

    | .S s :: ws =>
        let f1 :=
          match (q, sm) with
          | (.Quoted,   _)               => [.DQuo (symbolic_string_of_string s)]
          | (.Unquoted, .UserString)      => [.UsrS s]
          | (.Unquoted, .GeneratedString) => [.ExpS s]
        retOk (.ESStep "plain string", s0, f ++ f1, ws)

    | .K k :: ws =>
        match expand_control s0 split q k with
        | .error msg =>
            .error msg
        | .ok (.inl err) =>
            retErr err
        | .ok (.inr (step, s1, f1, w1)) =>
            retOk (step, s1, f ++ f1, w1 ++ ws)

    | .ESym c :: ws =>
        retOk (.ESStep "skipping symbolic result", s0, f ++ [.EWSym c], ws)

  partial def step_expansion {α : Type u} [OS α] :
    (os_state α × expansion_state) → Except String (expansion_step × os_state α × expansion_state)
  | (os0, st) =>
    match st with
    | .ExpStart opts w0 =>
        match expand_words os0 opts.splitting .Unquoted .UserString ([], w0) with
        | .error msg =>
            .error msg
        | .ok (.inr (step, os1, f1, w1)) =>
            .ok (step, os1, .ExpExpand opts f1 w1)
        | .ok (.inl (step, os1, f1)) =>
            .ok (step, os1, .ExpError (fields_of_expanded_words f1))

    | .ExpExpand opts f0 [] =>
        if should_split opts.splitting then
          .ok (.ESSplit "starting field splitting", os0, .ExpSplit opts f0)
        else
          .ok (.ESSplit "skipping field splitting", os0,
               .ExpPath opts (skip_field_splitting f0))

    | .ExpExpand opts f0 w0 =>
        match expand_words os0 opts.splitting .Unquoted .UserString (f0, w0) with
        | .error msg =>
            .error msg
        | .ok (.inr (step, os1, f1, w1)) =>
            .ok (step, os1, .ExpExpand opts f1 w1)
        | .ok (.inl (step, os1, f1)) =>
            .ok (step, os1, .ExpError (fields_of_expanded_words f1))

    | .ExpSplit opts f0 =>
        -- field_splitting 现在是 Except String intermediate_fields
        match field_splitting os0 f0 with
        | .error msg =>
            -- 属于 expansion error：写入 ExpError，而不是向外抛 failwith
            .ok (.ESSplit "field splitting error", os0,
                 .ExpError [symbolic_string_of_string msg])
        | .ok ifs =>
            .ok (.ESSplit "", os0, .ExpPath opts ifs)

    | .ExpPath opts ifs0 =>
        if Set.Set.member .Sh_noglob os0.sh.opts || opts.globbing = false then
          .ok (.ESPath "skipping pathname expansion (set -f/assignment/etc.)",
               os0,
               .ExpQuote opts (unescape_intermediate_fields ifs0))
        else
          .ok (.ESPath "", os0, .ExpQuote opts (pathname_expansion os0 ifs0))

    | .ExpQuote _opts ifs0 =>
        -- quote_removal 现在是 Except String fields
        match quote_removal ifs0 with
        | .error msg =>
            .ok (.ESQuote "quote removal error", os0,
                 .ExpError [symbolic_string_of_string msg])
        | .ok f =>
            .ok (.ESQuote "", os0, .ExpDone f)

    | .ExpError _ =>
        .ok (.ESStep "done in error state", os0, st)

    | .ExpDone _ =>
        .ok (.ESStep "done in success state", os0, st)

  partial def step_redir {α : Type u} [OS α]
    (os0 : os_state α) (er : expanding_redir) : redir_exp_result (os_state α) :=
  let exp_state := get_expanding_redir_state er
  match step_expansion (os0, exp_state) with
  | .error msg =>
      -- step_expansion 的 Except.error = failwith/内部错误；这里没有 Except 可抛，降级成 redir 扩展错误
      .REError [symbolic_string_of_string msg]
  | .ok (step, os1, st1) =>
      match st1 with
      | .ExpError err =>
          .REError err

      | .ExpDone f =>
          match try_expand_redir er f with
          | .error err => .REError [symbolic_string_of_string err]
          | .ok er' => .REDone os1 er'

      | .ExpPath opts ifs =>
          let (msg, es') :=
            if is_interactive os1 && !is_heredoc er && opts.globbing then
              let expanded := pathname_expansion os1 ifs
              if expanded.length = 1 then
                ("performed pathname expansion in interactive shell",
                 .ExpQuote opts expanded)
              else
                ("skipped pathname expansion in interactive shell [produced " ++
                   stringFromNat (expanded.length) ++ " words]",
                 .ExpQuote opts (unescape_intermediate_fields ifs))
            else if is_heredoc er then
              ("stopping expansion for heredoc",
               .ExpQuote opts (unescape_heredoc ifs))
            else
              ("skipped pathname expansion",
               .ExpQuote opts (unescape_intermediate_fields ifs))
          .REStep (.ESPath msg) os1 (set_expanding_redir_state es' er)

      | _ =>
          .REStep step os1 (set_expanding_redir_state st1 er)

  partial def step_redir_state {α : Type u} [OS α]
      (os0 : os_state α) (rs : redir_state) :
      os_state α × String × Option (redir_state × Option expansion_step) :=
    match rs with
    | (_ers, none, []) =>
        (os0, "done expanding redirs", some (rs, none))

    | (ers, none, r :: redirs) =>
        let opts := { splitting := .NoSplit, globbing := is_interactive os0 }
        let (msg, ers', exp_state) :=
          match r with
          | .RFile ty src w =>
              ("expanding file redirect", ers, some (.XRFile ty src (.ExpStart opts w)))
          | .RDup ty src w =>
              ("expanding dup redirect", ers, some (.XRDup ty src (.ExpStart opts w)))
          | .RHeredoc .XHere src w =>
              ("expanding unquoted heredoc", ers, some (.XRHeredoc .XHere src (.ExpStart opts w)))
          | .RHeredoc .Here src w =>
              ("not expanding quoted heredoc",
               ers ++ [.ERHeredoc .Here src (symbolic_string_of_string (string_of_words w))],
               none)
        (os0, msg, some ((ers', exp_state, redirs), none))

    | (ers, some er, redirs) =>
        match step_redir os0 er with
        | .REError err =>
            let msg := string_of_symbolic_string (symbolic_string_of_fields err)
            (os0, msg, none)

        | .REDone os1 er' =>
            (os1, "expanded redirect", some ((ers ++ [er'], none, redirs), none))

        | .REStep step os1 er' =>
            (os1, "redirection expansion step", some ((ers, some er', redirs), some step))

  partial def step_eval {α : Type u} [OS α]
      (s0 : os_state α) (checked : checking_mode) (st : stmt) :
      Except String (evaluation_step × os_state α × stmt) :=
  match st with
  /- COMMAND **************************************************************** -/
  | .Command assigns ws redirs opts => .ok
      ( .XSSimple "expand command args"
      , s0
      , .CommandExpArgs
          assigns
          (.ExpStart { splitting := .Split, globbing := true } ws)
          redirs
          opts
      )

  | .CommandExpArgs assigns exp_state redirs opts =>
      match step_expansion (s0, exp_state) with
      | .error msg =>
        match check_traps
            ( evaluation_step.XSSimple ("internal expansion error: " ++ msg)
            , fail_with msg s0
            , if is_interactive s0 then .Done else .Exit
            )
        with
        | .ok t      => .ok t
        | .error e   => .ok
            ( evaluation_step.XSSimple ("internal check_traps error: " ++ e)
            , fail_with e s0
            , if is_interactive s0 then .Done else .Exit
            )
      | .ok (step, s1, st1) =>
          match st1 with
          | .ExpError err =>
            match expansion_error true s1 (.XSSimple "arg expansion") step err with
            | .ok t => .ok t
            | .error msg => .ok
                ( .XSSimple ("internal expansion_error: " ++ msg)
                , fail_with msg s1
                , if is_interactive s1 then .Done else .Exit
                )
          | .ExpDone f =>
              let msg :=
                toString (f.length) ++ " " ++
                (if f.length = 1 then "argument" else "arguments") ++
                " fully expanded (including command)"
              .ok ( .XSExpand (.XSSimple msg) step
              , s1
              , .CommandExpRedirs assigns f ([], none, redirs) opts
              )
          | _ => .ok
              ( .XSExpand (.XSSimple "argument expansion step") step
              , s1
              , .CommandExpArgs assigns st1 redirs opts
              )


  -- (* done expanding redirs *)
  | .CommandExpRedirs assigns args (ers, none, []) opts =>
    let (s1, prog_special) :=
      match args with
      | s_prog :: _ =>
          let (s1, _, prog_name) := concretize s0 s_prog
          (s1, is_special_builtin prog_name)
      | _ =>
          (s0, false)

    let catching_errors :=
      (!checked_exit checked) && Set.Set.member .Sh_errexit s1.sh.opts

    let exit_on_error :=
      catching_errors ||
      (prog_special &&
        !opts.force_simple_command &&
        !(is_interactive s1))  -- per table in 2.8.1

    match do_redirs s1 ers with
    | (s2, .error msg) =>
      match check_traps
          ( .XSSimple ("error in redirection: " ++ msg)
          , fail_with msg s2
          , if exit_on_error then .Exit else .Done
          )
      with
      | .ok t => .ok t
      | .error e => .ok
          ( .XSSimple ("internal check_traps error: " ++ e)
          , fail_with e s2
          , if exit_on_error then .Exit else .Done
          )


    | (s2, .ok saved_fds) =>
        let exp_assigns :=
          List.map
            (fun (x, w) =>
              (x, .ExpStart { splitting := .NoSplit, globbing := false } w))
            assigns

        let s3 := new_local_scope s2

        .ok ( .XSSimple "redirected; expanding assignments"
        , s3
        , .CommandExpAssign exp_assigns args saved_fds opts
        )



  /- expand redirs *********************************************************** -/
  | .CommandExpRedirs assigns args redir_state opts =>
      -- 这里 step_redir_state 你之前迁移的是“不抛 Except”，保持即可
      match step_redir_state s0 redir_state with
      | (s1, msg, none) =>
          let (s2, may_exit) :=
            match args with
            | ss_prog :: _ =>
                let (s2, _, prog) := concretize s1 ss_prog
                (s2, is_special_builtin prog)
            | _ => (s1, false)
          match expansion_error may_exit s2
                  (.XSSimple "error in redirect expansion")
                  (.ESStep "")
                  [symbolic_string_of_string msg] with
          | .ok t => .ok t
          | .error emsg => .ok
              ( .XSSimple ("internal expansion_error: " ++ emsg)
              , fail_with emsg s2
              , if is_interactive s2 then .Done else .Exit
              )

      | (s1, msg, some (redir_state', mstep)) =>
          let (ran_cmd_subst', step') :=
            match mstep with
            | some estep =>
                ( opts.ran_cmd_subst || ran_command_substitution estep
                , .XSExpand (.XSSimple msg) estep
                )
            | none =>
                (opts.ran_cmd_subst, .XSSimple msg)
          let opts' := { opts with ran_cmd_subst := ran_cmd_subst' }
          .ok (step', s1, .CommandExpRedirs assigns args redir_state' opts')

  /- expanding assignments *************************************************** -/
  | .CommandExpAssign ((x, exp_state0) :: assigns) args saved_fds opts =>
      match step_expansion (s0, exp_state0) with
      | .error msg =>
        match check_traps
            ( .XSSimple ("internal expansion error: " ++ msg)
            , fail_with msg s0
            , if is_interactive s0 then .Done else .Exit
            )
        with
        | .ok t => .ok t
        | .error e => .ok
            ( .XSSimple ("internal check_traps error: " ++ e)
            , fail_with e s0
            , if is_interactive s0 then .Done else .Exit
            )

      | .ok (step, s1, exp_state1) =>
          let opts' :=
            { opts with ran_cmd_subst := opts.ran_cmd_subst || ran_command_substitution step }

          match exp_state1 with
          | .ExpDone f =>
              -- force_local_param 你原来是 Either；若你也改了 Except，同理处理
              match force_local_param s1 x (symbolic_string_of_fields f) with
              | .error err =>
                  let special_or_assign :=
                    match args with
                    | cmd :: _ =>
                        is_special_builtin (string_of_symbolic_string cmd) &&
                        !opts.force_simple_command
                    | [] => true
                  let may_exit :=
                    (!checked_exit checked && Set.Set.member .Sh_errexit s1.sh.opts) ||
                    !is_interactive s1
                  let s2 := safe_write_stderr (err ++ "\n") s1
                  .ok ( .XSSimple "assignment error"
                  , exit_with 2 s2
                  , if special_or_assign && may_exit then .Exit else .Done
                  )
              | .ok s2 => .ok
                  ( .XSSimple ("assign " ++ x)
                  , s2
                  , .CommandExpAssign assigns args saved_fds opts'
                  )

          | .ExpError err =>
              match expansion_error true s1 (.XSSimple "assignment expansion") step err with
              | .ok t => .ok t
              | .error msg => .ok
                  ( .XSSimple ("internal expansion_error error: " ++ msg)
                  , fail_with msg s1
                  , if is_interactive s1 then .Done else .Exit
                  )

          | _ => .ok
              ( .XSExpand (.XSSimple "") step
              , s1
              , .CommandExpAssign ((x, exp_state1) :: assigns) args saved_fds opts'
              )

  | .CommandExpAssign [] args saved_fds opts =>
    -- pop locals accumulated during assignment expansion
    match pop_locals s0 with
    | .error msg => .ok
        -- 这里按你的语义处理：要么直接报错（Except），要么把错误降级成 fail_with + Done/Exit
        -- 如果你在 step_eval 里：建议降级成三元组返回
        -- 例：返回一个错误 step（请按你当前分支需要的返回类型改）
        ( .XSSimple ("pop_locals failed: " ++ msg)
        , fail_with msg s0
        , .Done
        )

    | .ok (s1, local_env) =>
      let assigns :=
        Map.toList
          (Map.mapMaybe (fun (_x : String) (m_v, _opts) => m_v) local_env)

      match args with
      | [] =>
          -- no command name: just restore fds, maybe set exit code to 0, then commit assigns
          let s2 := restore_fds s1 saved_fds
          let s3 := if opts.ran_cmd_subst then s2 else exit_with 0 s2

          -- we've already called check_param in force_local_param
          let s4 :=
            List.foldr
              (fun (x, v) os => checked_set_param x v os)
              s3
              assigns

          -- announce what we've done if `set -x`
          let trace :=
            String.intercalate " "
              (List.map (fun (x, v) => x ++ "=" ++ string_of_symbolic_string v) assigns)

          let s5 := xtrace trace s4

          .ok ( .XSSimple "finished assignments w/o command, popping redirects"
          , s5
          , .Done
          )

      | cmd :: argv => .ok
          -- we have a command; continue
          ( .XSSimple "assignments fully expanded"
          , s1
          , .CommandReady assigns cmd argv saved_fds opts
          )

  | cmd@(.CommandReady assigns prog args saved_fds opts) =>
    if Set.Set.member .Sh_noexec s0.sh.opts then
      .ok (.XSSimple "set -n: skipping command", s0, .Done)
    else
      let s0_traced := xtrace (string_of_stmt cmd) s0

      let (s0_logged, concretized, prog_name) := concretize s0_traced prog
      let prog_special := is_special_builtin prog_name

      let s1 :=
        if (!concretized) && prog_special && (!opts.force_simple_command) then
          -- checked_set_param 已封装了 set_param 的 Except 逻辑（你工程里就是这么用的）
          List.foldr (fun (x, v) os => checked_set_param x v os) s0_logged assigns
        else
          s0_logged

      let catching_errors :=
        (!checked_exit checked) && Set.Set.member .Sh_errexit s1.sh.opts

      let exit_on_error :=
        catching_errors ||
        (prog_special &&
          !opts.force_simple_command &&
          !(is_interactive s1))  -- per table in 2.8.1

      -- load exported variables, perform assignments
      let env := Map.fromList assigns

      match run_command s1 opts checked prog args env with
      | .ok (s2, .Done, restore) => .ok
          ( .XSSimple ("done running " ++ string_of_symbolic_string prog)
          , s2
          , if catching_errors && s2.sh.exit_code ≠ 0 then
              .Exit
            else if restore then
              pushredir .Done saved_fds
            else
              .Done
          )

      | .ok (s2, stmt', restore) => .ok
          ( .XSSimple ("running " ++ string_of_symbolic_string prog)
          , s2
          , if restore then
              pushredir stmt' saved_fds
            else
              stmt'
          )

      | .error (s2, msg) =>
        match check_traps
            ( .XSSimple "couldn't run command"
            , fail_with (string_of_symbolic_string prog ++ ": " ++ msg) s2
            , if exit_on_error then .Exit else pushredir .Done saved_fds
            )
        with
        | .ok t => .ok t
        | .error e => .ok
            ( .XSSimple ("internal check_traps error: " ++ e)
            , fail_with e s2
            , if exit_on_error then .Exit else pushredir .Done saved_fds
            )


  | .Pipe bg_mode stmts =>
    match run_pipe s0 stmts bg_mode with
    | .error err =>
      match check_traps
          ( .XSPipe "couldn't start pipe"
          , fail_with ("couldn't create pipeline: " ++ err) s0
          , if (!checked_exit checked) && Set.Set.member .Sh_errexit s0.sh.opts then
              .Exit
            else
              .Done
          )
      with
      | .ok t => .ok t
      | .error e => .ok
          ( .XSPipe ("internal check_traps error: " ++ e)
          , fail_with e s0
          , if (!checked_exit checked) && Set.Set.member .Sh_errexit s0.sh.opts then
              .Exit
            else
              .Done
          )


    | .ok (s1, pipeline, last_pid) =>
        let (s2, c) :=
          let (s2, _job) :=
            add_job s1 pipeline last_pid (.Pipe bg_mode stmts) bg_mode .JobRunning
          if is_bg bg_mode then
            (set_last_pid last_pid s2, .Done)
          else
            -- non-background pipeline: wait for last pid (and maybe others)
            (s2, .Wait last_pid checked (some 0) .WaitInternal)  -- ← 如果你 Wait 的 bound 用 Option Nat，请改成 `none`
            match check_traps (.XSPipe "started pipe", s2, c) with
            | .ok t => .ok t
            | .error e => .ok
                ( .XSPipe ("internal check_traps error: " ++ e)
                , fail_with e s2
                , c
                )


  | .Redir stmt' (ers, none, []) =>
    let t :=
      match do_redirs s0 ers with
      | (s1, .error msg) =>
          ( .XSRedir "error in redirection"
          , fail_with msg s1
          , .Done
          )
      | (s1, .ok saved_fds) =>
          ( .XSRedir "running redirected command"
          , s1
          , pushredir stmt' saved_fds
          )

    match check_traps t with
    | .ok t' => .ok t'
    | .error e => .ok
        ( .XSRedir ("internal check_traps error: " ++ e)
        , fail_with e s0
        , .Done
        )


-- redirection steps
  | .Redir stmt' redir_state =>
    match step_redir_state s0 redir_state with
    | (s1, msg, none) =>
      match check_traps
          ( .XSRedir "error in redirect expansion"
          , fail_with msg s1
          , .Done
          )
      with
      | .ok t => .ok t
      | .error e => .ok
          ( .XSRedir ("internal check_traps error: " ++ e)
          , fail_with e s1
          , .Done
          )


    | (s1, msg, some (redir_state', mstep)) =>
        let step :=
          match mstep with
          | some estep => .XSExpand (.XSRedir msg) estep
          | none       => .XSRedir msg
        .ok (step, s1, .Redir stmt' redir_state')

  | .Background stmt' redir_state@(ers, none, []) =>
    let redir_state' :=
      if (!is_monitoring s0) && !(ers.any expanded_redir_has_stdin_redir) then
        -- assign stdin from /dev/null when job control disabled and no explicit stdin redir
        (.ERFile .From 0 (symbolic_string_of_string "/dev/null") :: ers, none, [])
      else
        redir_state

    -- defer to Redir to load redirs
    let (s1, pid) :=
      fork_and_subshell s0 (.Redir stmt' redir_state')
        .BG none true   -- no pgid; job control possible?

    let (s2, _job) :=
      add_job s1 [(pid, .Background stmt' redir_state)]  -- unit pipeline
        pid (.Background stmt' redir_state) .BG .JobRunning

    let s3 := set_last_pid pid s2

    match check_traps
        ( .XSBackground ("started background process with pid " ++ stringFromNat pid)
        , s3
        , .Done
        )
    with
    | .ok t => .ok t
    | .error e => .ok
        ( .XSBackground ("internal check_traps error: " ++ e)
        , fail_with e s3
        , .Done
        )


-- expand redirs
  | .Background stmt' redir_state =>
    match step_redir_state s0 redir_state with
    | (s1, msg, none) =>
      match check_traps
          ( .XSBackground "error in redirect expansion"
          , fail_with msg s1
          , .Done
          )
      with
      | .ok t => .ok t
      | .error e => .ok
          ( .XSBackground ("internal check_traps error: " ++ e)
          , fail_with e s1
          , .Done
          )


    | (s1, msg, some (redir_state', mstep)) =>
        let step :=
          match mstep with
          | some estep => .XSExpand (.XSBackground msg) estep
          | none       => .XSBackground msg
        .ok (step, s1, .Background stmt' redir_state')

  | .Subshell stmt' (ers, none, []) =>
    let checked_c := if checked_exit checked then .CheckedExit stmt' else stmt'

    match do_redirs s0 ers with
    | (s1, .error msg) => .ok
        ( .XSSubshell "error in redirection"
        , fail_with msg s1
        , .Done
        )

    | (s1, .ok saved_fds) =>
        let (s2, pid) :=
          fork_and_subshell s1 checked_c
            .FG none true   -- no pgid; job control possible?

      match check_traps
          ( .XSSubshell ("started subshell with pid " ++ stringFromNat pid)
          , restore_fds s2 saved_fds
          , .Wait pid checked .none .WaitInternal
          )
      with
      | .ok t => .ok t
      | .error e => .ok
          ( .XSSubshell ("internal check_traps error: " ++ e)
          , fail_with e (restore_fds s2 saved_fds)
          , .Done
          )


  | .Subshell stmt' redir_state =>
    match step_redir_state s0 redir_state with
    | (s1, msg, none) =>
      match check_traps
          ( .XSSubshell "error in redirect expansion"
          , fail_with msg s1
          , .Done
          )
      with
      | .ok t => .ok t
      | .error e => .ok
          ( .XSSubshell ("internal check_traps error: " ++ e)
          , fail_with e s1
          , .Done
          )


    | (s1, msg, some (redir_state', mstep)) =>
        let step :=
          match mstep with
          | some estep => .XSExpand (.XSSubshell msg) estep
          | none       => .XSSubshell msg
        .ok (step, s1, .Subshell stmt' redir_state')

-- AND
  | .And l r =>
    match step_eval s0 .Checked l with
    | .error msg => .error msg
    | .ok (step, s1, l') =>

    match l' with
    | .Exit       => .ok (step, s1, .Exit)
    | .Return     => .ok (step, s1, .Return)
    | .Break n    => .ok (step, s1, .Break n)
    | .Continue n => .ok (step, s1, .Continue n)
    | .Done =>
      let t :=
        if s1.sh.exit_code = 0 then
          (.XSAnd "exit code was 0, continuing", s1, r)
        else
          (.XSAnd "exit code was non-zero, short-circuiting", s1, .Done)

      match check_traps t with
      | .ok t' => .ok t'
      | .error e => .ok
          ( .XSAnd ("internal check_traps error: " ++ e)
          , fail_with e s1
          , .Done
          )

    | _ => .ok
        (.XSNested (.XSAnd "") step, s1, .And l' r)

-- OR
  | .Or l r =>
    match step_eval s0 .Checked l with
    | .error msg => .error msg
    | .ok (step, s1, l') =>
    match l' with
    | .Exit       => .ok (step, s1, .Exit)
    | .Return     => .ok (step, s1, .Return)
    | .Break n    => .ok (step, s1, .Break n)
    | .Continue n => .ok (step, s1, .Continue n)
    | .Done =>
      let t :=
        if s1.sh.exit_code = 0 then
          (.XSOr "exit code was 0, short-circuiting", s1, .Done)
        else
          (.XSOr "exit code was non-zero, continuing", s1, r)

      match check_traps t with
      | .ok t' => .ok t'
      | .error e => .ok
          ( .XSOr ("internal check_traps error: " ++ e)
          , fail_with e s1
          , .Done
          )

    | _ => .ok
        (.XSNested (.XSOr "") step, s1, .Or l' r)

-- NOT
  | .Not stmt' =>
    match step_eval s0 .Checked stmt' with
    | .error msg => .error msg
    | .ok (step, s1, stmt'') =>
    match stmt'' with
    | .Exit       => .ok (step, s1, .Exit)
    | .Return     => .ok (step, s1, .Return)
    | .Break n    => .ok (step, s1, .Break n)
    | .Continue n => .ok (step, s1, .Continue n)
    | .Done =>
      let t :=
        if s1.sh.exit_code = 0 then
          (.XSNot "0 -> 1", exit_with 1 s1, .Done)
        else
          (.XSNot "!0 -> 0", exit_with 0 s1, .Done)

      match check_traps t with
      | .ok t' => .ok t'
      | .error e => .ok
          ( .XSNot ("internal check_traps error: " ++ e)
          , fail_with e s1
          , .Done
          )

    | _ => .ok
        (.XSNested (.XSNot "") step, s1, .Not stmt'')

-- SEMI
  | .Semi l r =>
    match step_eval s0 .Checked l with
    | .error msg => .error msg
    | .ok (step, s1, l') =>
    match l' with
    | .Exit       => .ok (step, s1, .Exit)
    | .Return     => .ok (step, s1, .Return)
    | .Break n    => .ok (step, s1, .Break n)
    | .Continue n => .ok (step, s1, .Continue n)
    | .Done       => match check_traps (.XSNested (.XSSemi "done with LHS") step, s1, r) with
                     | .ok t => .ok t
                     | .error e => .ok
                        ( .XSSemi ("internal check_traps error: " ++ e)
                        , fail_with e s1
                        , .Done
                        )

    | _          => .ok (.XSNested (.XSSemi "") step, s1, .Semi l' r)

  -- IF
  | .If c t e =>
    match step_eval s0 .Checked c with
    | .error msg => .error msg
    | .ok (step, s1, c') =>
    match c' with
    | .Exit       => .ok (step, s1, .Exit)
    | .Return     => .ok (step, s1, .Return)
    | .Break n    => .ok (step, s1, .Break n)
    | .Continue n => .ok (step, s1, .Continue n)
    | .Done =>
      let tup :=
        if s1.sh.exit_code = 0 then
          (.XSIf "exit code was 0, taking the true branch", s1, t)
        else
          (.XSIf "exit code was non-zero, taking the false branch", s1, e)

      match check_traps tup with
      | .ok r => .ok r
      | .error msg => .ok
          ( .XSIf ("internal check_traps error: " ++ msg)
          , fail_with msg s1
          , .Done
          )

    | _ => .ok
        (.XSNested (.XSIf "") step, s1, .If c' t e)

-- WHILE
  | .While c body => .ok
    ( .XSWhile "start to evaluate the condtion"
    , enter_loop s0
    , .WhileCond c c body none
    )

  | .WhileCond c cur body saved_ec =>
    match step_eval s0 .Checked cur with
    | .error msg => .error msg
    | .ok (step, s1, cur') =>
    match cur' with
    | .Exit    => .ok (.XSNested (.XSWhile "exiting") step, s1, .Exit)
    | .Return  => .ok (.XSNested (.XSWhile "returning") step, s1, .Return)

    | .Break 1 => .ok
        (.XSNested (.XSWhile "breaking") step, exit_loop s1, .Done)

    | .Break n => .ok
        ( .XSNested (.XSWhile "breaking to outer loop") step
        , exit_loop s1
        , .Break (n - 1)
        )

    | .Continue 1 => .ok
        ( .XSNested (.XSWhile "continuing loop") step
        , s1
        , .WhileCond c c body saved_ec
        )

    | .Continue n => .ok
        ( .XSNested (.XSWhile "continuing to outer loop") step
        , exit_loop s1
        , .Continue (n - 1)
        )

    | .Done =>
      let tup :=
        if s1.sh.exit_code = 0 then
          ( .XSWhile "exit code was 0, running the loop body"
          , s1
          , .WhileRunning c body body
          )
        else
          let ec :=
            match saved_ec with
            | none     => 0
            | some ec' => ec'
          ( .XSWhile "exit code was non-zero, taking the false branch"
          , exit_with ec (exit_loop s1)
          , .Done
          )

      match check_traps tup with
      | .ok r => .ok r
      | .error msg => .ok
          ( .XSWhile ("internal check_traps error: " ++ msg)
          , fail_with msg s1
          , .Done
          )


    | _ => .ok
        (.XSNested (.XSWhile "") step, s1, .WhileCond c cur' body saved_ec)

  | .WhileRunning c body cur =>
    match step_eval s0 .Checked cur with
    | .error msg => .error msg
    | .ok (step, s1, cur') =>
    match cur' with
    | .Exit   => .ok (.XSNested (.XSWhile "exiting") step, s1, .Exit)
    | .Return => .ok (.XSNested (.XSWhile "returning") step, s1, .Return)

    | .Break 1 => .ok
        (.XSNested (.XSWhile "breaking loop") step, exit_loop s1, .Done)

    | .Break n => .ok
        ( .XSNested (.XSWhile "breaking to outer loop") step
        , exit_loop s1
        , .Break (n - 1)
        )

    | .Continue 1 => .ok
        ( .XSNested (.XSWhile "continuing loop") step
        , s1
        , .WhileCond c c body (some s1.sh.exit_code)
        )

    | .Continue n => .ok
        ( .XSNested (.XSWhile "continuing to outer loop") step
        , exit_loop s1
        , .Continue (n - 1)
        )

    | .Done =>
      match check_traps
          ( .XSNested (.XSWhile "finished iteration of while loop; retesting condition") step
          , s1
          , .WhileCond c c body (some s1.sh.exit_code)
          ) with
      | .ok t => .ok t
      | .error msg => .ok
          ( .XSWhile ("internal check_traps error: " ++ msg)
          , fail_with msg s1
          , .Done
          )


    | _ => .ok
        (.XSNested (.XSWhile "") step, s1, .WhileRunning c body cur')

-- FOR
  | .For var ws body => .ok
    ( .XSFor "begin arg expansion"
    , s0
    , .ForExpArgs var (.ExpStart { splitting := .Split, globbing := true } ws) body
    )

  | .ForExpArgs var exp_state body =>
    match step_expansion (s0, exp_state) with
    | .error msg => .ok
        -- step_expansion 的 Except.error 是 failwith/内部错误：这里直接当成 expansion error 处理
        -- expansion_error true os0 (.XSFor "arg expansion") (.ESStep "") [symbolic_string_of_string msg]
        -- ↑ 如果你不想这么“兜底”，也可以改成：
        (.XSFor msg, fail_with msg s0, if is_interactive s0 then .Done else .Exit)
        -- 取决于你工程对 internal error 的策略
        -- where os0 := s0  -- 只是避免上面引用未绑定；你也可以直接用 s0

    | .ok (step, os1, st1) =>
        match st1 with
        | .ExpError err =>
          match expansion_error true os1 (.XSFor "arg expansion") step err with
          | .ok t => .ok t
          | .error emsg => .ok
              ( .XSSimple ("internal expansion_error: " ++ emsg)
              , fail_with emsg os1
              , if is_interactive os1 then .Done else .Exit
              )

        | .ExpDone f => .ok
            ( .XSFor "arguments fully expanded"
            , os1
            , .ForExpanded var f body
            )

        | in_progress => .ok
            ( .XSExpand (.XSFor "argument expansion step") step
            , os1
            , .ForExpArgs var in_progress body
            )

-- FOR: Special case, no items exit status is zero
  | .ForExpanded _var [] _body =>
    match check_traps
        ( .XSFor "no items, exit code is 0"
        , exit_with 0 s0
        , .Done
        ) with
    | .ok t => .ok t
    | .error msg => .ok
        ( .XSFor ("internal check_traps error: " ++ msg)
        , fail_with msg s0
        , .Done
        )


  | .ForExpanded var (i :: f) body =>
    match set_param var i s0 with
    | .error err => .ok
        ( .XSFor err
        , fail_with ("for: " ++ err) s0
        , if is_interactive s0 then .Done else .Exit
        )
    | .ok s1 =>
        let s2 := enter_loop s1
        .ok ( .XSFor ("starting for loop with " ++ var ++ " = " ++ string_of_symbolic_string i)
        , s2
        , .ForRunning var f body body
        )

  | .ForRunning var f body cur =>
    let continue_ (s0 : os_state α) (step : evaluation_step) (msg : String) (i : symbolic_string) (f' : List symbolic_string) :=
      match set_param var i s0 with
      | .error err => .ok
          ( .XSNested (.XSFor err) step
          , fail_with ("for: " ++ err) s0
          , if is_interactive s0 then .Done else .Exit
          )
      | .ok s1 => .ok
          ( .XSNested (.XSFor (msg ++ " to next iteration with " ++ var ++ " = " ++ string_of_symbolic_string i)) step
          , s1
          , .ForRunning var f' body body
          )

    match step_eval s0 .Checked cur with
    | .error msg => .error msg
    | .ok (step, s1, cur') =>
    match cur' with
    | .Exit       => .ok (.XSNested (.XSFor "exiting") step, s1, .Exit)
    | .Return     => .ok (.XSNested (.XSFor "returning") step, s1, .Return)
    | .Break 1    => .ok (.XSNested (.XSFor "breaking loop") step, exit_loop s1, .Done)
    | .Break n    => .ok (.XSNested (.XSFor "breaking to outer loop") step, exit_loop s1, .Break (n - 1))
    | .Continue 1 =>
        match f with
        | []        => .ok (.XSNested (.XSFor "continued at last iteration") step, exit_loop s1, .Done)
        | i :: f'   => continue_ s1 step "continuing" i f'
    | .Continue n => .ok (.XSNested (.XSFor "continuing to outer loop") step, s1, .Continue (n - 1))
    | .Done =>
      let tupE : Except String (evaluation_step × os_state α × stmt) :=
        match f with
        | [] =>
            .ok
              ( .XSNested (.XSFor "finished last iteration") step
              , exit_loop s1
              , .Done
              )
        | i :: f' =>
            continue_ s1 step "stepping" i f'   -- 这里假设 continue_ : Except String (...)

      match tupE with
      | .error msg =>
          -- 你也可以选择把这个 error 直接 .error msg 传播；这里按你的风格降级成 ok
          .ok
            ( .XSFor ("internal continue_ error: " ++ msg)
            , fail_with msg s1
            , .Done
            )
      | .ok tup =>
          match check_traps tup with
          | .ok t => .ok t
          | .error msg =>
              .ok
                ( .XSFor ("internal check_traps error: " ++ msg)
                , fail_with msg s1
                , .Done
                )


    | _ => .ok
        (.XSNested (.XSFor "") step, s1, .ForRunning var f body cur')

-- CASE
  | .Case ws cases => .ok
    ( .XSCase "begin arg expansion"
    , s0
    , .CaseExpArg (.ExpStart { splitting := .NoSplit, globbing := false } ws) cases
    )

  | .CaseExpArg exp_state cases =>
    match step_expansion (s0, exp_state) with
    | .error msg =>
        -- 内部错误：这里没有 Except 可抛，按“扩展错误”降级
      match expansion_error true s0 (.XSCase "arg expansion") (.ESStep "")
              [symbolic_string_of_string msg] with
      | .ok t => .ok t
      | .error emsg => .ok
          ( .XSCase ("internal expansion_error: " ++ emsg)
          , fail_with emsg s0
          , if is_interactive s0 then .Done else .Exit
          )

    | .ok (step, os1, st1) =>
        match st1 with
        | .ExpError err =>
          match expansion_error true os1 (.XSCase "arg expansion") step err with
          | .ok t => .ok t
          | .error msg => .ok
              ( .XSCase ("internal expansion error: " ++ msg)
              , fail_with msg os1
              , if is_interactive os1 then .Done else .Exit
              )

        | .ExpExpand _opts ew [] =>
            -- "...matched by the string resulting from ... quote removal ..."
            let ss := symbolic_string_of_expanded_words false ew
            .ok (.XSCase "argument fully expanded", os1, .CaseMatch ss cases)

        | in_progress => .ok
            ( .XSExpand (.XSCase "argument expansion step") step
            , os1
            , .CaseExpArg in_progress cases
            )

  | .CaseMatch f cases =>
    match cases with
    | [] =>
      match check_traps (.XSCase "no match in case statement", exit_with 0 s0, .Done) with
      | .ok t => .ok t
      | .error msg => .ok
          ( .XSCase ("internal check_traps error: " ++ msg)
          , fail_with msg s0
          , .Done
          )

    | ([], _cmd) :: cases' => .ok
        (.XSCase "exhausted patterns, checking next case", s0, .CaseMatch f cases')

    | (pat :: pats', cmd) :: cases' => .ok
        ( .XSCase "checking pattern match"
        , s0
        , .CaseCheckMatch f
            (.ExpStart { splitting := .NoSplit, globbing := false } pat)
            cmd
            ((pats', cmd) :: cases')
        )

  | .CaseCheckMatch f pat cmd cases =>
    match step_expansion (s0, pat) with
    | .error msg =>
      match expansion_error true s0 (.XSCase "error in argument expansion") (.ESStep "")
          [symbolic_string_of_string msg] with
      | .ok t => .ok t
      | .error emsg => .ok
          ( .XSCase ("internal expansion error: " ++ emsg)
          , fail_with emsg s0
          , if is_interactive s0 then .Done else .Exit
          )


    | .ok (step, os1, st1) =>
        match st1 with
        | .ExpError err =>
          match expansion_error true os1 (.XSCase "error in argument expansion") step err with
          | .ok t => .ok t
          | .error emsg => .ok
              ( .XSCase ("internal expansion error: " ++ emsg)
              , fail_with emsg os1
              , if is_interactive os1 then .Done else .Exit
              )

        | .ExpExpand _opts ew [] =>
            let pat' := symbolic_string_of_expanded_words true ew
            match match_exact lc_ambient pat' f with
            | .noMatch => .ok
                (.XSCase "case did not match, trying the next", os1, .CaseMatch f cases)
            | .Match _ =>
                match check_traps (.XSCase "case matched, evaluating cmd", os1, cmd) with
                | .ok t => .ok t
                | .error msg => .ok
                    ( .XSCase ("internal check_traps error: " ++ msg)
                    , fail_with msg os1
                    , .Done
                    )

            | .symbolic => .ok
                ( .XSCase "case on symbolic value, gave up"
                , fail_with "case: symbolic match, giving up" os1
                , .Done
                )

        | in_progress => .ok
            ( .XSExpand (.XSCase "pattern expansion step") step
            , os1
            , .CaseCheckMatch f in_progress cmd cases
            )

-- DEFUN
  | .Defun name body =>
    if is_special_builtin name then
      let msg := "invalid function name " ++ name ++ " (shadows special built-in)"
      .ok ( .XSDefun msg
      , fail_with msg s0
      , if is_interactive s0 then .Done else .Exit
      )
    else
      let s1 :=
        if Set.Set.member .Sh_earlyhash s0.sh.opts then
          early_hash s0 body
        else
          s0
      match check_traps
          ( .XSDefun ("defined " ++ name)
          , defun name body (exit_with 0 s1)
          , .Done
          ) with
      | .ok t => .ok t
      | .error msg => .ok
          ( .XSDefun ("internal check_traps error: " ++ msg)
          , fail_with msg s1
          , .Done
          )


-- CALL
  | .Call old_loop_nest old_positional_params f orig c =>
    let cleanupE (os : os_state α) : Except String (os_state α) :=
      match pop_locals os with
      | .error msg => .error msg
      | .ok (os', _local_env) => .ok
          (set_function_params old_loop_nest old_positional_params os')


    match step_eval s0 .Checked c with
    | .error msg => .error msg
    | .ok (step, s1, c') =>
    match c' with
    | .Done =>
      match cleanupE s1 with
      | .ok sClean =>
          match check_traps (.XSStack (f ++ ": implicit return") step, sClean, .Done) with
          | .ok t => .ok t
          | .error msg => .ok
              ( .XSStack ("internal check_traps error: " ++ msg) step
              , fail_with msg s1
              , .Done
              )
      | .error msg =>
          -- cleanup 失败：按内部错误降级
          match check_traps
              ( .XSStack ("internal cleanup error: " ++ msg) step
              , fail_with msg s1
              , if is_interactive s1 then .Done else .Exit
              ) with
          | .ok t => .ok t
          | .error msg2 => .ok
              ( .XSStack ("internal check_traps error: " ++ msg2) step
              , fail_with msg2 s1
              , .Done
              )



    | .Return =>
      match cleanupE s1 with
      | .ok sClean =>
          match check_traps (.XSStack (f ++ ": explicit return") step, sClean, .Done) with
          | .ok t => .ok t
          | .error msg => .ok
              ( .XSStack ("internal check_traps error: " ++ msg) step
              , fail_with msg s1
              , .Done
              )
      | .error msg =>
          match check_traps
              ( .XSStack ("internal cleanup error: " ++ msg) step
              , fail_with msg s1
              , if is_interactive s1 then .Done else .Exit
              ) with
          | .ok t => .ok t
          | .error msg2 => .ok
              ( .XSStack ("internal check_traps error: " ++ msg2) step
              , fail_with msg2 s1
              , .Done
              )

    | .Exit =>
        match cleanupE s1 with
        | .ok sClean => .ok (.XSStack (f ++ ": exit") step, sClean, .Exit)
        | .error msg => .ok
            (.XSStack ("internal cleanup error: " ++ msg) step, fail_with msg s1, .Exit)

    | .Break n =>
        if (Set.Set.member .Sh_nonlexicalctrl s1.sh.opts) then
          match cleanupE s1 with
          | .ok s2 => .ok
              (.XSStack (f ++ ": break [unspecified behavior]") step, s2, .Break n)
          | .error msg => .ok
              (.XSStack ("internal cleanup error: " ++ msg) step, fail_with msg s1, .Break n)
        else
          .error "non-lexical break without -o nonlexicalctrl"
    | .Continue n =>
        if (Set.Set.member .Sh_nonlexicalctrl s1.sh.opts) then
          match cleanupE s1 with
          | .ok s2 => .ok
              (.XSStack (f ++ ": continue [unspecified behavior]") step, s2, .Continue n)
          | .error msg => .ok
              (.XSStack ("internal cleanup error: " ++ msg) step, fail_with msg s1, .Continue n)
        else
         .error "non-lexical continue without -o nonlexicalctrl"
    | _ => .ok
        ( .XSStack f step
        , s1
        , .Call old_loop_nest old_positional_params f orig c'
        )

  | .EvalLoop linno ctx@(.Mk sstr stackmark) src interactive shell_level =>
    -- INVARIANT: you must call parse_cleanup sstr if you're leaving the eval loop
    let s1 := show_changed_jobs .DeleteJobs .Sh_monitor s0
    let (s2, parsed) := parse_next s1 interactive
    match check_traps <|
      match parsed with
      | .ParseDone =>
          let (s3, c) :=
            if is_interactive_mode interactive &&
              is_toplevel shell_level &&
              Set.Set.member .Sh_ignoreeof s2.sh.opts then
              ( write_stderr "Use \"exit\" to leave the shell.\n" s2
              , .EvalLoop linno ctx src interactive shell_level
              )
            else
              let _ := parse_cleanup sstr stackmark shell_level
              (s2, .Done)
          (.XSEval linno src "done", s3, c)
      | .ParseError s =>
          let s3 :=
            exit_with 2 <|
              if s = "" then s2 else write_stderr s s2
          let c' :=
            if is_interactive_mode interactive && is_toplevel shell_level then
              .EvalLoop linno ctx src interactive shell_level
            else
              let _ := parse_cleanup sstr stackmark shell_level
              let catching_errors :=
                (!checked_exit checked) && Set.Set.member .Sh_errexit s1.sh.opts
              let exit_on_error := catching_errors || !(is_interactive s3)
              if exit_on_error then .Exit else .Done
          (.XSEval linno src "parse error", s3, c')
      | .ParseNull =>
          ( .XSEval linno src "empty line"
          , s2
          , .EvalLoop (linno + 1) ctx src interactive shell_level
          )
      | .ParseStmt c =>
          let s3 :=
            if is_interactive_mode interactive && is_toplevel shell_level then
              add_to_history c s2
            else
              s2
          ( .XSEval linno src ""
          , s3
          , .EvalLoopCmd (linno + 1) ctx src interactive shell_level c
          )
    with
    | .ok t => .ok t
    | .error msg => .ok
        ( .XSEval linno src ("internal check_traps error: " ++ msg)
        , fail_with msg s2
        , .Done
        )


  | .EvalLoopCmd linno ctx@(.Mk sstr stackmark) src interactive shell_level c =>
    -- INVARIANT: you must call parse_cleanup sstr shell_level if you're leaving the eval loop
    match step_eval s0 .Checked c with
    | .error msg => .error msg
    | .ok (step, s1, c') =>
    match c' with
    | .Exit =>
        let _ := parse_cleanup sstr stackmark shell_level
        .ok (step, s1, .Exit)

    | .Done => .ok
        (step, s1, .EvalLoop linno ctx src interactive shell_level)

    | .Return =>
        let (step', c'') :=
          if is_toplevel shell_level then
            ( .XSNested (.XSEval linno src "return at top level") step
            , .EvalLoop linno ctx src interactive shell_level
            )
          else
            let _ := parse_cleanup sstr stackmark shell_level
            if parse_source_for_dot src then
              ( .XSNested (.XSEval linno src "return from dot") step
              , .Done
              )
            else
              ( .XSNested (.XSEval linno src "return in eval loop") step
              , .Return
              )
        .ok (step', s1, c'')

    | _ =>
        if is_terminating_control c' then
          -- terminating control other than Exit/Done/Return
        match check_traps
            ( .XSNested (.XSEval linno src "returning to loop") step
            , s1
            , if (!is_toplevel shell_level) && parse_source_propagates_control src then
                -- allow break/continue to propagate out of eval
                let _ := parse_cleanup sstr stackmark shell_level
                c'
              else
                -- ignore at top-level or in dot
                .EvalLoop linno ctx src interactive shell_level
            )
        with
        | .ok t => .ok t
        | .error msg => .ok
            ( .XSNested (.XSEval linno src ("internal check_traps error: " ++ msg)) step
            , fail_with msg s1
            , .Done
            )

        else
          -- keep on running
          .ok ( .XSNested (.XSEval linno src "") step
          , s1
          , .EvalLoopCmd linno ctx src interactive shell_level c'
          )

-- EXEC
  | .Exec cmd argv0 args env binsh =>
    -- INVARIANT: check_execve already called before generating Exec
    -- symbolic execve returns; real execve does not
    let (s1, res) := execve s0 cmd argv0 args env binsh
    let msg :=
      match res with
      | .error msg    => msg
      | .ok _stmt  => "symbolic execve unimplemented"
    .ok ( .XSExec msg
    , fail_with msg s1
    , if is_interactive s1 then .Done else .Exit
    )

-- WAIT: out of steps
  | .Wait n _checked (some 0) _mode =>
    match check_traps
        ( .XSWait ("stopped blocking on process with pid " ++ stringFromNat n)
        , s0
        , .Done
        )
    with
    | .ok t => .ok t
    | .error msg => .ok
        ( .XSWait ("internal check_traps error: " ++ msg)
        , fail_with msg s0
        , .Done
        )


-- WAIT: normal
  | .Wait pid checking bound mode =>
    let exit_on_error :=
      (!checked_exit checking) && Set.Set.member .Sh_errexit s0.sh.opts
    let s_pid := stringFromNat pid
    let stepEval' : step_fun α :=
      fun os checked st =>
        match step_eval os checked st with
        | .ok t => t
        | .error msg =>
            ( .XSSimple ("internal step_eval error: " ++ msg)
            , fail_with msg os
            , if is_interactive os then .Done else .Exit
            )
    match wait_for_pid  (step_eval := stepEval') s0 pid with
    | (s1, none) =>
        let tup :=
          ( .XSWait ("couldn't step process with pid " ++ s_pid)
          , (if from_wait_command mode then
              safe_write_stderr ("wait: pid " ++ s_pid ++ " is not a child of this shell\n") s1
            else
              s1)
          , .Done
          )
        match check_traps tup with
        | .ok t => .ok t
        | .error msg =>
            .ok
              ( .XSWait ("internal check_traps error: " ++ msg)
              , fail_with msg s1
              , .Done
              )



    | (s1, some (.error step)) =>
        -- we took a step, so record it
        let bound' :=
          match bound with
          | none   => none
          | some n => some (n - 1)
        .ok ( .XSNested (.XSWait ("process with pid " ++ s_pid ++ " stepped")) step
        , s1
        , .Wait pid checking bound' mode
        )

    | (s1, some (.ok code)) =>
        let s2 := delete_job_with_pid s1 pid
        match check_traps
            ( .XSWait ("process with pid " ++ s_pid ++ " completed with code " ++ stringFromNat code)
            , exit_with code s2
            , if exit_on_error && code ≠ 0 then .Exit else .Done
            )
        with
        | .ok t => .ok t
        | .error msg =>
            .ok ( .XSWait ("internal check_traps error: " ++ msg)
            , fail_with msg s2
            , .Done
            )


-- TRAPPED
  | .Trapped signal old_ec c_handler c_cont =>
    if is_terminating_control c_handler then
      let (s1, c) :=
        if c_handler = .Exit then
          (s0, .Exit)               -- don't restore old exit code!
        else
          (exit_with old_ec s0, c_cont)
      .ok (.XSTrap signal "finished", s1, c)
    else
      match step_eval s0 .Unchecked c_handler with
      | .error msg => .error msg
      | .ok (step, s1, c_handler') => .ok
        ( .XSNested (.XSTrap signal "") step
        , s1
        , .Trapped signal old_ec c_handler' c_cont
        )

-- CHECKEDEXIT
  | .CheckedExit c =>
    if is_terminating_control c then
      match check_traps (.XSSubshell "", s0, c) with
      | .ok t => .ok t
      | .error msg => .ok
          ( .XSSubshell ("internal check_traps error: " ++ msg)
          , fail_with msg s0
          , .Done
          )

          else
            match step_eval s0 .Checked c with
            | .error msg => .error msg
            | .ok (step, s1, c') => .ok
              ( .XSNested (.XSSubshell "disable errexit") step
              , s1
              , .CheckedExit c'
              )

-- PUSHREDIR
  | .Pushredir c saved_fds =>
    if is_terminating_control c then
      match check_traps
          ( .XSRedir "popping redirects"
          , restore_fds s0 saved_fds
          , c
          )
      with
      | .ok t => .ok t
      | .error msg => .ok
          ( .XSRedir ("internal check_traps error: " ++ msg)
          , fail_with msg s0
          , .Done
          )

    else
      match step_eval s0 .Checked c with
      | .error msg => .error msg
      | .ok (step, s1, c') => .ok
        ( .XSNested (.XSRedir "") step
        , s1
        , .Pushredir c' saved_fds
        )

-- BREAK/CONTINUE/RETURN/EXIT/DONE
  | .Break _n =>
    match check_traps (.XSSimple "break bottomed out", s0, .Done) with
    | .ok t => .ok t
    | .error msg => .ok
        ( .XSSimple ("internal check_traps error: " ++ msg)
        , fail_with msg s0
        , .Done
        )


  | .Continue _n =>
    match check_traps (.XSSimple "continue bottomed out", s0, .Done) with
    | .ok t => .ok t
    | .error msg => .ok
        ( .XSSimple ("internal check_traps error: " ++ msg)
        , fail_with msg s0
        , .Done
        )


  | .Return =>
    match check_traps (.XSSimple "return bottomed out", s0, .Done) with
    | .ok t => .ok t
    | .error msg => .ok
        ( .XSSimple ("internal check_traps error: " ++ msg)
        , fail_with msg s0
        , .Done
        )


  | .Exit =>
    let (s1, m_cmd) := exit_trap s0
    match m_cmd with
    | none =>
        .ok (.XSSimple "exited", exit s1, .Done)
    | some cmd =>
        .ok (.XSSimple "trapped on exit", s1, .Semi cmd .Exit)

  | .Done =>
    match check_traps (.XSSimple "", s0, .Done) with
    | .ok t => .ok t
    | .error msg => .ok
        ( .XSSimple ("internal check_traps error: " ++ msg)
        , fail_with msg s0
        , .Done
        )

  partial def full_evaluation {α : Type u} [OS α]
      (os0 : os_state α) (stmt0 : stmt) : Except String (os_state α) :=
    if out_of_fuel os0 then
      .ok os0
    else
      let os1 := tick os0
      match stmt0 with
      | .Done => .ok os1
      | _ =>
        match step_eval os1 .Unchecked stmt0 with
        | .error msg => .error msg
        | .ok (step, os2, stmt1) =>
          full_evaluation (log_step step os2) stmt1

  partial def eval {α : Type u} [OS α]
      (os0 : os_state α) (stmt0 : stmt) : Except String Int :=
    match full_evaluation os0 stmt0 with
    | .error msg => .error msg
    | .ok os1 =>
      match full_evaluation os1 .Exit with
      | .error msg => .error msg
      | .ok os2 => .ok os2.sh.exit_code

end

end Expand
open Expand
/-- Lem: symbolic_run_full_expansion
    Unbounded, for tests: run step_expansion until ExpError/ExpDone,
    returning the final fields (either error payload or success payload). -/
partial def symbolic_run_full_expansion
    (os0 : os_state symbolic) (st0 : expansion_state) :
    os_state symbolic × fields :=
  match st0 with
  | .ExpError f => (os0, f)
  | .ExpDone  f => (os0, f)
  | _ =>
      match step_expansion (os0, st0) with
      | .error msg =>
          -- 这里 Lem 版本不会抛异常；为了测试函数“能跑到底”，我选择把内部错误映射成 ExpError 的结果
          -- 你也可以改成 (os0, [symbolic_string_of_string msg]) 等你 fields 的构造。
          (os0, [symbolic_string_of_string msg])
      | .ok (_step, os1, st1) =>
          symbolic_run_full_expansion os1 st1

/-- Lem: symbolic_full_expansion -/
def symbolic_full_expansion (s0 : os_state symbolic) (w0 : words) :
    os_state symbolic × fields :=
  symbolic_run_full_expansion s0 (.ExpStart { splitting := .Split, globbing := true } w0)

/-- Lem: try_step_pid -/
def try_step_pid (os0 : os_state symbolic) (pid : pid) :
    os_state symbolic × Option evaluation_step :=
  let (os1, res) := symbolic_step_pid step_eval os0 pid
  match res with
  | none                 => (os1, none)
  | some (.ok _ec)   => (os1, none)
  | some (.error step)  => (os1, some step)

/-- Lem: try_step_all_loop -/
partial def try_step_all_loop
    (os0 : os_state symbolic) (p : pid) (max_pid : pid)
    (steps : List (Option evaluation_step)) :
    os_state symbolic × List (Option evaluation_step) :=
  if p >= max_pid then
    (os0, steps.reverse)
  else
    let (os1, res) := symbolic_step_pid step_eval os0 p
    let step : Option evaluation_step :=
      match res with
      | none                => none
      | some (.ok _ec)  => none
      | some (.error st)   => some st
    try_step_all_loop os1 (p + 1) max_pid (step :: steps)

/-- Lem: try_step_all -/
def try_step_all (os0 : os_state symbolic) :
    os_state symbolic × List (Option evaluation_step) :=
  try_step_all_loop os0 0 (List.length os0.symbolic.procs) []

/-- Lem: run_trace_evaluation_loop -/
partial def run_trace_evaluation_loop
    (os0 : os_state symbolic) :
    evaluation_trace × os_state symbolic :=
  if out_of_fuel os0 then
    ( [(.XSStep "out of fuel", os0.sh, os0.symbolic, proc_stmt os0 0)]
    , os0
    )
  else
    let os1 := tick os0
    let (os2, steps) := try_step_all os1
    -- make sure we're back in pid 0 (root shell)
    let (os3, _sproc) := proc_select os2 0
    if steps.all (fun ms => ms.isNone) then
      ([], os3)
    else
      let m_step0 := steps.head?   -- Option (Option evaluation_step)
      let step0 : evaluation_step :=
        match m_step0 with
        | some (some st) => st
        | _              => .XSSimple "no step in root shell"
      let entry := (step0, os3.sh, os3.symbolic, proc_stmt os3 0)
      let (trace, os4) := run_trace_evaluation_loop os2
      (entry :: trace, os4)

/-- Lem: run_trace_evaluation -/
def run_trace_evaluation (os0 : os_state symbolic) (stmt : stmt) :
    evaluation_trace :=
  let os1 := proc_set_stmt os0 0 stmt
  (run_trace_evaluation_loop os1).1

/-- Lem: symbolic_full_evaluation -/
def symbolic_full_evaluation (s0 : os_state symbolic) (c : stmt) :
    os_state symbolic :=
  (run_trace_evaluation_loop (proc_set_stmt s0 0 c)).2

-- convenience functions for shell.ml (Lean side)
-- open import Os_system
-- def real_eval (os0 : os_state system) (c : stmt) : os_state system :=
--   full_evaluation os0 c

-- def real_eval_for_exit_code (os0 : os_state system) (c : stmt) : Nat :=
--   eval os0 c


end Smoosh
