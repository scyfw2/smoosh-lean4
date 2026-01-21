import Smoosh.Compat.PervasivesExtra
import Smoosh.BuildInfo
import Smoosh.Platform.SignalPlatform
import Smoosh.Prelude.FilePerm

namespace Smoosh

/-- Lem: trace_tag -/
inductive trace_tag where
  | Trace_symbolic
  | Trace_syscall
  | Trace_traps
  | Trace_undef
  | Trace_unspec
  deriving DecidableEq, Repr

/-- Lem: string_of_trace_tag : trace_tag -> string -/
def string_of_trace_tag : trace_tag → String
  | .Trace_symbolic => "symbolic"
  | .Trace_syscall  => "syscall"
  | .Trace_traps    => "traps"
  | .Trace_undef    => "undef"
  | .Trace_unspec   => "unspec"

/-- Lem: trace_tag_of_string : string -> maybe trace_tag -/
def trace_tag_of_string : String → Option trace_tag
  | "symbolic" => some .Trace_symbolic
  | "syscall"  => some .Trace_syscall
  | "traps"    => some .Trace_traps
  | "undef"    => some .Trace_undef
  | "unspec"   => some .Trace_unspec
  | _          => none

/-- Lem: all_trace_tags : list trace_tag -/
def all_trace_tags : List trace_tag :=
  sortBy (fun t1 t2 => string_of_trace_tag t1 <= string_of_trace_tag t2)
    [ .Trace_symbolic
    , .Trace_syscall
    , .Trace_traps
    , .Trace_undef
    , .Trace_unspec
    ]

/-- Lem: sh_opt type -/
inductive sh_opt where
  | Sh_allexport
  | Sh_errexit
  | Sh_ignoreeof
  | Sh_earlyhash
  | Sh_interactive
  | Sh_monitor
  | Sh_noclobber
  | Sh_noglob
  | Sh_noexec
  | Sh_nolog
  | Sh_notify
  | Sh_nounset
  | Sh_verbose
  | Sh_vi
  | Sh_xtrace
  | Sh_nonlexicalctrl
  | Sh_trace (tag : trace_tag)
deriving DecidableEq, Repr

/-- Lem: string_of_sh_opt type -/
def string_of_sh_opt : sh_opt → String
  | .Sh_allexport      => "allexport"
  | .Sh_errexit        => "errexit"
  | .Sh_ignoreeof      => "ignoreeof"
  | .Sh_earlyhash      => "earlyhash"
  | .Sh_interactive    => "interactive"
  | .Sh_monitor        => "monitor"
  | .Sh_noclobber      => "noclobber"
  | .Sh_noglob         => "noglob"
  | .Sh_noexec         => "noexec"
  | .Sh_nolog          => "nolog"
  | .Sh_notify         => "notify"
  | .Sh_nounset        => "nounset"
  | .Sh_verbose        => "verbose"
  | .Sh_vi             => "vi"
  | .Sh_xtrace         => "xtrace"
  | .Sh_nonlexicalctrl => "nonlexicalctrl"
  | .Sh_trace tag      => "trace" ++ string_of_trace_tag tag

/-- Lem: char_of_sh_opt type -/
def char_of_sh_opt : sh_opt → Option Char
  | .Sh_allexport      => some 'a'
  | .Sh_errexit        => some 'e'
  | .Sh_ignoreeof      => none
  | .Sh_earlyhash      => some 'h'
  | .Sh_interactive    => some 'i'
  | .Sh_monitor        => some 'm'
  | .Sh_noclobber      => some 'C'
  | .Sh_noglob         => some 'f'
  | .Sh_noexec         => some 'n'
  | .Sh_nolog          => none
  | .Sh_notify         => some 'b'
  | .Sh_nounset        => some 'u'
  | .Sh_verbose        => some 'v'
  | .Sh_vi             => none
  | .Sh_xtrace         => some 'x'
  | .Sh_nonlexicalctrl => none
  | .Sh_trace _        => none

/-- Lem: sh_opt_of_shortopt -/
def sh_opt_of_shortopt : Char → Option sh_opt
  | 'a' => some .Sh_allexport
  | 'b' => some .Sh_notify
  | 'C' => some .Sh_noclobber
  | 'e' => some .Sh_errexit
  | 'f' => some .Sh_noglob
  | 'h' => some .Sh_earlyhash
  | 'm' => some .Sh_monitor
  | 'n' => some .Sh_noexec
  | 'u' => some .Sh_nounset
  | 'v' => some .Sh_verbose
  | 'x' => some .Sh_xtrace
  | _   => none

/-- Lem: sh_opt_of_longopt -/
def sh_opt_of_longopt (lo : String) : Option sh_opt :=
  match lo with
  | "allexport"      => some .Sh_allexport
  | "errexit"        => some .Sh_errexit
  | "ignoreeof"      => some .Sh_ignoreeof
  | "monitor"        => some .Sh_monitor
  | "noclobber"      => some .Sh_noclobber
  | "noglob"         => some .Sh_noglob
  | "noexec"         => some .Sh_noexec
  | "nolog"          => some .Sh_nolog
  | "notify"         => some .Sh_notify
  | "nounset"        => some .Sh_nounset
  | "verbose"        => some .Sh_verbose
  | "vi"             => some .Sh_vi
  | "xtrace"         => some .Sh_xtrace
  | "nonlexicalctrl" => some .Sh_nonlexicalctrl
  | _ =>
      let cs := toCharList lo
      match cs with
      | 't' :: 'r' :: 'a' :: 'c' :: 'e' :: tag_cs =>
          match trace_tag_of_string (charsToString tag_cs) with
          | none => none
          | some tag => some (.Sh_trace tag)
      | _ => none

/-- Lem: all_sh_opts type -/
def all_sh_opts : List sh_opt :=
  sortBy (fun o1 o2 => string_of_sh_opt o1 <= string_of_sh_opt o2)
    ( [ .Sh_allexport
      , .Sh_errexit
      , .Sh_ignoreeof
      , .Sh_earlyhash
      , .Sh_interactive
      , .Sh_monitor
      , .Sh_noclobber
      , .Sh_noglob
      , .Sh_noexec
      , .Sh_errexit
      , .Sh_nolog
      , .Sh_notify
      , .Sh_nounset
      , .Sh_verbose
      , .Sh_vi
      , .Sh_xtrace
      , .Sh_nonlexicalctrl
      ] ++ (all_trace_tags.map sh_opt.Sh_trace) )

def unimplemented_sh_opts : List sh_opt :=
  [ .Sh_vi ]

/-
(**********************************************************************)
(* Other modes, options, and flags ************************************)
(**********************************************************************)
(* NB we write custom tester functions with complete pattern matches
   rather than using equality tests so that we can freely add cases
   without having to worry about introducing logic bugs *)
-/

/-- Lem: command_opts type -/
structure command_opts where
  ran_cmd_subst : Bool
  should_fork : Bool
  force_simple_command : Bool
  deriving Repr, DecidableEq

/-- Lem: splitting_mode type -/
inductive splitting_mode where
  | Split | NoSplit
  deriving Repr, DecidableEq

/-- Lem: should_split -/
def should_split : splitting_mode → Bool
  | .Split   => true
  | .NoSplit => false

/-- Lem: expansion_opts type -/
structure expansion_opts where
  splitting : splitting_mode
  globbing : Bool
  deriving Repr, DecidableEq

/-- Lem: bg_mode type -/
inductive bg_mode where
  | FG | BG
  deriving Repr, DecidableEq

/-- Lem: is_fg : bg_mode -> bool -/
def is_fg : bg_mode → Bool
  | .BG => false
  | .FG => true

/-- Lem: is_bg : bg_mode -> bool -/
def is_bg : bg_mode → Bool
  | .BG => true
  | .FG => false

/-- Lem: interactivity_mode type -/
inductive interactivity_mode where
  | Interactive | Noninteractive
  deriving Repr, DecidableEq

/-- Lem: is_interactive_mode : interactivity_mode -> bool -/
def is_interactive_mode : interactivity_mode → Bool
  | .Interactive    => true
  | .Noninteractive => false

/-- Lem: shell_level type -/
inductive shell_level where
  | Toplevel | Subsidiary
  deriving Repr, DecidableEq

/-- Lem: is_toplevel : shell_level -> bool -/
def is_toplevel : shell_level → Bool
  | .Toplevel   => true
  | .Subsidiary => false

/-- Lem: binsh_mode type -/
inductive binsh_mode where
  | TryBinSh | NoBinSh
  deriving Repr, DecidableEq

/-- Lem: try_binsh : binsh_mode -> bool -/
def try_binsh : binsh_mode → Bool
  | .TryBinSh => true
  | .NoBinSh  => false

/-- Lem: checking_mode type -/
inductive checking_mode where
  | Checked | Unchecked
  deriving Repr, DecidableEq

/-- Lem: checked_exit : checking_mode -> bool -/
def checked_exit : checking_mode → Bool
  | .Checked   => true
  | .Unchecked => false

/-- Lem: wait_mode type -/
inductive wait_mode where
  | WaitCommand | WaitInternal
  deriving Repr, DecidableEq

/-- Lem: from_wait_command : wait_mode -> bool -/
def from_wait_command : wait_mode → Bool
  | .WaitCommand  => true
  | .WaitInternal => false

end Smoosh
