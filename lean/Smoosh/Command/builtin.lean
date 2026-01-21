import Smoosh.Smoosh
import Smoosh.Fields
import Smoosh.Test

universe u

open Smoosh
/-
NB that special builtins have to return the restore_redirs bool,
but it'll automatically get set to true for everything else. all
of this is a bunch of silliness to properly allow exec its two
(rather different) behaviors
-/

/-- Lem: val is_special_builtin : string -> bool -/
def is_special_builtin (s : String) : Bool :=
  List.elem s
    [ "break", ":", "continue", ".", "eval", "exec", "exit", "export", "local", "readonly"
    , "return", "set", "shift", "source", "times", "trap", "unset"
    ]

/-- Lem: val is_builtin : string -> bool -/
def is_builtin (s : String) : Bool :=
  List.elem s
    [ "[", "alias", "bg", "cd", "command", "echo", "false", "fc", "fg"
    , "getopts", "hash", "help", "jobs", "kill" -- "newgrp" (disabled)
    , "printf", "pwd", "read", "test", "true", "type", "ulimit", "umask", "unalias"
    , "wait"
    ]

/-- Lem: val builtin_names : list string -/
def builtin_names : List String :=
  [ "."
  , ":"
  , "["
  , "alias"
  , "bg"
  , "break"
  , "cd"
  , "command"
  , "continue"
  , "echo"
  , "eval"
  , "exec"
  , "exit"
  , "export"
  , "false"
  , "fc"
  , "fg"
  , "getopts"
  , "hash"
  , "history"
  , "jobs"
  , "kill"
  , "local"
  -- , "newgrp"   -- use command
  , "printf"
  , "pwd"
  , "read"
  , "readonly"
  , "return"
  , "set"
  , "shift"
  , "test"
  , "times"
  , "trap"
  , "true"
  , "type"
  -- , "ulimit"   -- unimpl
  , "umask"
  , "unalias"
  , "unset"
  , "wait"
  ]

/- INVARIANT: uncomment the ones that we actually implement -/
/-- Lem: val is_unspecified_utility : string -> bool -/
def is_unspecified_utility (s : String) : Bool :=
  List.elem s
    [ "alloc", "autoload", "bind", "bindkey", "builtin", "bye", "caller", "cap"
    , "chdir", "clone", "comparguments", "compcall", "compctl", "compdescribe"
    , "compfiles", "compgen", "compgroups", "complete", "compquote", "comptags"
    , "comptry", "compvalues", "declare", "dirs", "disable", "disown", "dosh"
    , "echotc", "echoti"
    -- , "help"
    -- , "history"
    , "hist"
    , "let"
    -- , "local"
    , "login"
    , "logout", "map", "mapfile", "popd", "print", "pushd", "readarray", "repeat"
    , "savehistory", "source", "shopt", "stop", "suspend", "typeset", "whence"
    ]

/-- Lem: builtin_unimplemented -/
def builtin_unimplemented {α : Type u} (s0 : os_state α) (_argv : fields) (_env : env) :
  Except (os_state α × String) (os_state α × stmt × Bool) :=
  .error (s0, "unimplemented")

/-- drop the `restore : Bool` flag -/
def drop_restore {α : Type u} :
    Except (os_state α × String) (os_state α × stmt × Bool) →
    Except (os_state α × String) (os_state α × stmt)
  | .error e          => .error e
  | .ok (s, st, _rr)  => .ok (s, st)
