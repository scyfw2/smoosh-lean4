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
import Smoosh.Version

namespace Smoosh
open Smoosh
/-
Lem:
val getppid : unit -> pid
declare ocaml target_rep function getppid = `Unix.getppid`
-/

opaque getppid : Unit → pid

-- Lem: local_opts_default
def local_opts_default : local_opts :=
  { local_readonly := false
    local_exported := false }

-- Lem: env_default
def env_default : env :=
  Map.fromList
    [ ("OPTIND", symbolic_string_of_string "1")
    , ("PPID", symbolic_string_of_nat (getppid ()))
    , ("SMOOSH_VERSION", symbolic_string_of_string Version.smoosh_version)
    , ("SMOOSH_BUILD", symbolic_string_of_string Version.smoosh_build)
    ]

-- Lem: default_shell_state
def default_shell_state : shell_state :=
  { rootpid := 0
    outermost := true
    opts := Set.Set.empty
    traps := Map.empty
    supershell_traps := none
    jobs := []
    exit_code := 0
    last_pid := none
    positional_params := [symbolic_string_of_string "smoosh"]  -- $0, $1, $2, ...
    env := env_default
    locals := []
    optoff := none
    readonly := Set.Set.empty
    exported := Set.Set.empty
    funcs := Map.empty
    aliases := Map.empty
    cwd := "/"
    locale := lc_ambient
    loop_nest := 0
    history := []
    hashes := Map.empty
  }

end Smoosh
