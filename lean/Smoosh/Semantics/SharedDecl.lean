import Smoosh.Smoosh
import Smoosh.Fields
import Smoosh.Arith
import Smoosh.Pattern
import Smoosh.Command.All

open Smoosh

namespace Smoosh

/- Lem: string_mode type -/
inductive string_mode where
  | UserString
  | GeneratedString
deriving DecidableEq, Repr

/-- Lem: quoting_mode type -/
inductive quoting_mode where
  | Unquoted
  | Quoted
deriving DecidableEq, Repr

/-- Lem: type redir_exp_result type -/
inductive redir_exp_result (α : Type u) where
  | REDone  : α → expanded_redir → redir_exp_result α
  | REError : fields → redir_exp_result α
  | REStep  : expansion_step → α → expanding_redir → redir_exp_result α
deriving Inhabited

end Smoosh
