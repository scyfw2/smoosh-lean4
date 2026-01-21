import Smoosh.Compat.PervasivesExtra
import Smoosh.BuildInfo
import Smoosh.Platform.SignalPlatform

namespace Smoosh

/-- Lem: redir_type type -/
inductive redir_type where
  | To | Clobber | From | FromTo | Append
  deriving DecidableEq, Repr

/-- Lem: dup_type type -/
inductive dup_type where
  | ToFD | FromFD
  deriving DecidableEq, Repr

/-- Lem: heredoc: Here = quoted (no expansion); XHere = unquoted (do expansion) -/
inductive heredoc_type where
  | Here | XHere
  deriving DecidableEq, Repr

/-- Lem: orig_fd_action type -/
inductive orig_fd_action where
  | CloseOrig | LeaveOrig
  deriving DecidableEq, Repr

/-- Lem: should_close_orig : orig_fd_action -> bool -/
def should_close_orig : orig_fd_action → Bool
  | .CloseOrig => true
  | .LeaveOrig => false

end Smoosh
