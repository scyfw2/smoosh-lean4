import Smoosh.Compat.PervasivesExtra
import Smoosh.BuildInfo
import Smoosh.Platform.SignalPlatform
import Smoosh.Prelude.FilePerm

namespace Smoosh

inductive substring_mode where
  | Shortest
  | Longest
  deriving DecidableEq, Repr

inductive substring_side where
  | Prefix
  | Suffix
  deriving DecidableEq, Repr

end Smoosh
