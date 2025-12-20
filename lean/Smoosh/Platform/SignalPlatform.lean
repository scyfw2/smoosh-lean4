namespace Smoosh.Platform

inductive Signal where
  | sigint | sigterm | sigkill | sighup
  deriving DecidableEq, Repr

/-- Platform-specific signal number. Stub for now. -/
def platformIntOfSignal : Signal → Nat
  | .sigint => 2
  | .sighup => 1
  | .sigterm => 15
  | .sigkill => 9

end Smoosh.Platform
