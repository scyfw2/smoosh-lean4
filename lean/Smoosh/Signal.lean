import Smoosh.Platform.SignalPlatform

namespace Smoosh

/-- Public signal type (facade). -/
abbrev Signal := Platform.Signal

-- Re-export constructors under `Smoosh.Signal.*`

namespace Signal
abbrev sigint  : Signal := Platform.Signal.sigint
abbrev sighup  : Signal := Platform.Signal.sighup
abbrev sigterm : Signal := Platform.Signal.sigterm
abbrev sigkill : Signal := Platform.Signal.sigkill
end Signal

/-- Public accessor for platform signal numbers. -/
abbrev platformIntOfSignal : Signal → Nat :=
  Platform.platformIntOfSignal

end Smoosh
