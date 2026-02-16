/-
  Smoosh.Signal — Signal types and helpers
  Translated from `signal.lem` and `signal_platform.lem`.

  Defines the `Signal` enumeration, string/integer conversions, and default signal behaviors.
  `signal_of_ocaml_signal` (reverse platform-int lookup) is not translated.
-/
import Smoosh.Num

/-! # Signal type -/

inductive Signal where
  | EXIT    -- shell only, for trap
  | SIGABRT
  | SIGALRM
  | SIGBUS
  | SIGCHLD
  | SIGCONT
  | SIGFPE
  | SIGHUP
  | SIGILL
  | SIGINT
  | SIGKILL
  | SIGPIPE
  | SIGQUIT
  | SIGSEGV
  | SIGSTOP
  | SIGTERM
  | SIGTSTP
  | SIGTTIN
  | SIGTTOU
  | SIGUSR1
  | SIGUSR2
  | SIGTRAP
  | SIGURG
  | SIGXCPU
  | SIGXFSZ
  deriving Repr, BEq, Hashable, Ord, Inhabited, DecidableEq

/-- Ref: signal.lem:all_signals — Complete list of all `Signal` constructors. -/
def Signal.allSignals : List Signal :=
  [ .EXIT, .SIGABRT, .SIGALRM, .SIGBUS, .SIGCHLD, .SIGCONT, .SIGFPE,
    .SIGHUP, .SIGILL, .SIGINT, .SIGKILL, .SIGPIPE, .SIGQUIT, .SIGSEGV,
    .SIGSTOP, .SIGTERM, .SIGTSTP, .SIGTTIN, .SIGTTOU, .SIGUSR1, .SIGUSR2,
    .SIGTRAP, .SIGURG, .SIGXCPU, .SIGXFSZ ]

/-- Ref: signal.lem:undefined_traps — Signals that cannot be trapped (KILL, STOP). -/
def Signal.undefinedTraps : List Signal :=
  [.SIGKILL, .SIGSTOP]

/-- Ref: signal.lem:stopped_signals — Signals indicating a stopped process. -/
def Signal.stoppedSignals : List Signal :=
  [.SIGTSTP, .SIGSTOP, .SIGTTIN, .SIGTTOU]

/-! # String <-> Signal conversion -/

/-- Ref: signal.lem:string_of_signal — Convert signal to short name (e.g., `SIGINT` → `"INT"`). -/
def Signal.toString : Signal → String
  | .EXIT    => "EXIT"
  | .SIGABRT => "ABRT"
  | .SIGALRM => "ALRM"
  | .SIGBUS  => "BUS"
  | .SIGCHLD => "CHLD"
  | .SIGCONT => "CONT"
  | .SIGFPE  => "FPE"
  | .SIGHUP  => "HUP"
  | .SIGILL  => "ILL"
  | .SIGINT  => "INT"
  | .SIGKILL => "KILL"
  | .SIGPIPE => "PIPE"
  | .SIGQUIT => "QUIT"
  | .SIGSEGV => "SEGV"
  | .SIGSTOP => "STOP"
  | .SIGTERM => "TERM"
  | .SIGTSTP => "TSTP"
  | .SIGTTIN => "TTIN"
  | .SIGTTOU => "TTOU"
  | .SIGUSR1 => "USR1"
  | .SIGUSR2 => "USR2"
  | .SIGTRAP => "TRAP"
  | .SIGURG  => "URG"
  | .SIGXCPU => "XCPU"
  | .SIGXFSZ => "XFSZ"

instance : Std.ToFormat Signal where
  format s := s.toString

/-- Ref: signal_platform.lem:uppercase_char — Convert lowercase letter to uppercase. -/
def uppercaseChar (c : Char) : Char :=
  if 'a' ≤ c && c ≤ 'z' then Char.ofNat (c.toNat - 32) else c

/-- Ref: signal.lem:signal_of_string — Parse signal name (case-insensitive, optional SIG prefix). -/
def Signal.ofString (s : String) : Option Signal :=
  -- Convert to uppercase, remove SIG prefix
  let s' := String.ofList (s.toList.map uppercaseChar)
  let s'' :=
    match s'.toList with
    | 'S' :: 'I' :: 'G' :: rest => String.ofList rest
    | _ => s'
  match s'' with
  | "EXIT" => some .EXIT
  | "ABRT" => some .SIGABRT
  | "ALRM" => some .SIGALRM
  | "BUS"  => some .SIGBUS
  | "CHLD" => some .SIGCHLD
  | "CONT" => some .SIGCONT
  | "FPE"  => some .SIGFPE
  | "HUP"  => some .SIGHUP
  | "ILL"  => some .SIGILL
  | "INT"  => some .SIGINT
  | "KILL" => some .SIGKILL
  | "PIPE" => some .SIGPIPE
  | "QUIT" => some .SIGQUIT
  | "SEGV" => some .SIGSEGV
  | "STOP" => some .SIGSTOP
  | "TERM" => some .SIGTERM
  | "TSTP" => some .SIGTSTP
  | "TTIN" => some .SIGTTIN
  | "TTOU" => some .SIGTTOU
  | "USR1" => some .SIGUSR1
  | "USR2" => some .SIGUSR2
  | "TRAP" => some .SIGTRAP
  | "URG"  => some .SIGURG
  | "XCPU" => some .SIGXCPU
  | "XFSZ" => some .SIGXFSZ
  | _ => none

/-! # Platform signal numbers (stubbed) -/

/-- Ref: signal_platform.lem:ocaml_signal_of_signal — Map signal to platform (Linux) signal number. -/
def Signal.platformInt : Signal → Nat
  | .EXIT    => 0
  | .SIGHUP  => 1
  | .SIGINT  => 2
  | .SIGQUIT => 3
  | .SIGILL  => 4
  | .SIGTRAP => 5
  | .SIGABRT => 6
  | .SIGBUS  => 7
  | .SIGFPE  => 8
  | .SIGKILL => 9
  | .SIGUSR1 => 10
  | .SIGSEGV => 11
  | .SIGUSR2 => 12
  | .SIGPIPE => 13
  | .SIGALRM => 14
  | .SIGTERM => 15
  | .SIGCHLD => 17
  | .SIGCONT => 18
  | .SIGSTOP => 19
  | .SIGTSTP => 20
  | .SIGTTIN => 21
  | .SIGTTOU => 22
  | .SIGURG  => 23
  | .SIGXCPU => 24
  | .SIGXFSZ => 25

/-! # Signal default behavior -/

inductive SignalBehavior where
  | terminate (additionalActions : Bool)  -- T = false, A = true
  | ignore                                -- I
  | stop                                  -- S
  | continue_                             -- C
  deriving Repr, BEq

/-- Ref: signal.lem:signal_default_behavior — POSIX default disposition for each signal. -/
def Signal.defaultBehavior : Signal → SignalBehavior
  | .EXIT    => .ignore
  | .SIGABRT => .terminate true
  | .SIGALRM => .terminate false
  | .SIGBUS  => .terminate true
  | .SIGCHLD => .ignore
  | .SIGCONT => .continue_
  | .SIGFPE  => .terminate true
  | .SIGHUP  => .terminate false
  | .SIGILL  => .terminate true
  | .SIGINT  => .terminate false
  | .SIGKILL => .terminate false
  | .SIGPIPE => .terminate false
  | .SIGQUIT => .terminate true
  | .SIGSEGV => .terminate true
  | .SIGSTOP => .stop
  | .SIGTERM => .terminate false
  | .SIGTSTP => .stop
  | .SIGTTIN => .stop
  | .SIGTTOU => .stop
  | .SIGUSR1 => .terminate false
  | .SIGUSR2 => .terminate false
  | .SIGTRAP => .terminate true
  | .SIGURG  => .ignore
  | .SIGXCPU => .terminate true
  | .SIGXFSZ => .terminate true
