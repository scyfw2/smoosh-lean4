/-
  Smoosh.Signal — Signal types and helpers
  Translated from signal.lem
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

def Signal.allSignals : List Signal :=
  [ .EXIT, .SIGABRT, .SIGALRM, .SIGBUS, .SIGCHLD, .SIGCONT, .SIGFPE,
    .SIGHUP, .SIGILL, .SIGINT, .SIGKILL, .SIGPIPE, .SIGQUIT, .SIGSEGV,
    .SIGSTOP, .SIGTERM, .SIGTSTP, .SIGTTIN, .SIGTTOU, .SIGUSR1, .SIGUSR2,
    .SIGTRAP, .SIGURG, .SIGXCPU, .SIGXFSZ ]

def Signal.undefinedTraps : List Signal :=
  [.SIGKILL, .SIGSTOP]

def Signal.stoppedSignals : List Signal :=
  [.SIGTSTP, .SIGSTOP, .SIGTTIN, .SIGTTOU]

/-! # String <-> Signal conversion -/

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

def uppercaseChar (c : Char) : Char :=
  if 'a' ≤ c && c ≤ 'z' then Char.ofNat (c.toNat - 32) else c

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
