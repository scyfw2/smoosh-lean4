namespace Smoosh

/-
  Lem:
    val uppercase_char : char -> char
    declare ocaml target_rep function uppercase_char = `Char.uppercase_ascii`
-/
def uppercaseChar (c : Char) : Char :=
  let n := c.toNat
  let a := ('a'.toNat)
  let z := ('z'.toNat)
  if a ≤ n ∧ n ≤ z then
    -- ASCII: 'a'..'z' -> 'A'..'Z' by subtracting 32
    Char.ofNat (n - 32)
  else
    c

/-- Lem: signal type -/
inductive signal where
  | EXIT
  | SIGABRT | SIGALRM | SIGBUS | SIGCHLD | SIGCONT | SIGFPE | SIGHUP | SIGILL | SIGINT
  | SIGKILL | SIGPIPE | SIGQUIT | SIGSEGV | SIGSTOP | SIGTERM | SIGTSTP | SIGTTIN | SIGTTOU
  | SIGUSR1 | SIGUSR2 | SIGTRAP | SIGURG | SIGXCPU | SIGXFSZ
  deriving DecidableEq, Repr, Inhabited

open signal

/-- Lem: all_signals types -/
def all_signals : List signal :=
  [ EXIT
  , SIGABRT
  , SIGALRM
  , SIGBUS
  , SIGCHLD
  , SIGCONT
  , SIGFPE
  , SIGHUP
  , SIGILL
  , SIGINT
  , SIGKILL
  , SIGPIPE
  , SIGQUIT
  , SIGSEGV
  , SIGSTOP
  , SIGTERM
  , SIGTSTP
  , SIGTTIN
  , SIGTTOU
  , SIGUSR1
  , SIGUSR2
  , SIGTRAP
  , SIGURG
  , SIGXCPU
  , SIGXFSZ
  ]

/-- Lem: undefined_traps type -/
def undefined_traps : List signal :=
  [ SIGKILL, SIGSTOP ]

/-- Lem: stopped_signals type -/
def stopped_signals : List signal :=
  [ SIGTSTP, SIGSTOP, SIGTTIN, SIGTTOU ]

/-- Lem: string_of_signal : signal -> string -/
def string_of_signal : signal → String
  | EXIT    => "EXIT"
  | SIGABRT => "ABRT"
  | SIGALRM => "ALRM"
  | SIGBUS  => "BUS"
  | SIGCHLD => "CHLD"
  | SIGCONT => "CONT"
  | SIGFPE  => "FPE"
  | SIGHUP  => "HUP"
  | SIGILL  => "ILL"
  | SIGINT  => "INT"
  | SIGKILL => "KILL"
  | SIGPIPE => "PIPE"
  | SIGQUIT => "QUIT"
  | SIGSEGV => "SEGV"
  | SIGSTOP => "STOP"
  | SIGTERM => "TERM"
  | SIGTSTP => "TSTP"
  | SIGTTIN => "TTIN"
  | SIGTTOU => "TTOU"
  | SIGUSR1 => "USR1"
  | SIGUSR2 => "USR2"
  | SIGTRAP => "TRAP"
  | SIGURG  => "URG"
  | SIGXCPU => "XCPU"
  | SIGXFSZ => "XFSZ"

def normalizeSignalName (s : String) : String :=
  let cs := s.toList.map uppercaseChar
  match cs with
  | 'S' :: 'I' :: 'G' :: rest => String.ofList rest
  | _                         => String.ofList cs

/-- Lem: signal_of_string : string -> maybe signal -/
def signal_of_string (s : String) : Option signal :=
  let s' := normalizeSignalName s
  match s' with
  | "EXIT" => some EXIT
  | "ABRT" => some SIGABRT
  | "ALRM" => some SIGALRM
  | "BUS"  => some SIGBUS
  | "CHLD" => some SIGCHLD
  | "CONT" => some SIGCONT
  | "FPE"  => some SIGFPE
  | "HUP"  => some SIGHUP
  | "ILL"  => some SIGILL
  | "INT"  => some SIGINT
  | "KILL" => some SIGKILL
  | "PIPE" => some SIGPIPE
  | "QUIT" => some SIGQUIT
  | "SEGV" => some SIGSEGV
  | "STOP" => some SIGSTOP
  | "TERM" => some SIGTERM
  | "TSTP" => some SIGTSTP
  | "TTIN" => some SIGTTIN
  | "TTOU" => some SIGTTOU
  | "USR1" => some SIGUSR1
  | "USR2" => some SIGUSR2
  | "TRAP" => some SIGTRAP
  | "URG"  => some SIGURG
  | "XCPU" => some SIGXCPU
  | "XFSZ" => some SIGXFSZ
  | _      => none

namespace SignalPlatform

/-
val ocaml_sigabrt   : int
declare ocaml target_rep function ocaml_sigabrt = `Sys.sigabrt`
val ocaml_sigalrm   : int
declare ocaml target_rep function ocaml_sigalrm = `Sys.sigalrm`
val ocaml_sigbus    : int
declare ocaml target_rep function ocaml_sigbus = `Sys.sigbus`
val ocaml_sigchld   : int
declare ocaml target_rep function ocaml_sigchld = `Sys.sigchld`
val ocaml_sigcont   : int
declare ocaml target_rep function ocaml_sigcont = `Sys.sigcont`
val ocaml_sigfpe    : int
declare ocaml target_rep function ocaml_sigfpe = `Sys.sigfpe`
val ocaml_sighup    : int
declare ocaml target_rep function ocaml_sighup = `Sys.sighup`
val ocaml_sigill    : int
declare ocaml target_rep function ocaml_sigill = `Sys.sigill`
val ocaml_sigint    : int
declare ocaml target_rep function ocaml_sigint = `Sys.sigint`
val ocaml_sigkill   : int
declare ocaml target_rep function ocaml_sigkill = `Sys.sigkill`
val ocaml_sigpipe   : int
declare ocaml target_rep function ocaml_sigpipe = `Sys.sigpipe`
val ocaml_sigquit   : int
declare ocaml target_rep function ocaml_sigquit = `Sys.sigquit`
val ocaml_sigsegv   : int
declare ocaml target_rep function ocaml_sigsegv = `Sys.sigsegv`
val ocaml_sigstop   : int
declare ocaml target_rep function ocaml_sigstop = `Sys.sigstop`
val ocaml_sigterm   : int
declare ocaml target_rep function ocaml_sigterm = `Sys.sigterm`
val ocaml_sigtstp   : int
declare ocaml target_rep function ocaml_sigtstp = `Sys.sigtstp`
val ocaml_sigttin   : int
declare ocaml target_rep function ocaml_sigttin = `Sys.sigttin`
val ocaml_sigttou   : int
declare ocaml target_rep function ocaml_sigttou = `Sys.sigttou`
val ocaml_sigusr1   : int
declare ocaml target_rep function ocaml_sigusr1 = `Sys.sigusr1`
val ocaml_sigusr2   : int
declare ocaml target_rep function ocaml_sigusr2 = `Sys.sigusr2`
val ocaml_sigtrap   : int
declare ocaml target_rep function ocaml_sigtrap = `Sys.sigtrap`
val ocaml_sigurg    : int
declare ocaml target_rep function ocaml_sigurg = `Sys.sigurg`
val ocaml_sigxcpu   : int
declare ocaml target_rep function ocaml_sigxcpu = `Sys.sigxcpu`
val ocaml_sigxfsz   : int
declare ocaml target_rep function ocaml_sigxfsz = `Sys.sigxfsz`
-/
opaque ocaml_sigabrt : Int
opaque ocaml_sigalrm : Int
opaque ocaml_sigbus  : Int
opaque ocaml_sigchld : Int
opaque ocaml_sigcont : Int
opaque ocaml_sigfpe  : Int
opaque ocaml_sighup  : Int
opaque ocaml_sigill  : Int
opaque ocaml_sigint  : Int
opaque ocaml_sigkill : Int
opaque ocaml_sigpipe : Int
opaque ocaml_sigquit : Int
opaque ocaml_sigsegv : Int
opaque ocaml_sigstop : Int
opaque ocaml_sigterm : Int
opaque ocaml_sigtstp : Int
opaque ocaml_sigttin : Int
opaque ocaml_sigttou : Int
opaque ocaml_sigusr1 : Int
opaque ocaml_sigusr2 : Int
opaque ocaml_sigtrap : Int
opaque ocaml_sigurg  : Int
opaque ocaml_sigxcpu : Int
opaque ocaml_sigxfsz : Int

end SignalPlatform

open SignalPlatform

/-- Lem: ocaml_signal_of_signal : signal -> maybe int -/
def ocaml_signal_of_signal : signal → Option Int
  | .EXIT    => some 0
  | .SIGABRT => some ocaml_sigabrt
  | .SIGALRM => some ocaml_sigalrm
  | .SIGBUS  => some ocaml_sigbus
  | .SIGCHLD => some ocaml_sigchld
  | .SIGCONT => some ocaml_sigcont
  | .SIGFPE  => some ocaml_sigfpe
  | .SIGHUP  => some ocaml_sighup
  | .SIGILL  => some ocaml_sigill
  | .SIGINT  => some ocaml_sigint
  | .SIGKILL => some ocaml_sigkill
  | .SIGPIPE => some ocaml_sigpipe
  | .SIGQUIT => some ocaml_sigquit
  | .SIGSEGV => some ocaml_sigsegv
  | .SIGSTOP => some ocaml_sigstop
  | .SIGTERM => some ocaml_sigterm
  | .SIGTSTP => some ocaml_sigtstp
  | .SIGTTIN => some ocaml_sigttin
  | .SIGTTOU => some ocaml_sigttou
  | .SIGUSR1 => some ocaml_sigusr1
  | .SIGUSR2 => some ocaml_sigusr2
  | .SIGTRAP => some ocaml_sigtrap
  | .SIGURG  => some ocaml_sigurg
  | .SIGXCPU => some ocaml_sigxcpu
  | .SIGXFSZ => some ocaml_sigxfsz

def signalOfOcamlSignal? (ocamlSignal : Int) : Option signal :=
  if      ocamlSignal = ocaml_sigabrt then some SIGABRT
  else if ocamlSignal = ocaml_sigalrm then some SIGALRM
  else if ocamlSignal = ocaml_sigbus  then some SIGBUS
  else if ocamlSignal = ocaml_sigchld then some SIGCHLD
  else if ocamlSignal = ocaml_sigcont then some SIGCONT
  else if ocamlSignal = ocaml_sigfpe  then some SIGFPE
  else if ocamlSignal = ocaml_sighup  then some SIGHUP
  else if ocamlSignal = ocaml_sigill  then some SIGILL
  else if ocamlSignal = ocaml_sigint  then some SIGINT
  else if ocamlSignal = ocaml_sigkill then some SIGKILL
  else if ocamlSignal = ocaml_sigpipe then some SIGPIPE
  else if ocamlSignal = ocaml_sigquit then some SIGQUIT
  else if ocamlSignal = ocaml_sigsegv then some SIGSEGV
  else if ocamlSignal = ocaml_sigstop then some SIGSTOP
  else if ocamlSignal = ocaml_sigterm then some SIGTERM
  else if ocamlSignal = ocaml_sigtstp then some SIGTSTP
  else if ocamlSignal = ocaml_sigttin then some SIGTTIN
  else if ocamlSignal = ocaml_sigttou then some SIGTTOU
  else if ocamlSignal = ocaml_sigusr1 then some SIGUSR1
  else if ocamlSignal = ocaml_sigusr2 then some SIGUSR2
  else if ocamlSignal = ocaml_sigtrap then some SIGTRAP
  else if ocamlSignal = ocaml_sigurg  then some SIGURG
  else if ocamlSignal = ocaml_sigxcpu then some SIGXCPU
  else if ocamlSignal = ocaml_sigxfsz then some SIGXFSZ
  else none

-- val signal_of_ocaml_signal : int -> signal
def signal_of_ocaml_signal (ocamlSignal : Int) : signal :=
  match signalOfOcamlSignal? ocamlSignal with
  | some s => s
  | none   => panic! s!"unknown OCaml signal {ocamlSignal}"

/- from POSIX signal.h: default behaviors -/
inductive signal_behavior where
  | Terminate (additionalActions : Bool)  -- false = T, true = A
  | Ignore
  | Stop
  | Continue
  deriving DecidableEq, Repr

open signal_behavior

-- val signal_default_behavior : signal -> signal_behavior
def signal_default_behavior (sig : signal) : signal_behavior :=
  let T := Terminate false
  let A := Terminate true
  let I := Ignore
  let S := Stop
  let C := Continue
  match sig with
  | EXIT    => I  -- not really a signal, but okay
  | SIGABRT => A
  | SIGALRM => T
  | SIGBUS  => A
  | SIGCHLD => I
  | SIGCONT => C
  | SIGFPE  => A
  | SIGHUP  => T
  | SIGILL  => A
  | SIGINT  => T
  | SIGKILL => T
  | SIGPIPE => T
  | SIGQUIT => A
  | SIGSEGV => A
  | SIGSTOP => S
  | SIGTERM => T
  | SIGTSTP => S
  | SIGTTIN => S
  | SIGTTOU => S
  | SIGUSR1 => T
  | SIGUSR2 => T
  | SIGTRAP => A
  | SIGURG  => I
  | SIGXCPU => A
  | SIGXFSZ => A

end Smoosh
