import Smoosh.os.All
import Smoosh.Prelude.All

universe u

open Smoosh

opaque parse_init : parse_source → Option dash_string

opaque stack_init : Unit → stackmark

opaque stack_pop  : stackmark → Unit

opaque parse_done : Option dash_string → Option stackmark → Unit

opaque parse_next_internal : interactivity_mode → parse_result


def parse_next {α : Type u} [OS α]
    (s0 : os_state α) (interactive : interactivity_mode) : os_state α × parse_result :=
  match parse_next_internal interactive with
  | .ParseDone =>
      (s0, .ParseDone)
  | .ParseError s =>
      (s0, .ParseError s)
  | .ParseNull =>
      (s0, .ParseNull)
  | .ParseStmt c =>
      let s1 :=
        if Set.Set.member .Sh_verbose s0.sh.opts then
          safe_write_stderr (α := α) (string_of_stmt c ++ "\n") s0
        else
          s0
      (s1, .ParseStmt c)


def parse_cleanup (mss : Option dash_string) (smark : Option stackmark) (lvl : shell_level) : Unit :=
  if is_toplevel lvl then
    ()
  else
    parse_done mss smark
