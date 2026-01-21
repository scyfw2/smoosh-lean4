import Smoosh.Prelude.All
import Smoosh.Map
import Smoosh.Set
import Smoosh.os.OsState
import Smoosh.Num
import Smoosh.os.ParamHelper
import Smoosh.os.LogHis

universe u

namespace Smoosh
open Smoosh

/-- Lem: val clear_hash : forall 'a . os_state 'a -> os_state 'a -/
def clear_hash {α : Type u} (os : os_state α) : os_state α :=
  { os with
    sh := { os.sh with
      hashes := Map.empty } }

/--
Lem: val hash_lookup :
  forall 'a. os_state 'a -> (path -> bool) -> string -> os_state 'a * maybe path
-/
def hash_lookup {α : Type u}
    (s0 : os_state α) (ok : path → Bool) (prog : String)
    : os_state α × Option path :=
  match Map.lookup prog s0.sh.hashes with
  | none => (s0, none)
  | some (p, hits) =>
      if ok p then
        let s1 :=
          { s0 with
            sh := { s0.sh with
              hashes := Map.insert prog (p, hits + 1) s0.sh.hashes } }
        (s1, some p)
      else
        let s1 :=
          { s0 with
            sh := { s0.sh with
              hashes := Map.delete prog s0.sh.hashes } }
        (s1, some p)

/-- Lem: val hash_insert :
  forall 'a. os_state 'a -> string -> path -> os_state 'a -/
def hash_insert {α : Type u} (os : os_state α) (prog : String) (p : path) : os_state α :=
  { os with
    sh := { os.sh with
      hashes := Map.insert prog (p, 1) os.sh.hashes } }

end Smoosh
