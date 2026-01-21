import Smoosh.Prelude.All
import Smoosh.Map
import Smoosh.Set
import Smoosh.os.OsState
import Smoosh.Num

universe u

namespace Smoosh
open Smoosh

/-- Lem: local_binding type -/
inductive local_binding where
  | LocalNotFound : local_binding
  | LocalUnset : local_opts → local_binding
  | LocalSet : symbolic_string → local_opts → local_binding

/-- Lem: pop_locals : forall 'a. os_state 'a -> os_state 'a * local_env -/
def pop_locals : ∀ {α : Type u}, os_state α → Except String (os_state α × local_env)
  | _, os =>
    match os.sh.locals with
    | [] => .error "pop_locals"
    | outer :: locals' =>
        .ok ( { os with sh := { os.sh with locals := locals' } }, outer )

/-- Lem: push_locals : forall 'a. os_state 'a -> env -> os_state 'a -/
def push_locals {α : Type u} (os : os_state α) (env : env) : os_state α :=
  let local_env :=
    Map.mapValues (fun v => (some v, local_opts_default)) env
  { os with
    sh := { os.sh with
      locals := local_env :: os.sh.locals } }

/-- Lem: val new_local_scope : forall 'a. os_state 'a -> os_state 'a -/
def new_local_scope : ∀ {α : Type u}, os_state α → os_state α
  | _, os =>
    { os with sh := { os.sh with locals := Map.empty :: os.sh.locals } }

/-- Lem: val get_locals_loop : list local_env -> set string -/
def get_locals_loop : List local_env → Set.Set String
  | [] => .empty
  | env :: locals' =>
      .union (Map.map.domain env) (get_locals_loop locals')

/-- Lem: val get_locals : forall 'a. os_state 'a -> list string -/
def get_locals : ∀ {α : Type u}, os_state α → List String
  | _, os => Set.Set.toOrderedList (get_locals_loop os.sh.locals)

/-- Lem: val lookup_local_param_loop : string -> list local_env -> local_binding -/
def lookup_local_param_loop : String → List local_env → local_binding
  | _, [] => local_binding.LocalNotFound
  | x, env :: locals' =>
      match Map.map.lookup x env with
      | none => lookup_local_param_loop x locals'
      | some (none, opts) => local_binding.LocalUnset opts
      | some (some ss, opts) => local_binding.LocalSet ss opts

/-- Lem: val lookup_local_param : forall 'a. os_state 'a -> string -> local_binding -/
def lookup_local_param : ∀ {α : Type u}, os_state α → String → local_binding
  | _, os, x => lookup_local_param_loop x os.sh.locals

/-- Lem: val is_readonly : forall 'a. string -> os_state 'a -> bool -/
def is_readonly : ∀ {α : Type u}, String → os_state α → Bool
  | _, var, os =>
    match lookup_local_param os var with
    | local_binding.LocalNotFound => Set.Set.member var os.sh.readonly
    | local_binding.LocalUnset opts => opts.local_readonly
    | local_binding.LocalSet _ opts => opts.local_readonly

/-- Lem: val check_param : forall 'a. string -> os_state 'a -> maybe string (* err msg *) -/
def check_param : ∀ {α : Type u}, String → os_state α → Option String
  | _, x, os0 =>
    if is_readonly x os0 then
      some (x ++ ": is read only")
    else if is_special_param x then
      some (x ++ ": is a special parameter and not a valid identifier")
    else
      none

/-- Lem: val set_local_param_opts_loop : string -> (local_opts -> local_opts) -> list local_env -> maybe (list local_env) -/
def set_local_param_opts_loop
  : String → (local_opts → local_opts) → List local_env → Option (List local_env)
  | _, _, [] => none
  | x, upd, env :: locals' =>
      match Map.map.lookup x env with
      | none =>
          match set_local_param_opts_loop x upd locals' with
          | none => none
          | some set_locals => some (env :: set_locals)
      | some (v, opts) =>
          let env' := Map.map.insert x (v, upd opts) env
          some (env' :: locals')

/-- Lem: val set_local_param_opts : forall 'a. os_state 'a -> string -> (local_opts -> local_opts) -> os_state 'a * bool -/
def set_local_param_opts
  : ∀ {α : Type u}, os_state α → String → (local_opts → local_opts) → os_state α × Bool
  | _, os, x, upd =>
    match set_local_param_opts_loop x upd os.sh.locals with
    | none => (os, false)
    | some locals' =>
        ( { os with sh := { os.sh with locals := locals' } }, true )

/-- Lem: val set_local_param_loop : string -> maybe symbolic_string -> list local_env -> maybe (list local_env) -/
def set_local_param_loop
  : String → Option symbolic_string → List local_env → Option (List local_env)
  | _, _, [] => none
  | x, m_v, env :: locals' =>
      match Map.map.lookup x env with
      | none =>
          match set_local_param_loop x m_v locals' with
          | none => none
          | some set_locals => some (env :: set_locals)
      | some (_, opts) =>
          let env' := Map.map.insert x (m_v, opts) env
          some (env' :: locals')

/-- Lem: val set_local_param : forall 'a. os_state 'a -> string -> maybe symbolic_string -> os_state 'a * bool -/
def set_local_param
  : ∀ {α : Type u}, os_state α → String → Option symbolic_string → os_state α × Bool
  | _, os, x, m_v =>
    match set_local_param_loop x m_v os.sh.locals with
    | none => (os, false)
    | some locals' =>
        ( { os with sh := { os.sh with locals := locals' } }, true )

/-- Lem: val force_local_param : forall 'a. os_state 'a -> string -> symbolic_string -> either string (os_state 'a) -/
def force_local_param
  : ∀ {α : Type u}, os_state α → String → symbolic_string → Except String (os_state α)
  | _, os, x, v =>
    match os.sh.locals with
    | [] => .error "force_local_param missing local scope"
    | env :: locals' =>
        match check_param x os with
        | some err => .error err
        | none =>
            let env' := Map.map.insert x (some v, local_opts_default) env
            .ok { os with sh := { os.sh with locals := env' :: locals' } }

-- Helper
def index {α : Type u} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => index xs n

/-- Lem: val lookup_positional_param : forall 'a. nat -> os_state 'a -> maybe symbolic_string -/
def lookup_positional_param : ∀ {α : Type u}, Nat → os_state α → Option symbolic_string
  | _, num, os => index os.sh.positional_params num

/-- Lem: val get_function_params : forall 'a. os_state 'a -> fields -/
def get_function_params : ∀ {α : Type u}, os_state α → fields
  | _, os =>
    match os.sh.positional_params with
    | [] => []
    | _ :: argv => argv

/-- The result is none if unset, and the empty string if it's null.
 Lem: val lookup_string_param : forall 'a. os_state 'a -> string -> maybe symbolic_string -/
def lookup_string_param : ∀ {α : Type u}, os_state α → String → Except String (Option symbolic_string)
  | _, os, str =>
    match (Num.readNat (toCharList str), str) with
    | (.ok num, _) => .ok (lookup_positional_param num os)
    | (.error _, "$") => .ok (some (symbolic_string_of_nat os.sh.rootpid))
    | (.error _, "@") => .error "broken invariant: called lookup_string_param on @"
    | (.error _, "*") => .error "broken invariant: called lookup_string_param on *"
    | (.error _, "?") => .ok (symbolic_string_of_string (stringFromNat os.sh.exit_code))
    | (.error _, "-") =>
        let char_opts := (Set.Set.toList os.sh.opts).filterMap char_of_sh_opt
        .ok (some (symbolic_string_of_string (String.ofList char_opts)))
    | (.error _, "!") =>
        match os.sh.last_pid with
        | none => .ok none
        | some pid => .ok (some (symbolic_string_of_string (stringFromNat pid)))
    | (.error _, "#") =>
        let num_params := List.length os.sh.positional_params
        .ok (some (symbolic_string_of_string (stringFromNat (Nat.max 0 (num_params - 1)))))
    | (.error _, _) =>
        match lookup_local_param os str with
        | local_binding.LocalNotFound =>
            .ok (Map.map.lookup str os.sh.env)
        | local_binding.LocalUnset _opts =>
            .ok none
        | local_binding.LocalSet ss _opts =>
            .ok (some ss)

/-- Lem: val lookup_param : forall 'a. os_state 'a -> string -> maybe fields -/
def lookup_param : ∀ {α : Type u}, os_state α → String → Except String (Option fields)
  | _, os, str =>
    if str = "@" || str = "*" then
      .ok (some (get_function_params os))
    else
      match lookup_string_param os str with
      | .error msg => .error msg
      | .ok none   => .ok none
      | .ok (some v) => .ok (some [v])

/-- Lem: val lookup_concrete_param : forall 'a. os_state 'a -> string -> maybe string -/
def lookup_concrete_param : ∀ {α : Type u}, os_state α → String → Except String (Option String)
  | _, os, str =>
    match lookup_param os str with
    | .error msg => .error msg
    | .ok none => .ok none
    | .ok (some fs) => .ok (try_concrete_fields fs)

/-- Lem: val printable_shell_env : forall 'a. os_state 'a -> string -/
def printable_shell_env : ∀ {α : Type u}, os_state α → String
  | _, os =>
    (Map.map.toList os.sh.env).foldr
      (fun (kv : String × symbolic_string) s =>
        let (k, v) := kv
        k ++ "=" ++ quote (string_of_symbolic_string v) ++ "\n" ++ s)
      ""

/-- Lem: val ps1 : forall 'a. os_state 'a -> string -/
def ps1 : ∀ {α : Type u}, os_state α → String
  | _, os =>
    match lookup_concrete_param os "PS1" with
    | .error msg        => msg
    | .ok none          => "$ "
    | .ok (some prompt) => prompt

/-- Lem: val ps4 : forall 'a. os_state 'a -> string -/
def ps4 : ∀ {α : Type u}, os_state α → String
  | _, os =>
    match lookup_concrete_param os "PS4" with
    | .error msg        => msg
    | .ok none          => "+ "
    | .ok (some prompt) => prompt

/-- Lem: val get_path : forall 'a. os_state 'a -> string -/
def get_path {α : Type u} (os : os_state α) : String :=
  match lookup_concrete_param os "PATH" with
  | .error msg      => msg
  | .ok none        => ""
  | .ok (some path) => path

/-- Lem: val set_readonly : forall 'a. os_state 'a -> string -> os_state 'a -/
def set_readonly {α : Type u} (os0 : os_state α) (x : String) : os_state α :=
  let (os1, found_local) :=
    set_local_param_opts os0 x (fun opts => { opts with local_readonly := true })
  if found_local then
    os1
  else
    { os1 with
      sh := { os1.sh with
        readonly := Set.Set.insert x os1.sh.readonly } }

/-- Lem: val set_exported : forall 'a. os_state 'a -> string -> os_state 'a -/
def set_exported {α : Type u} (os0 : os_state α) (x : String) : os_state α :=
  let (os1, found_local) :=
    set_local_param_opts os0 x (fun opts => { opts with local_exported := true })
  if found_local then
    os1
  else
    { os1 with
      sh := { os1.sh with
        exported := Set.Set.insert x os1.sh.exported } }

/-- Lem: unset_env type -/
abbrev unset_env : Type :=
  Map.map String (Option symbolic_string)

def foldrMResult {α β : Type u}
    (f : α → β → Except String β) (init : β) : List α → Except String β
  | []      => .ok init
  | x :: xs =>
      match foldrMResult f init xs with
      | .error msg => .error msg
      | .ok acc    => f x acc

/--
Lem: collect_vars
  (os_state α -> set string) -> (local_opts -> bool) -> os_state α -> unset_env
-/
def collect_vars {α : Type u}
    (get_globals : os_state α → Set.Set String)
    (select_local : local_opts → Bool)
    (os : os_state α) : Except String unset_env :=
  let globalsList : List String :=
    Set.Set.toOrderedList (get_globals os)
  let step : String → unset_env → Except String unset_env :=
    fun x m =>
      match lookup_string_param os x with
      | .error msg => .error msg
      | .ok mv     => .ok (Map.insert x mv m)
  match foldrMResult step Map.empty globalsList with
  | .error msg => .error msg
  | .ok globals =>
      let add_local (lenv : local_env) (env0 : unset_env) : unset_env :=
        let selected_locals : unset_env :=
          Map.mapMaybe
            (fun _x (mv_opts : Option symbolic_string × local_opts) =>
              let m_v  := mv_opts.1
              let opts := mv_opts.2
              if select_local opts then some m_v else none)
            lenv
        Map.fold Map.insert selected_locals env0
      .ok (List.foldr add_local globals os.sh.locals)


/-- Lem: val readonly_vars : forall 'a. os_state 'a -> unset_env -/
def readonly_vars {α : Type u} (os : os_state α) : Except String unset_env :=
  collect_vars (fun os => os.sh.readonly) (fun opts => opts.local_readonly) os

/-- Lem: val exported_vars : forall 'a. os_state 'a -> unset_env -/
def exported_vars {α : Type u} (os : os_state α) : Except String unset_env :=
  collect_vars (fun os => os.sh.exported) (fun opts => opts.local_exported) os

/-- Lem: val exported_set_vars : forall 'a. os_state 'a -> env -/
def exported_set_vars {α : Type u} (os : os_state α) : Except String env :=
  match exported_vars os with
  | .ok une => .ok (Map.mapMaybe (fun _x (m_v : Option symbolic_string) => m_v) une)
  | .error msg => .error msg

/-- Lem: val internal_set_param
    : forall 'a. string -> symbolic_string -> os_state 'a -> os_state 'a -/
def internal_set_param {α : Type u}
    (x : String) (v : symbolic_string) (os0 : os_state α) : os_state α :=
  let (os1, found_local) := set_local_param os0 x (some v)
  if found_local then
    os1
  else
    { os1 with
      sh := { os1.sh with
        env := Map.insert x v os1.sh.env } }

/-- Lem: val unset_param : forall 'a. string -> os_state 'a -> os_state 'a -/
def unset_param {α : Type u} (x : String) (os0 : os_state α) : os_state α :=
  let (os1, found_local) := set_local_param os0 x none
  if found_local then
    os1
  else
    { os1 with
      sh := { os1.sh with
        env      := Map.delete x os1.sh.env
        readonly := .delete x os1.sh.readonly
        exported   := .delete x os1.sh.exported } }

end Smoosh
