import Smoosh.Pattern
import Smoosh.Smoosh
import Smoosh.OsSymbolic.All

open Smoosh

/-- split_on_slash : list char -> list (list char)
    let split_on_slash = split_on false (* not escapable *) #'/'
-/
def split_on_slash : List Char → List (List Char) :=
  split_on false '/'

/-- path_info = <| path_prefix : string; trailing_slash : bool |> -/
structure path_info where
  path_prefix    : String
  trailing_slash : Bool
deriving Repr

/-- has_leading_dot : list char -> bool -/
def has_leading_dot : List Char → Bool
  | '.' :: _ => true
  | _        => false

/-- has_trailing_slash : list char -> bool -/
def has_trailing_slash (cs : List Char) : Bool :=
  match cs.reverse with
  | '/' :: _ => true
  | _        => false

/-- parse_path_pattern : OS a => os_state a -> string -> list string * path * path_info -/
def parse_path_pattern {α : Type u} [OS α]
    (os : os_state α) (pat : String)
    : List String × path × path_info :=
  match toCharList pat with
  | '/' :: pat' =>
      ( List.map charListToString (split_on_slash pat')
      , "/"
      , { path_prefix := "/", trailing_slash := has_trailing_slash pat' } )
  | chars =>
      ( List.map charListToString (split_on_slash chars)
      , os.sh.cwd
      , { path_prefix := "", trailing_slash := has_trailing_slash chars } )

/-
We use shortest matching because we won't look at the content of the match.
We only care whether or not there was a match.
-/

/-- match_pattern_file_list : OS a => os_state a -> locale -> path -> string -> set (string * file path) -/
def match_pattern_file_list {α : Type u} [OS α]
    (os : os_state α) (lc : locale) (dir : path) (pat : String)
    : Set.Set (String × file path) :=
  Set.Set.map (fun (p : Smoosh.path × file Unit) =>
      let (name, f) := p
      ( name
      , match f with
        | .File   => .File
        | .Dir _  => .Dir (dir ++ "/" ++ name)
      ))
    (Set.Set.filter
      (fun (p : Smoosh.path × file Unit) =>
        let (fileName, _f) := p
        let r := match_exact lc (symbolic_string_of_string pat)
                          (symbolic_string_of_string fileName)
        match r with
        | .Match _ =>
            (!has_leading_dot (toCharList fileName)) || has_leading_dot (toCharList pat)
        | _ => false)
      (readdir os dir))

/-- match_dir : OS a => os_state a -> path -> locale -> string -> set (string * file path) -/
def match_dir {α : Type u} [OS α]
    (os : os_state α) (dir : path) (lc : locale) (name : String)
    : Set.Set (String × file path) :=
  match name with
  | ""   => Set.Set.singleton ("",   .Dir dir)
  | "."  => Set.Set.singleton (".",  .Dir dir)
  | ".." => Set.Set.singleton ("..", .Dir (dotdot dir))
  | _    => match_pattern_file_list os lc dir name

/-- walk : OS a => os_state a -> (maybe path * path) -> path_info -> locale
            -> list string -> set (string * file path) -/
partial def walk {α : Type u} [OS α]
    (os : os_state α) (state : Option path × path)
    (pinfo : path_info) (lc : locale) (pathParts : List String)
    : Set.Set (String × file path) :=
  let path_so_far : Option path := state.1
  let dir : path := state.2
  match pathParts with
  | [] =>
      let full_path :=
        match path_so_far with
        | none   => pinfo.path_prefix
        | some p => p
      Set.Set.singleton
        ( full_path ++ (if pinfo.trailing_slash then "/" else "")
        , .Dir dir )
  | path' :: rest =>
      Set.Set.bigunionMapBy compare_by_first
        (fun (sub, f) =>
          let full_path :=
            match path_so_far with
            | none        => pinfo.path_prefix ++ sub
            | some parent => parent ++ "/" ++ sub
          match f with
          | .File =>
              if rest.isEmpty && (!pinfo.trailing_slash) then
                Set.Set.singleton (full_path, .File)
              else
                Set.Set.empty
          | .Dir dir' =>
              walk os (some full_path, dir') pinfo lc rest)
        (match_dir os dir lc path')

/-- match_path : OS a => os_state a -> string -> list path -/
def match_path {α : Type u} [OS α]
    (os : os_state α) (pathStr : String) : List path :=
  let (pat, start, pinfo) := parse_path_pattern os pathStr
  Set.Set.toOrderedList
    (Set.Set.map (fun p => p.1) (walk os (none, start) pinfo os.sh.locale pat))

/-- instantiated version for testing from OCaml -/
def match_path_symbolic : os_state symbolic → String → List path :=
  match_path
