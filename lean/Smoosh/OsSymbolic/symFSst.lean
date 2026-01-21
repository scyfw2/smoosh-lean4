import Smoosh.os.All
import Smoosh.Prelude.All

open Smoosh

/-- Lem: symbolic_fs type -/
structure symbolic_fs where
  parent   : Option symbolic_fs
  contents : Map.map String (file symbolic_fs)

/-- Lem: fs type -/
abbrev fs := symbolic_fs  -- shim

/-- Lem: symbolic_fs_dotdot -/
def symbolic_fs_dotdot (fs : symbolic_fs) : symbolic_fs :=
  match fs.parent with
  | none  => fs
  | some fs' => fs'

/-- Lem: symbolic_fs_subdir -/
def symbolic_fs_subdir (fs : symbolic_fs) (name : String) : Option symbolic_fs :=
  match Map.lookup name fs.contents with
  | some (.Dir fs') => some fs'
  | _              => none

/-- Lem: val symbolic_fs_resolve_comps : symbolic_fs -> list string -> maybe (file symbolic_fs) -/
def symbolic_fs_resolve_comps (fs : symbolic_fs) (comps : List String) : Option (file symbolic_fs) :=
  match comps with
  | []            => some (.Dir fs)
  | ""    :: cs   => symbolic_fs_resolve_comps fs cs
  | "."   :: cs   => symbolic_fs_resolve_comps fs cs
  | ".."  :: cs   => symbolic_fs_resolve_comps (symbolic_fs_dotdot fs) cs
  | [f]           => Map.lookup f fs.contents
  | dir   :: cs   =>
      match symbolic_fs_subdir fs dir with
      | some fs' => symbolic_fs_resolve_comps fs' cs
      | none  => none
termination_by comps

/-- Lem: val symbolic_fs_resolve_path : symbolic_fs -> string -> maybe (file symbolic_fs) -/
def symbolic_fs_resolve_path (fs : symbolic_fs) (path : String) : Option (file symbolic_fs) :=
  let comps := split_string_on false '/' path
  symbolic_fs_resolve_comps fs comps

/-- Lem: val symbolic_fs_resolve_dir : symbolic_fs -> string -> maybe symbolic_fs -/
def symbolic_fs_resolve_dir (fs : symbolic_fs) (path : String) : Option symbolic_fs :=
  match symbolic_fs_resolve_path fs path with
  | some (.Dir fs') => some fs'
  | _              => none

/-- empty FS/OS for testing purposes -/
def fs_empty : symbolic_fs :=
  { parent := none
  , contents := Map.empty
  }
