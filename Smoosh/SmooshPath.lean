/-
  Smoosh.SmooshPath — Pathname expansion / globbing
  Translated from `path.lem` (102 lines).

  Implements directory walking and glob pattern matching against symbolic filesystem entries.
-/
import Smoosh.Os
import Smoosh.Pattern

/-! # Path info -/

structure PathInfo where
  pathPrefix : String
  trailingSlash : Bool
  deriving Repr, BEq

/-! # Path utilities -/

/-- Ref: path.lem:has_leading_dot — Check if filename starts with '.'. -/
def hasLeadingDot : List Char → Bool
  | '.' :: _ => true
  | _ => false

/-- Ref: path.lem:has_trailing_slash — Check if path ends with '/'. -/
def hasTrailingSlash (cs : List Char) : Bool :=
  match cs.reverse with
  | '/' :: _ => true
  | _ => false

/-- Ref: path.lem:split_on_slash — Split path components on '/'. -/
def splitOnSlash (cs : List Char) : List (List Char) :=
  splitOn false '/' cs

/-! # Path pattern parsing -/

/-- Ref: path.lem:parse_path_pattern — Parse glob pattern into (components, starting dir, path info). -/
def parsePathPattern {α : Type} [OS α] (os : OsState α) (pat : String) : List String × Path × PathInfo :=
  match pat.toList with
  | '/' :: pat' =>
    ((splitOnSlash pat').map String.ofList,
     "/",
     { pathPrefix := "/", trailingSlash := hasTrailingSlash pat' })
  | chars =>
    ((splitOnSlash chars).map String.ofList,
     os.sh.cwd,
     { pathPrefix := "", trailingSlash := hasTrailingSlash chars })

/-! # Pattern file matching -/

/-- Ref: path.lem:match_pattern_file_list — Match glob pattern against directory listing. -/
def matchPatternFileList {α : Type} [OS α] (os : OsState α) (lc : Locale) (dir : Path) (pat : String) : List (String × FileUnit) :=
  let entries := OS.osReaddir os dir
  entries.filterMap (fun (name, file) =>
    let mr := matchExact lc (symbolicStringOfString pat) (symbolicStringOfString name)
    match mr with
    | .match_ _ =>
      if ¬(hasLeadingDot name.toList) || hasLeadingDot pat.toList then
        some (name, file)
      else none
    | _ => none)

/-- Ref: path.lem:match_dir — Match a single path component in a directory ('.', '..', or pattern). -/
def matchDir {α : Type} [OS α] (os : OsState α) (dir : Path) (lc : Locale) (name : String) : List (String × FileUnit) :=
  match name with
  | "" => [("", .dir dir)]
  | "." => [(".", .dir dir)]
  | ".." => [("..", .dir (dotdot dir))]
  | _ => matchPatternFileList os lc dir name

/-! # Directory walking -/

/-- Ref: path.lem:walk — Recursively walk directory tree matching path pattern components. -/
partial def walk {α : Type} [OS α] (os : OsState α) (pathSoFar : Option Path) (dir : Path)
    (pinfo : PathInfo) (lc : Locale) : List String → List (String × FileUnit)
  | [] =>
    let fullPath := match pathSoFar with
      | none => pinfo.pathPrefix
      | some p => p
    [(fullPath ++ if pinfo.trailingSlash then "/" else "", .dir dir)]
  | path' :: rest =>
    let matched := matchDir os dir lc path'
    matched.flatMap (fun (sub, fileU) =>
      let fullPath := match pathSoFar with
        | none => pinfo.pathPrefix ++ sub
        | some parent => parent ++ "/" ++ sub
      match fileU with
      | .file =>
        if rest.isEmpty && ¬pinfo.trailingSlash
        then [(fullPath, .file)]
        else []
      | .dir dir' => walk os (some fullPath) dir' pinfo lc rest)

/-! # Main match_path function -/

/-- Ref: path.lem:match_path — Main entry: glob a path pattern, returning sorted list of matches. -/
def matchPath {α : Type} [OS α] (os : OsState α) (path : String) : List Path :=
  let (pat, start, pinfo) := parsePathPattern os path
  let results := walk os none start pinfo os.sh.locale pat
  (results.map Prod.fst).mergeSort (· ≤ ·)
