/-
  Smoosh.Fields — Field splitting, pathname expansion, and quote removal
  Translated from fields.lem (253 lines)
-/
import Smoosh.Os
import Smoosh.SmooshPath

/-! # Field splitting helpers -/

def isWs (c : Char) : Bool := c ∈ [' ', '\n', '\t']

/-! # Collect non-IFS characters -/

def collectNonIfs (ifs : List Char) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    if c ∈ ifs then ([], c :: cs)
    else let (f, remaining) := collectNonIfs ifs cs; (c :: f, remaining)

/-! # Expanded string splitting by IFS -/

partial def splitExpstring (ifs : List Char) (clst : List Char) : List (List Char) :=
  match clst with
  | [] => [[]]
  | c :: cs =>
    if c ∈ ifs then
      [] :: splitExpstring ifs cs
    else
      let (f, remaining) := collectNonIfs ifs (c :: cs)
      match splitExpstring ifs remaining with
      | [] => [f]
      | first :: rest => (f ++ first) :: rest

/-! # Word splitting -/

partial def splitWord (ifs : List Char) : IntermediateFields × ExpandedWords → IntermediateFields
  | (f, []) => f
  | (f, .usrF :: wrds) =>
    -- IFS field split
    f ++ [.wfs] ++ splitWord ifs ([], wrds)
  | (f, .expS s :: wrds) =>
    let parts := splitExpstring ifs s.toList
    let fields := parts.map (fun p => TmpField.field (symbolicStringOfString (String.ofList p)))
    f ++ fields ++ splitWord ifs ([], wrds)
  | (f, .usrS s :: wrds) =>
    f ++ [.field (symbolicStringOfString s)] ++ splitWord ifs ([], wrds)
  | (f, .at_ fs :: wrds) =>
    let fields := fs.map (fun ss => TmpField.field ss)
    f ++ fields ++ splitWord ifs ([], wrds)
  | (f, .dquo ss :: wrds) =>
    f ++ [.qfield ss] ++ splitWord ifs ([], wrds)
  | (f, .ewSym sym :: wrds) =>
    f ++ [.field [.sym sym]] ++ splitWord ifs ([], wrds)

/-! # Concat expanded words -/

def concatExpanded : ExpandedWords → SymbolicString
  | [] => symbolicStringOfString ""
  | .usrF :: ws => symbolicStringOfString " " ++ concatExpanded ws
  | .expS s :: ws => symbolicStringOfString s ++ concatExpanded ws
  | .usrS s :: ws => symbolicStringOfString s ++ concatExpanded ws
  | .at_ fs :: ws => fs.flatMap id ++ concatExpanded ws
  | .dquo ss :: ws => ss ++ concatExpanded ws
  | .ewSym sym :: ws => [.sym sym] ++ concatExpanded ws

/-! # Skip field splitting -/

def skipFieldSplitting : ExpandedWords → IntermediateFields
  | [] => []
  | .usrF :: ws => skipFieldSplitting ws
  | .expS s :: ws => .field (symbolicStringOfString s) :: skipFieldSplitting ws
  | .usrS s :: ws => .field (symbolicStringOfString s) :: skipFieldSplitting ws
  | .at_ fs :: ws => fs.map (fun ss => TmpField.field ss) ++ skipFieldSplitting ws
  | .dquo ss :: ws => .qfield ss :: skipFieldSplitting ws
  | .ewSym sym :: ws => .field [.sym sym] :: skipFieldSplitting ws

/-! # Full field splitting -/

def fieldSplitting {α : Type} [OS α] (os : OsState α) (expWords : ExpandedWords) : IntermediateFields :=
  match lookupConcreteParam os "IFS" with
  | none => splitWord [' ', '\n', '\t'] ([], expWords)
  | some "" => skipFieldSplitting expWords
  | some s => splitWord s.toList ([], expWords)

/-! # Combine fields -/

partial def combineFields : IntermediateFields → IntermediateFields
  | [] => []
  | [.wfs] => []
  | .wfs :: .wfs :: rst => combineFields (.wfs :: rst)
  | .wfs :: .fs :: rst => combineFields (.fs :: rst)
  | .fs :: .wfs :: rst => combineFields (.fs :: rst)
  | .wfs :: rst => combineFields rst
  | f :: rst => f :: combineFields rst

/-! # Pathname expansion -/

def pathnameExpansion {α : Type} [OS α] (os : OsState α) (ifs : IntermediateFields) : IntermediateFields :=
  if os.sh.opts.any (· == .noglob) then ifs
  else
    ifs.flatMap (fun tf =>
      match tf with
      | .field ss =>
        match tryConcrete ss with
        | none => [tf]
        | some s =>
          let matched := matchPath os s
          match matched with
          | [] => [tf]
          | _ => matched.map (fun p => TmpField.field (symbolicStringOfString p))
      | other => [other])

/-! # Quote removal -/

def removeQuotes : IntermediateFields → IntermediateFields
  | [] => []
  | .qfield s :: rst => .field s :: removeQuotes rst
  | f :: rst => f :: removeQuotes rst

def toFields : IntermediateFields → Fields
  | [] => []
  | .field fs :: rst => fs :: toFields rst
  | .qfield fs :: rst => fs :: toFields rst
  | .wfs :: rst => toFields rst
  | .fs :: rst => toFields rst

def finalizeFields : IntermediateFields → Fields
  | .fs :: rst => symbolicStringOfString "" :: finalizeFields rst
  | other => toFields other

def quoteRemoval (f : IntermediateFields) : Fields :=
  let noQuotes := combineFields (removeQuotes f)
  finalizeFields noQuotes
