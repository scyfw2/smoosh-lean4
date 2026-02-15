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

-- OCaml: split_expstring ifs clst produces IntermediateFields with WFS/FS/Field distinction.
-- WFS for IFS whitespace chars, FS for non-whitespace IFS delimiters, Field for data.
partial def splitExpstring (ifs : List Char) (clst : List Char) : IntermediateFields :=
  match clst with
  | [] => []
  | c :: cs =>
    if c ∈ ifs then
      (if isWs c then TmpField.wfs else TmpField.fs) :: splitExpstring ifs cs
    else
      let (cc, remaining) := collectNonIfs ifs cs
      TmpField.field (symbolicStringOfString (String.ofList (c :: cc))) :: splitExpstring ifs remaining

/-! # Word splitting -/

-- OCaml: split_word ifs (f, expanded_words) where f is IntermediateFields accumulator.
-- Matching OCaml's (intermediate_fields * expanded_words) pair.
partial def splitWord (ifs : List Char) : IntermediateFields × ExpandedWords → IntermediateFields
  | (f, []) => f
  | (f, .usrF :: .usrF :: wrds) => splitWord ifs (f, .usrF :: wrds)
  | (f, .usrF :: wrds) => splitWord ifs (f ++ [.fs], wrds)
  | (f, .expS s :: wrds) =>
    let newFields := splitExpstring ifs s.toList
    splitWord ifs (f ++ newFields, wrds)
  | (f, .usrS s :: wrds) =>
    splitWord ifs (f ++ [.field (symbolicStringOfString s)], wrds)
  | (f, .at_ fs :: wrds) =>
    splitWord ifs (f ++ fs.map (fun s => TmpField.field s), wrds)
  | (f, .dquo ss :: wrds) =>
    splitWord ifs (f ++ [.qfield ss], wrds)
  | (f, .ewSym sym :: wrds) =>
    splitWord ifs (f ++ [.field [.sym sym]], wrds)

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

-- OCaml: skip_field_splitting collapses UsrF::UsrF, turns UsrF into FS,
-- and uses QField (not Field) for DQuo/At.
partial def skipFieldSplitting : ExpandedWords → IntermediateFields
  | [] => []
  | .usrF :: .usrF :: ws => skipFieldSplitting (.usrF :: ws)
  | .usrF :: ws => .fs :: skipFieldSplitting ws
  | .expS s :: ws => .field (symbolicStringOfString s) :: skipFieldSplitting ws
  | .usrS s :: ws => .field (symbolicStringOfString s) :: skipFieldSplitting ws
  | .at_ fs :: ws =>
    -- OCaml: intersperse FS (map QField fs)
    let qfields := fs.map (fun ss => TmpField.qfield ss)
    let interspersed := qfields.intersperse .fs
    interspersed ++ skipFieldSplitting ws
  | .dquo ss :: ws => .qfield ss :: skipFieldSplitting ws
  | .ewSym sym :: ws => .field [.sym sym] :: skipFieldSplitting ws

/-! # Combine fields -/

-- OCaml: combine_fields merges adjacent Field/QField and normalizes WFS/FS.
-- Key cases: Field++Field, QField++QField, QField++Field (escape_patterns), Field++QField (escape_patterns).
partial def combineFields : IntermediateFields → IntermediateFields
  | [] => []
  | [.wfs] => []
  | .wfs :: .wfs :: rst => combineFields (.wfs :: rst)
  | .wfs :: .fs :: rst => combineFields (.fs :: rst)
  | .fs :: .wfs :: rst => combineFields (.fs :: rst)
  | .field s1 :: .field s2 :: rst => combineFields (.field (s1 ++ s2) :: rst)
  | .qfield s1 :: .qfield s2 :: rst => combineFields (.qfield (s1 ++ s2) :: rst)
  | .qfield s1 :: .field s2 :: rst => combineFields (.field (escapePatterns s1 ++ s2) :: rst)
  | .field s1 :: .qfield s2 :: rst => combineFields (.field (s1 ++ escapePatterns s2) :: rst)
  | .wfs :: rst => .fs :: combineFields rst
  | f :: rst => f :: combineFields rst

/-! # Clean fields -/

-- OCaml: clean_fields strips leading WFS, then calls combine_fields.
partial def cleanFields : IntermediateFields → IntermediateFields
  | .wfs :: rst => cleanFields rst
  | other => combineFields other

/-! # Full field splitting -/

def fieldSplitting {α : Type} [OS α] (os : OsState α) (expWords : ExpandedWords) : IntermediateFields :=
  match lookupConcreteParam os "IFS" with
  | none => cleanFields (splitWord [' ', '\n', '\t'] ([], expWords))
  | some "" => skipFieldSplitting expWords
  | some s => cleanFields (splitWord s.toList ([], expWords))

/-! # Pathname expansion -/

-- OCaml: needs_expansion checks if pattern chars exist (optimization)
def needsExpansion : SymbolicString → Bool
  | [] => false
  | [.c '['] => false  -- kludge for a bare [
  | .c '?' :: _ => true
  | .c '*' :: _ => true
  | .c '[' :: _ => true
  | _ :: ss => needsExpansion ss

-- OCaml: insert_field_separators interleaves FS between expanded path matches
def insertFieldSeparators : List String → IntermediateFields
  | [] => []
  | [f] => [.field (symbolicStringOfString f)]
  | f :: fs => .field (symbolicStringOfString f) :: .fs :: insertFieldSeparators fs

-- OCaml: pathname_expansion only expands unquoted Field entries
def pathnameExpansion {α : Type} [OS α] (os : OsState α) (ifs : IntermediateFields) : IntermediateFields :=
  if os.sh.opts.any (· == .noglob) then ifs
  else
    ifs.flatMap (fun tf =>
      match tf with
      | .field ss =>
        let matched :=
          if needsExpansion ss then
            match tryConcrete ss with
            | some pat => matchPath os pat
            | none => []
          else []
        if matched.isEmpty then
          [.field (unescapePattern ss)]
        else
          insertFieldSeparators matched
      | other => [other])

/-! # Quote removal -/

def removeQuotes : IntermediateFields → IntermediateFields
  | [] => []
  | .qfield s :: rst => .field s :: removeQuotes rst
  | f :: rst => f :: removeQuotes rst

-- OCaml: to_fields handles FS::FS producing empty fields
def toFields : IntermediateFields → Fields
  | [] => []
  | .field fs :: rst => fs :: toFields rst
  | .qfield fs :: rst => fs :: toFields rst
  | .fs :: .fs :: rst => symbolicStringOfString "" :: toFields (.fs :: rst)
  | .fs :: rst => toFields rst
  -- WFS should have been cleaned by combine_fields; if any remain, skip
  | .wfs :: rst => toFields rst

def finalizeFields : IntermediateFields → Fields
  | .fs :: rst => symbolicStringOfString "" :: finalizeFields rst
  | other => toFields other

def quoteRemoval (f : IntermediateFields) : Fields :=
  let noQuotes := combineFields (removeQuotes f)
  finalizeFields noQuotes
