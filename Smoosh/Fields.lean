/-
  Smoosh.Fields — Field splitting, pathname expansion, and quote removal
  Translated from `fields.lem` (253 lines).

  Implements IFS-based field splitting, pathname expansion via globs, and POSIX quote removal.
-/
import Smoosh.Os
import Smoosh.SmooshPath

/-! # Field splitting helpers -/

/-- Ref: fields.lem helpers — True if `c` is an IFS-whitespace char (space/newline/tab). -/
def isWs (c : Char) : Bool := c ∈ [' ', '\n', '\t']

/-! # Collect non-IFS characters -/

/-- Ref: fields.lem helpers — Collect consecutive non-IFS characters into a field. -/
def collectNonIfs (ifs : List Char) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    if c ∈ ifs then ([], c :: cs)
    else let (f, remaining) := collectNonIfs ifs cs; (c :: f, remaining)

/-! # Expanded string splitting by IFS -/

-- OCaml: split_expstring ifs clst produces IntermediateFields with WFS/FS/Field distinction.
-- WFS for IFS whitespace chars, FS for non-whitespace IFS delimiters, Field for data.
/-- Ref: fields.lem:split_expstring — Split expanded string by IFS into intermediate fields. -/
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
/-- Ref: fields.lem:split_word — Split word list by IFS, accumulating intermediate fields. -/
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

/-- Ref: fields.lem:concat_expanded — Concatenate expanded words into a symbolic string (no splitting). -/
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
/-- Ref: fields.lem:skip_field_splitting — Convert expanded words to intermediate fields without IFS splitting. -/
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
/-- Ref: fields.lem:combine_fields — Merge adjacent fields and normalize whitespace separators. -/
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
/-- Ref: fields.lem:clean_fields — Strip leading whitespace, then combine fields. -/
partial def cleanFields : IntermediateFields → IntermediateFields
  | .wfs :: rst => cleanFields rst
  | other => combineFields other

/-! # Full field splitting -/

/-- Ref: fields.lem:field_splitting — Main field splitting entry: IFS-aware splitting. -/
def fieldSplitting {α : Type} [OS α] (os : OsState α) (expWords : ExpandedWords) : IntermediateFields :=
  match lookupConcreteParam os "IFS" with
  | none => cleanFields (splitWord [' ', '\n', '\t'] ([], expWords))
  | some "" => skipFieldSplitting expWords
  | some s => cleanFields (splitWord s.toList ([], expWords))

/-! # Pathname expansion -/

-- OCaml: needs_expansion checks if pattern chars exist (optimization)
/-- Ref: fields.lem:needs_expansion — Check if pattern chars exist (glob optimization). -/
def needsExpansion : SymbolicString → Bool
  | [] => false
  | [.c '['] => false  -- kludge for a bare [
  | .c '?' :: _ => true
  | .c '*' :: _ => true
  | .c '[' :: _ => true
  | _ :: ss => needsExpansion ss

-- OCaml: insert_field_separators interleaves FS between expanded path matches
/-- Ref: fields.lem:insert_field_separators — Interleave FS between expanded path matches. -/
def insertFieldSeparators : List String → IntermediateFields
  | [] => []
  | [f] => [.field (symbolicStringOfString f)]
  | f :: fs => .field (symbolicStringOfString f) :: .fs :: insertFieldSeparators fs

-- OCaml: pathname_expansion only expands unquoted Field entries
/-- Ref: fields.lem:pathname_expansion — Expand unquoted Field entries using glob matching. -/
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

/-- Ref: fields.lem:remove_quotes — Convert qfield to field (remove quote markers). -/
def removeQuotes : IntermediateFields → IntermediateFields
  | [] => []
  | .qfield s :: rst => .field s :: removeQuotes rst
  | f :: rst => f :: removeQuotes rst

-- OCaml: to_fields handles FS::FS producing empty fields
/-- Ref: fields.lem:to_fields — Convert intermediate fields to final fields list. -/
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

/-- Ref: fields.lem:quote_removal — Full pipeline: remove quotes, combine, and finalize fields. -/
def quoteRemoval (f : IntermediateFields) : Fields :=
  let noQuotes := combineFields (removeQuotes f)
  finalizeFields noQuotes
