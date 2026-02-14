/-
  Smoosh.Pattern — Pattern parsing and matching
  Translated from pattern.lem (407 lines)
-/
import Smoosh.Prelude

/-! # Match result -/

inductive MatchResult (α : Type) where
  | noMatch
  | symbolic
  | match_ (a : α)
  deriving Repr, Nonempty

/-! # Bracket chars and entries -/

inductive BracketChar where
  | char_ (c : Char)
  | collating (s : String)
  | equiv (s : String)
  | class_ (s : String)
  deriving Repr, BEq

inductive BracketEntry where
  | bc (c : BracketChar)
  | range (lo hi : BracketChar)
  deriving Repr, BEq

/-! # Pattern chars -/

inductive PatternChar where
  | lit (c : Char)
  | bracket (shouldMatch : Bool) (entries : List BracketEntry)
  | qmark
  | star
  deriving Repr, BEq

abbrev Pattern' := List PatternChar

def stringOfBracketChar : BracketChar → String
  | .char_ c => String.ofList [c]
  | .collating s => "[." ++ s ++ ".]"
  | .equiv s => "[=" ++ s ++ "=]"
  | .class_ s => "[:" ++ s ++ ":]"

def stringOfBracketEntry : BracketEntry → String
  | .bc c => stringOfBracketChar c
  | .range lo hi => stringOfBracketChar lo ++ "-" ++ stringOfBracketChar hi

def stringOfPatternChar : PatternChar → String
  | .lit c => String.ofList [c]
  | .bracket shouldMatch es =>
    "[" ++ (if shouldMatch then "" else "!") ++
    String.join (es.map stringOfBracketEntry) ++ "]"
  | .qmark => "?"
  | .star => "*"

def stringOfPattern (p : Pattern') : String :=
  String.join (p.map stringOfPatternChar)

/-! # Pattern parsing -/

def parseBracketTerminator (pat : List Char) (term : Char) : Except String (List Char × List Char) :=
  match pat with
  | [] => .error "expected bracket terminator, found end-of-pattern"
  | c :: ']' :: pat' =>
    if c == term then .ok (pat', [])
    else .error "expected terminator"
  | c :: pat' => do
    let (pat'', cls) ← parseBracketTerminator pat' term
    .ok (pat'', c :: cls)

def parseBracketChar (pat : List Char) : Except String (List Char × BracketChar) :=
  match pat with
  | [] => .error "expected bracket character, found end-of-pattern"
  | '[' :: '.' :: pat' => do
    let (pat'', cls) ← parseBracketTerminator pat' '.'
    .ok (pat'', .collating (String.ofList cls))
  | '[' :: '=' :: pat' => do
    let (pat'', cls) ← parseBracketTerminator pat' '='
    .ok (pat'', .equiv (String.ofList cls))
  | '[' :: ':' :: pat' => do
    let (pat'', cls) ← parseBracketTerminator pat' ':'
    .ok (pat'', .class_ (String.ofList cls))
  | c :: pat' => .ok (pat', .char_ c)

partial def parseBracketEntries (pat : List Char) : Except String (List Char × List BracketEntry) :=
  match pat with
  | [] => .error "expected bracket entries, found end-of-pattern"
  | ']' :: pat' => .ok (pat', [])
  | _ => do
    let (pat', bc) ← parseBracketChar pat
    match pat' with
    | '-' :: ']' :: pat'' => .ok (']' :: pat'', [.bc (.char_ '-'), .bc bc])
    | '-' :: pat'' => do
      let (pat''', bc2) ← parseBracketChar pat''
      let (pat'''', es) ← parseBracketEntries pat'''
      .ok (pat'''', .range bc bc2 :: es)
    | _ => do
      let (pat'', es) ← parseBracketEntries pat'
      .ok (pat'', .bc bc :: es)

def bracketInitialLiteral (c : Char) : Bool := c == ']' || c == '-'

partial def parseBracket (pat : List Char) : Except String (List Char × PatternChar) :=
  match pat with
  | [] => .error "unterminated bracket, found end-of-pattern"
  | c :: pat' =>
    let (matching, pat'') :=
      if c == '!' then (false, pat')
      else (true, pat)
    let (realPat, frontEs) :=
      match pat'' with
      | c' :: rest' =>
        if bracketInitialLiteral c' then (rest', [BracketEntry.bc (.char_ c')])
        else (pat'', [])
      | _ => (pat'', [])
    match parseBracketEntries realPat with
    | .error err => .error err
    | .ok (restPat, es) => .ok (restPat, .bracket matching (frontEs ++ es))

partial def parsePatternLoop (pat : List Char) : Except String (List Char × Pattern') :=
  match pat with
  | [] => .ok ([], [])
  | '*' :: pat' => do
    let (rest, pcs) ← parsePatternLoop pat'
    .ok (rest, .star :: pcs)
  | '?' :: pat' => do
    let (rest, pcs) ← parsePatternLoop pat'
    .ok (rest, .qmark :: pcs)
  | '[' :: pat' =>
    match parseBracket pat' with
    | .error _ => do
      -- treat '[' as literal
      let (rest, pcs) ← parsePatternLoop pat'
      .ok (rest, .lit '[' :: pcs)
    | .ok (pat'', bc) => do
      let (rest, pcs) ← parsePatternLoop pat''
      .ok (rest, bc :: pcs)
  | '\\' :: c :: pat' => do
    let (rest, pcs) ← parsePatternLoop pat'
    .ok (rest, .lit c :: pcs)
  | c :: pat' => do
    let (rest, pcs) ← parsePatternLoop pat'
    .ok (rest, .lit c :: pcs)

def parsePattern (pat : List Char) : Except String Pattern' :=
  match parsePatternLoop pat with
  | .error err => .error err
  | .ok ([], pattern) => .ok pattern
  | .ok (pat', _) => .error s!"unexpected unparsed pattern in '{String.ofList pat'}'"

/-! # Pattern matching -/

def matchEntry (lc : Locale) (c : Char) (be : BracketEntry) : Bool :=
  match be with
  | .bc (.char_ c') => c' == c
  | .bc (.collating cls) => lc.collates c cls
  | .bc (.equiv cls) => lc.equiv c cls
  | .bc (.class_ cls) => lc.charclass c cls
  | .range lo hi =>
    let rcharOf : BracketChar → Option RangeChar
      | .char_ c => some (.rchar c)
      | .collating s => some (.rcollating s)
      | _ => none
    match rcharOf lo, rcharOf hi with
    | some rlo, some rhi => lc.range c rlo rhi
    | _, _ => false

partial def matchExactPattern (lc : Locale) (pat : Pattern') (s : SymbolicString) : MatchResult SymbolicString :=
  match pat, s with
  | [], [] => .match_ []
  | [], _ => .noMatch
  | .lit c :: pat', .c c' :: s' =>
    if c == c' then matchExactPattern lc pat' s'
    else .noMatch
  | .qmark :: pat', .c _ :: s' => matchExactPattern lc pat' s'
  | .bracket shouldMatch es :: pat', .c c :: s' =>
    let matched := es.any (matchEntry lc c)
    if matched == shouldMatch then matchExactPattern lc pat' s'
    else .noMatch
  | .star :: pat', _ => matchStar lc pat' s
  | _, .sym _ :: _ => .symbolic
  | _ :: _, [] => .noMatch
where
  matchStar (lc : Locale) (pat' : Pattern') : SymbolicString → MatchResult SymbolicString
    | [] => matchExactPattern lc pat' []
    | ss@(.c _ :: s') =>
      match matchExactPattern lc pat' ss with
      | .match_ r => .match_ r
      | .symbolic => .symbolic
      | .noMatch => matchStar lc pat' s'
    | ss@(.sym _ :: _) => .symbolic

def matchExact (lc : Locale) (pat s : SymbolicString) : MatchResult SymbolicString :=
  match parsePattern (pat.filterMap (fun c => match c with | .c ch => some ch | .sym _ => none)) with
  | .error _ => .noMatch
  | .ok parsedPat => matchExactPattern lc parsedPat s

/-! # Shortest and longest matching (for ${var%pat} etc.) -/

partial def matchShortest (lc : Locale) (pat str : SymbolicString) : MatchResult (SymbolicString × SymbolicString) :=
  go str
where
  go : SymbolicString → MatchResult (SymbolicString × SymbolicString)
  | [] =>
    match matchExact lc pat [] with
    | .match_ _ => .match_ ([], [])
    | .symbolic => .symbolic
    | .noMatch => .noMatch
  | c :: str' =>
    match matchExact lc pat [c] with
    | .match_ _ => .match_ ([c], str')
    | .symbolic => .symbolic
    | .noMatch =>
      match go str' with
      | .match_ (m, rest) => .match_ (c :: m, rest)
      | other => other

partial def matchLongest (lc : Locale) (pat str : SymbolicString) : MatchResult (SymbolicString × SymbolicString) :=
  -- Try matching the whole string first, then successively shorter
  let rec tryLen (n : Nat) : MatchResult (SymbolicString × SymbolicString) :=
    let pref := str.take n
    let suff := str.drop n
    match matchExact lc pat pref with
    | .match_ _ => .match_ (pref, suff)
    | .symbolic => .symbolic
    | .noMatch =>
      if n == 0 then .noMatch
      else tryLen (n - 1)
  tryLen str.length
