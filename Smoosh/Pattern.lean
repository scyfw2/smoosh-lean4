/-
  Smoosh.Pattern — Pattern parsing and matching
  Translated from `pattern.lem` (407 lines).

  Implements POSIX glob pattern parsing (brackets, `?`, `*`, literals) and
  matching against symbolic strings. Used by both pathname expansion (`SmooshPath`)
  and `case` statement pattern matching.
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

/-- Ref: pattern.lem:parse_bracket_terminator — Parse a single bracket entry terminator character. -/
def parseBracketTerminator (pat : SymbolicString) (term : Char) : Except String (SymbolicString × List Char) :=
  match pat with
  | [] => .error "expected bracket terminator, found end-of-pattern"
  | .c c :: .c ']' :: pat' =>
    if c == term then .ok (pat', [])
    else .error "expected terminator"
  | .c c :: pat' => do
    let (pat'', cls) ← parseBracketTerminator pat' term
    .ok (pat'', c :: cls)
  | .q c :: pat' => do
    let (pat'', cls) ← parseBracketTerminator pat' term
    .ok (pat'', c :: cls)
  | .sym _ :: pat' => parseBracketTerminator pat' term -- Skip symbols?

def parseBracketChar (pat : SymbolicString) : Except String (SymbolicString × BracketChar) :=
  match pat with
  | [] => .error "expected bracket character, found end-of-pattern"
  | .c '[' :: .c '.' :: pat' => do
    let (pat'', cls) ← parseBracketTerminator pat' '.'
    .ok (pat'', .collating (String.ofList cls))
  | .c '[' :: .c '=' :: pat' => do
    let (pat'', cls) ← parseBracketTerminator pat' '='
    .ok (pat'', .equiv (String.ofList cls))
  | .c '[' :: .c ':' :: pat' => do
    let (pat'', cls) ← parseBracketTerminator pat' ':'
    .ok (pat'', .class_ (String.ofList cls))
  | .c c :: pat' => .ok (pat', .char_ c)
  | .q c :: pat' => .ok (pat', .char_ c)
  | .sym _ :: pat' => parseBracketChar pat' -- Skip symbols

/-- Ref: pattern.lem:parse_bracket_entries — Parse bracket entries (char classes, ranges, literals). -/
partial def parseBracketEntries (pat : SymbolicString) : Except String (SymbolicString × List BracketEntry) :=
  match pat with
  | [] => .error "expected bracket entries, found end-of-pattern"
  | .c ']' :: pat' => .ok (pat', [])
  | _ => do
    let (pat', bc) ← parseBracketChar pat
    match pat' with
    | .c '-' :: .c ']' :: pat'' => .ok (.c ']' :: pat'', [.bc (.char_ '-'), .bc bc])
    | .c '-' :: pat'' => do
      let (pat''', bc2) ← parseBracketChar pat''
      let (pat'''', es) ← parseBracketEntries pat'''
      .ok (pat'''', .range bc bc2 :: es)
    | _ => do
      let (pat'', es) ← parseBracketEntries pat'
      .ok (pat'', .bc bc :: es)

def bracketInitialLiteral (c : Char) : Bool := c == ']' || c == '-'

/-- Ref: pattern.lem:parse_bracket — Parse a full bracket expression `[...]` or `[!...]`. -/
partial def parseBracket (pat : SymbolicString) : Except String (SymbolicString × PatternChar) :=
  match pat with
  | [] => .error "unterminated bracket, found end-of-pattern"
  | .c c :: pat' =>
    let (matching, pat'') :=
      if c == '!' then (false, pat')
      else (true, pat)
    let (realPat, frontEs) :=
      (match pat'' with
      | .c c' :: rest' =>
        if bracketInitialLiteral c' then (rest', [BracketEntry.bc (.char_ c')])
        else (pat'', [])
      | .q c' :: rest' => (rest', [BracketEntry.bc (.char_ c')]) -- Quoted initial char is mostly just a char, except ] and - might be special if not quoted? Actually if quoted, they are definitely literals.
      | _ => (pat'', []) : SymbolicString × List BracketEntry)
    match parseBracketEntries realPat with
    | .error err => .error err
    | .ok (restPat, es) => .ok (restPat, .bracket matching (frontEs ++ es))
  | .q c :: pat' =>
      -- Quoted [ is just literal [. But parseBracket is called only if [ was detected.
      -- Wait, parseBracket is called from parsePatternLoop when it sees [.
      -- If parsePatternLoop calls it, it already consumed [.
      -- But here parseBracket logic seems to handle the content INSIDE [ ... ].
      -- Ah, parsePatternLoop consumes '[', calls parseBracket with the rest.
      -- The first char of parseBracket input is the first char *after* [.
      -- So my match above on `.c c :: pat'` is handling `!`, `^` etc.
      let (matching, pat'') := (true, pat) -- Quoted first char can't be ! or ^?
      -- Actually, `[!...]` negation. If `!` is quoted, does it negate? `["!"]` -> matches `!`?
      -- The standard says `!` or `^` as first char. Quote removes special meaning.
      -- So if .q '!', it is NOT negation.
      let (realPat, frontEs) : SymbolicString × List BracketEntry := (pat, []) -- No special negation, proceed to entries
      -- But wait, what if the first char IS quoted ] or -?
      -- `["-"]` -> matches -
      match parseBracketEntries realPat with
        | .error err => .error err
        | .ok (restPat, es) => .ok (restPat, .bracket true es)
  | .sym _ :: pat' => parseBracket pat'

/-- Ref: pattern.lem:parse_pattern_loop — Parse a pattern string into a list of `PatternChar`. -/
partial def parsePatternLoop (pat : SymbolicString) : Except String (SymbolicString × Pattern') :=
  match pat with
  | [] => .ok ([], [])
  | .c '*' :: pat' => do
    let (rest, pcs) ← parsePatternLoop pat'
    .ok (rest, .star :: pcs)
  | .q '*' :: pat' => do
    let (rest, pcs) ← parsePatternLoop pat'
    .ok (rest, .lit '*' :: pcs)
  | .c '?' :: pat' => do
    let (rest, pcs) ← parsePatternLoop pat'
    .ok (rest, .qmark :: pcs)
  | .q '?' :: pat' => do
    let (rest, pcs) ← parsePatternLoop pat'
    .ok (rest, .lit '?' :: pcs)
  | .c '[' :: pat' =>
    match parseBracket pat' with
    | .error _ => do
      -- treat '[' as literal
      let (rest, pcs) ← parsePatternLoop pat'
      .ok (rest, .lit '[' :: pcs)
    | .ok (pat'', bc) => do
      let (rest, pcs) ← parsePatternLoop pat''
      .ok (rest, bc :: pcs)
  | .q '[' :: pat' => do
    let (rest, pcs) ← parsePatternLoop pat'
    .ok (rest, .lit '[' :: pcs)
  | .c '\\' :: .c c :: pat' => do
    let (rest, pcs) ← parsePatternLoop pat'
    .ok (rest, .lit c :: pcs)
  | .c '\\' :: .q c :: pat' => do
    let (rest, pcs) ← parsePatternLoop pat'
    .ok (rest, .lit c :: pcs)
  | .c c :: pat' => do
    let (rest, pcs) ← parsePatternLoop pat'
    .ok (rest, .lit c :: pcs)
  | .q c :: pat' => do
    let (rest, pcs) ← parsePatternLoop pat'
    .ok (rest, .lit c :: pcs)
  | .sym _ :: pat' => parsePatternLoop pat' -- Skip symbols

/-- Ref: pattern.lem:parse_pattern — Parse a complete pattern (calls `parsePatternLoop` and checks for full consumption). -/
def parsePattern (pat : SymbolicString) : Except String Pattern' :=
  match parsePatternLoop pat with
  | .error err => .error err
  | .ok ([], pattern) => .ok pattern
  | .ok (pat', _) => .error s!"unexpected unparsed pattern in '{stringOfSymbolicString pat'}'"

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

/-- Ref: pattern.lem:match_exact_pattern — Match a parsed pattern against a symbolic string. -/
partial def matchExactPattern (lc : Locale) (pat : Pattern') (s : SymbolicString) : MatchResult SymbolicString :=
  let rec matchStar (lc : Locale) (pat' : Pattern') : SymbolicString → MatchResult SymbolicString
    | [] => matchExactPattern lc pat' []
    | ss@(.c _ :: s') =>
      match matchExactPattern lc pat' ss with
      | .match_ r => .match_ r
      | .symbolic => .symbolic
      | .noMatch => matchStar lc pat' s'
    | ss@(.q _ :: s') =>
      match matchExactPattern lc pat' ss with
      | .match_ r => .match_ r
      | .symbolic => .symbolic
      | .noMatch => matchStar lc pat' s'
    | .sym _ :: _ => .symbolic

  match pat, s with
  | [], [] => .match_ []
  | [], _ => .noMatch
  | .lit c :: pat', .c c' :: s' =>
    if c == c' then matchExactPattern lc pat' s'
    else .noMatch
  | .lit c :: pat', .q c' :: s' =>
    if c == c' then matchExactPattern lc pat' s'
    else .noMatch
  | .qmark :: pat', .c _ :: s' => matchExactPattern lc pat' s'
  | .qmark :: pat', .q _ :: s' => matchExactPattern lc pat' s'
  | .bracket shouldMatch es :: pat', .c c :: s' =>
    let matched := es.any (matchEntry lc c)
    if matched == shouldMatch then matchExactPattern lc pat' s'
    else .noMatch
  | .bracket shouldMatch es :: pat', .q c :: s' =>
    let matched := es.any (matchEntry lc c)
    if matched == shouldMatch then matchExactPattern lc pat' s'
    else .noMatch
  | .star :: pat', _ => matchStar lc pat' s
  | _, .sym _ :: _ => .symbolic
  | _ :: _, [] => .noMatch

/-- Ref: pattern.lem:match_exact — Parse and match a pattern against a string. -/
def matchExact (lc : Locale) (pat s : SymbolicString) : MatchResult SymbolicString :=
  match parsePattern (pat.filter fun | .sym _ => false | _ => true) with
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
