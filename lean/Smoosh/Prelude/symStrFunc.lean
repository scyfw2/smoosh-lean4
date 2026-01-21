import Smoosh.Compat.PervasivesExtra
import Smoosh.BuildInfo
import Smoosh.Platform.SignalPlatform
import Smoosh.Prelude.FilePerm
import Smoosh.Prelude.AST

namespace Smoosh

/-
  You should replace the fields of these constructors with your real definitions.
  The important part is: the constructor names & pattern-match shape.
-/

/-- Lem: first_is_slash : path -> bool -/
def first_is_slash (path : String) : Bool :=
  match path.toList with
  | '/' :: _ => true
  | _        => false

/-- Lem: last_is_slash : path -> bool -/
def last_is_slash (path : String) : Bool :=
  match path.toList.getLast? with
  | some '/' => true
  | _        => false

/-- Lem: join_path : path -> path -> path -/
def join_path (root ext : path) : path :=
  root ++ (if last_is_slash root then "" else "/") ++ ext

/-- Lem: null_sym : sym -> maybe bool -/
def null_sym : sym → Option Bool
  | .SymArith _   => some false
  | .SymCommand _ => none
  | .SymPat _ _ _ _ => none

/-- Lem: null_char : symbolic_char -> maybe bool -/
def null_char : symbolic_char → Option Bool
  | .C _     => some false
  | .Sym sym => null_sym sym

/-- Lem: null_string : symbolic_string -> maybe bool -/
def null_string : symbolic_string → Option Bool
  | [] => some true
  | c :: cs =>
      let only_false : Option Bool → Option Bool
        | some true  => none
        | some false => some false
        | none       => none
      match null_char c with
      | some true  => only_false (null_string cs)
      | some false => some false
      | none       => only_false (null_string cs)

/-- Lem: null_fields : fields -> maybe bool -/
def null_fields : fields → Option Bool
  | [] => some true
  | f :: fs =>
      match (null_string f, null_fields fs) with
      | (some true,  some true)  => some true
      | (some false, _)          => some false
      | (_,          some false) => some false
      | (_,          _)          => none

/-- Lem: symbolic_string_of_fields_sep : symbolic_string -> fields -> symbolic_string -/
def symbolic_string_of_fields_sep (sep : symbolic_string) : fields → symbolic_string
  | []        => []
  | [f]       => f
  | f :: fs'  => f ++ sep ++ symbolic_string_of_fields_sep sep fs'

/-- Lem: symbolic_string_of_fields : fields -> symbolic_string -/
def symbolic_string_of_fields : fields → symbolic_string :=
  symbolic_string_of_fields_sep [symbolic_char.C ' ']

/-- Lem: maximal_char_list : symbolic_string -> (list char * symbolic_string) -/
def maximal_char_list (symStr : symbolic_string) : (List Char × symbolic_string) :=
  match symStr with
  | [] => ([], [])
  | symbolic_char.C c :: rest =>
      let (cs, symStr') := maximal_char_list rest
      (c :: cs, symStr')
  | symbolic_char.Sym _ :: _ =>
      ([], symStr)

/- Lem: words_of_symbolic_string : symbolic_string -> words -/
-- partial def wordsOfSymbolicString : SymbolicString → List Entry
--   | [] => []
--   | symStr@(SymbolicChar.C _ :: _) =>
--       let (cs, symStr') := maximalCharList symStr
--       Entry.S (String.ofList cs) :: wordsOfSymbolicString symStr'
--   | SymbolicChar.Sym sym :: symStr' =>
--       Entry.ESym sym :: wordsOfSymbolicString symStr'
def words_of_symbolic_string (symStr : symbolic_string) : words :=
  let rec go (s : symbolic_string) (acc : List Char) (outRev : words) : words :=
    match s with
    | [] =>
        let outRev :=
          match acc with
          | [] => outRev
          | _  => entry.S (String.ofList acc.reverse) :: outRev
        outRev.reverse
    | symbolic_char.C c :: rest =>
        go rest (c :: acc) outRev
    | symbolic_char.Sym sym :: rest =>
        let outRev :=
          match acc with
          | [] => entry.ESym sym :: outRev
          | _  =>
              let sWord := entry.S (String.ofList acc.reverse)
              entry.ESym sym :: sWord :: outRev
        go rest [] outRev
  go symStr [] []

/-- Lem: words_of_fields : fields -> words -/
def words_of_fields : fields → words
  | []        => []
  | [ss]      => words_of_symbolic_string ss
  | ss :: fs' => words_of_symbolic_string ss ++ [entry.F] ++ words_of_fields fs'

/- Lem: expanded_words_of_symbolic_string : symbolic_string -> expanded_words -/
-- partial def expandedWordsOfSymbolicString : SymbolicString → List ExpandedWord
--   | [] => []
--   | symStr@(SymbolicChar.C _ :: _) =>
--       let (cs, symStr') := maximalCharList symStr
--       ExpandedWord.ExpS (String.ofList cs) :: expandedWordsOfSymbolicString symStr'
--   | SymbolicChar.Sym sym :: symStr' =>
--       ExpandedWord.EWSym sym :: expandedWordsOfSymbolicString symStr'
def expanded_words_of_symbolic_string (symStr : symbolic_string) : expanded_words :=
  let rec go (s : symbolic_string) (acc : List Char) (outRev : expanded_words) : expanded_words :=
    match s with
    | [] =>
        let outRev :=
          match acc with
          | [] => outRev
          | _  => expanded_word.ExpS (String.ofList acc.reverse) :: outRev
        outRev.reverse
    | symbolic_char.C c :: rest =>
        go rest (c :: acc) outRev
    | symbolic_char.Sym sym :: rest =>
        let outRev :=
          match acc with
          | [] => expanded_word.EWSym sym :: outRev
          | _  =>
              expanded_word.EWSym sym :: expanded_word.ExpS (String.ofList acc.reverse) :: outRev
        go rest [] outRev
  go symStr [] []


/-- Lem: expanded_words_of_fields : fields -> expanded_words -/
def expanded_words_of_fields : fields → expanded_words
  | []        => []
  | [ss]      => expanded_words_of_symbolic_string ss
  | ss :: fs' =>
      expanded_words_of_symbolic_string ss ++ [expanded_word.UsrF] ++ expanded_words_of_fields fs'

/-- Lem: symbolic_string_of_char_list : list char -> symbolic_string -/
def symbolic_string_of_char_list (cs : List Char) : symbolic_string :=
  cs.map symbolic_char.C

/-- Lem: symbolic_string_of_string : string -> symbolic_string -/
def symbolic_string_of_string (s : String) : symbolic_string :=
  symbolic_string_of_char_list s.toList

/-- Lem: fields_of_symbolic_string : symbolic_string -> fields -/
def fields_of_symbolic_string (s : symbolic_string) : fields :=
  [s]

/-- Lem: try_concrete : symbolic_string -> maybe string -/
def try_concrete : symbolic_string → Option String
  | [] => some ""
  | symbolic_char.C c :: vs' =>
      match try_concrete vs' with
      | none      => none
      | some tail => some (String.singleton c ++ tail)
  | symbolic_char.Sym _ :: _ =>
      none

/-- Lem: try_concrete_fields : fields -> maybe string -/
def try_concrete_fields : fields → Option String
  | [] => some ""
  | [ss] => try_concrete ss
  | ss :: fs' =>
      match try_concrete ss with
      | none => none
      | some s =>
          match try_concrete_fields fs' with
          | none => none
          | some s' => some (s ++ " " ++ s')

/-- Lem: try_concrete_fields_list : fields -> maybe (list string) -/
def try_concrete_fields_list : fields → Option (List String)
  | [] => some []
  | ss :: fs' =>
      match try_concrete ss, try_concrete_fields_list fs' with
      | some s, some rest => some (s :: rest)
      | _, _              => none

/-- Lem: pattern_escs : list char -/
def pattern_escs : List Char :=
  ("*?[" : String).toList

/-- Lem: heredoc_escs : list char -/
def heredoc_escs : List Char :=
  ("\\*?[" : String).toList

/-- Lem: escape_sc -/
def escape_sc (chars : List Char) (sc : symbolic_char) : symbolic_string :=
  match sc with
  | symbolic_char.C c =>
      if chars.contains c then
        [symbolic_char.C '\\', symbolic_char.C c]
      else
        [symbolic_char.C c]
  | _ =>
      [sc]

/-- Lem: concatMap -/
def concatMap {α β : Type} (f : α → List β) : List α → List β
  | []      => []
  | x :: xs => f x ++ concatMap f xs

/-- Lem: escape_quotes : symbolic_string -> symbolic_string -/
def escape_quotes (ss : symbolic_string) : symbolic_string :=
  concatMap (escape_sc ['"', '\\']) ss

/-- Lem: val escape_patterns : symbolic_string -> symbolic_string -/
def escape_patterns (ss : symbolic_string) : symbolic_string :=
  concatMap (escape_sc pattern_escs) ss

/-- Lem: unescape_chars : list char -> symbolic_string -> symbolic_string -/
def unescape_chars (escs : List Char) : symbolic_string → symbolic_string
  | [] => []
  | symbolic_char.C '\\' :: symbolic_char.C c :: ss' =>
      if escs.contains c then
        symbolic_char.C c :: unescape_chars escs ss'
      else
        symbolic_char.C '\\' :: symbolic_char.C c :: unescape_chars escs ss'
  | sc :: ss' =>
      sc :: unescape_chars escs ss'

/-- Lem: unescape_pattern : symbolic_string -> symbolic_string -/
def unescape_pattern : symbolic_string → symbolic_string :=
  unescape_chars pattern_escs

/-- Lem: unescape_tmp_field : tmp_field -> tmp_field -/
def unescape_tmp_field : tmp_field → tmp_field
  | .WFS      => .WFS
  | .FS       => .FS
  | .Field ss => .Field (unescape_pattern ss)
  | .QField ss => .QField ss

/-- Lem: unescape_intermediate_fields : intermediate_fields -> intermediate_fields -/
def unescape_intermediate_fields : intermediate_fields → intermediate_fields :=
  List.map unescape_tmp_field

/-- Lem: unescape_heredoc_field : tmp_field -> tmp_field -/
def unescape_heredoc_field : tmp_field → tmp_field
  | .WFS       => .WFS
  | .FS        => .FS
  | .Field ss  => .Field (unescape_chars heredoc_escs ss)
  | .QField ss => .QField (unescape_chars heredoc_escs ss)

/-- Lem: unescape_heredoc : intermediate_fields -> intermediate_fields -/
def unescape_heredoc : intermediate_fields → intermediate_fields :=
  List.map unescape_heredoc_field

/-- Lem: symbolic_string_of_expanded_words : bool (* for pattern? *) -> expanded_words -> symbolic_string -/
def symbolic_string_of_expanded_words (forPattern : Bool) : expanded_words → symbolic_string
  | [] => symbolic_string_of_string ""
  | .UsrF :: ws =>
      symbolic_string_of_string " " ++ symbolic_string_of_expanded_words forPattern ws
  | .ExpS s :: ws =>
      let ss := symbolic_string_of_string s
      (if forPattern then (concatMap (escape_sc ['"']) ss) else ss)
        ++ symbolic_string_of_expanded_words forPattern ws
  | .DQuo ss :: ws =>
      (if forPattern
       then [.C '"'] ++ escape_quotes ss ++ [.C '"']
       else ss)
        ++ symbolic_string_of_expanded_words forPattern ws
  | .At fs :: ws =>
      symbolic_string_of_fields fs ++ symbolic_string_of_expanded_words forPattern ws
  | .EWSym sym :: ws =>
      .Sym sym :: symbolic_string_of_expanded_words forPattern ws
  | .UsrS s :: ws =>
      let ss := symbolic_string_of_string s
      (if forPattern then escape_quotes ss else ss)
        ++ symbolic_string_of_expanded_words forPattern ws

/-- Lem: symbolic_string_of_intermediate_fields : intermediate_fields -> symbolic_string -/
def symbolic_string_of_intermediate_fields : intermediate_fields → symbolic_string
  | [] => []
  | .FS :: ifs' =>
      .C ' ' :: symbolic_string_of_intermediate_fields ifs'
  | .WFS :: ifs' =>
      .C ' ' :: symbolic_string_of_intermediate_fields ifs'
  | .Field s :: ifs' =>
      s ++ symbolic_string_of_intermediate_fields ifs'
  | .QField s :: ifs' =>
      [.C '"'] ++ s ++ [.C '"']
        ++ symbolic_string_of_intermediate_fields ifs'

/-- Lem: fields_of_expanded_words : expanded_words -> fields -/
def fields_of_expanded_words (w : expanded_words) : fields :=
  [symbolic_string_of_expanded_words false w]

def quoted_chars : List Char :=
  ("|&;<>()$`\\\"'*?[#˜=% \t\n" : String).toList

def escaped_chars : List Char :=
  ("$`\"\\\n" : String).toList

/-- Lem: quote_cl : list char -> list char * bool -/
def quote_cl : List Char → (List Char × Bool)
  | [] => ([], false)
  | c :: cs =>
      let (cs', needsQuotes) := quote_cl cs
      if escaped_chars.contains c then
        ('\\' :: c :: cs', true)
      else
        (c :: cs', needsQuotes || quoted_chars.contains c)

/-- Lem: quote : string -> string -/
def quote (s : String) : String :=
  let (cs, needsQuotes) := quote_cl s.toList
  let s' := String.ofList cs
  if needsQuotes then
    "\"" ++ s' ++ "\""
  else
    s'

/-- Lem: symbolic_string_of_nat : nat -> symbolic_string -/
def symbolic_string_of_nat (n : Nat) : symbolic_string :=
  symbolic_string_of_string (toString n)

/-- Lem: integerToFields : integer -> fields -/
def integerToFields (n : Int) : fields :=
  [symbolic_string_of_string (toString n)]

/-- Lem: int32ToFields : int32 -> fields -/
def int32ToFields (n : Int32) : fields :=
  [symbolic_string_of_string (toString n)]

/-- Lem: int64ToFields : int64 -> fields -/
def int64ToFields (n : Int64) : fields :=
  [symbolic_string_of_string (toString n)]





-- def renderSymbolicString : symbolic_string → String
--   | [] => ""
--   | .C c :: rest => String.singleton c ++ renderSymbolicString rest
--   | .Sym _ :: rest => "⟦SYM⟧" ++ renderSymbolicString rest

-- def entryTag : entry → String
--   | .S s    => "S(" ++ s ++ ")"
--   | .F      => "F"
--   | .ESym _ => "ESym"
--   | .K _    => "K"

-- def ewordTag : expanded_word → String
--   | .UsrF     => "UsrF"
--   | .ExpS s   => "ExpS(" ++ s ++ ")"
--   | .UsrS s   => "UsrS(" ++ s ++ ")"
--   | .At _     => "At"
--   | .DQuo _   => "DQuo"
--   | .EWSym _  => "EWSym"

-- def assertEq (name : String) (got expected : String) : String :=
--   if got = expected then
--     "OK   " ++ name ++ " = " ++ got
--   else
--     "FAIL " ++ name ++ "\n  got:      " ++ got ++ "\n  expected: " ++ expected

-- def assertBool (name : String) (got expected : Bool) : String :=
--   if got = expected then
--     "OK   " ++ name ++ " = " ++ toString got
--   else
--     "FAIL " ++ name ++ "\n  got:      " ++ toString got ++ "\n  expected: " ++ toString expected

-- def assertOptBool (name : String) (got expected : Option Bool) : String :=
--   if got = expected then
--     "OK   " ++ name ++ " = " ++ toString got
--   else
--     "FAIL " ++ name ++ "\n  got:      " ++ toString got ++ "\n  expected: " ++ toString expected

-- def assertListStr (name : String) (got expected : List String) : String :=
--   if got = expected then
--     "OK   " ++ name ++ " = " ++ toString got
--   else
--     "FAIL " ++ name ++ "\n  got:      " ++ toString got ++ "\n  expected: " ++ toString expected

-- def ssEmpty : symbolic_string := []
-- def ssAB    : symbolic_string := [.C 'a', .C 'b']

-- def sym0 : sym := .SymArith []

-- def symCmd : sym := .SymCommand stmt.Done

-- def ssWithSym : symbolic_string :=
--   [.C 'a', .Sym sym0, .C 'b']

-- def ssOnlyCmdSym : symbolic_string :=
--   [.Sym symCmd]

-- def fs1 : fields := [ssAB]
-- def fs2 : fields := [ssAB, ssWithSym, ssAB]


-- #eval assertBool "firstIsSlash(\"/abc\")" (first_is_slash "/abc") true
-- #eval assertBool "firstIsSlash(\"abc\")"  (first_is_slash "abc")  false

-- #eval assertBool "lastIsSlash(\"/abc/\")" (last_is_slash "/abc/") true
-- #eval assertBool "lastIsSlash(\"/abc\")"  (last_is_slash "/abc")  false

-- #eval assertEq "joinPath(\"/a\",\"b\")" (join_path "/a" "b") "/a/b"
-- #eval assertEq "joinPath(\"/a/\",\"b\")" (join_path "/a/" "b") "/a/b"

-- #eval assertOptBool "nullSym(SymArith [])" (null_sym sym0) (some false)
-- #eval assertOptBool "nullSym(SymCommand Done)" (null_sym symCmd) none

-- #eval assertOptBool "nullChar(C 'a')" (null_char (.C 'a')) (some false)
-- #eval assertOptBool "nullChar(Sym SymCommand)" (null_char (.Sym symCmd)) none

-- #eval assertOptBool "nullString([])"
--   (null_string (ssEmpty : symbolic_string))
--   (some true)

-- #eval assertOptBool "nullString([C a])"
--   (null_string ([.C 'a'] : symbolic_string))
--   (some false)

-- #eval assertOptBool "nullString([Sym SymCommand])"
--   (null_string (ssOnlyCmdSym : symbolic_string))
--   (none : Option Bool)

-- #eval assertOptBool "nullFields([])"
--   (null_fields ([] : fields))
--   (some true)

-- #eval assertOptBool "nullFields([[C a]])"
--   (null_fields ([[.C 'a']] : fields))
--   (some false)

-- #eval assertOptBool "nullFields([[Sym SymCommand]])"
--   (null_fields ([ssOnlyCmdSym] : fields))
--   (none : Option Bool)

-- #eval assertEq "symbolicStringOfFields([\"ab\"])"
--   (renderSymbolicString (symbolic_string_of_fields fs1))
--   "ab"

-- #eval assertEq "symbolicStringOfFieldsSep(\"-\")([\"ab\",\"ab\"])"
--   (renderSymbolicString (symbolic_string_of_fields_sep [.C '-'] [ssAB, ssAB]))
--   "ab-ab"

-- #eval
--   let (cs, _) := maximal_char_list ssWithSym
--   assertEq "maximalCharList(\"a⟦SYM⟧b\") chars" (String.ofList cs) "a"

-- #eval
--   let (_, rest) := maximal_char_list ssWithSym
--   assertEq "maximalCharList rest" (renderSymbolicString rest) "⟦SYM⟧b"

-- #eval assertListStr "wordsOfSymbolicString(\"ab\")"
--   ((words_of_symbolic_string ssAB).map entryTag)
--   ["S(ab)"]

-- #eval assertListStr "wordsOfSymbolicString(\"a⟦SYM⟧b\")"
--   ((words_of_symbolic_string ssWithSym).map entryTag)
--   ["S(a)", "ESym", "S(b)"]

-- #eval assertListStr "wordsOfFields([\"ab\",\"a⟦SYM⟧b\"])"
--   ((words_of_fields [ssAB, ssWithSym]).map entryTag)
--   ["S(ab)", "F", "S(a)", "ESym", "S(b)"]

-- #eval assertEq "escapeQuotes(\"a\\\"b\")"
--   (renderSymbolicString (escape_quotes (symbolic_string_of_string "a\"b")))
--   "a\\\"b"

-- #eval assertEq "escapePatterns(\"a*b?\")"
--   (renderSymbolicString (escape_patterns (symbolic_string_of_string "a*b?")))
--   "a\\*b\\?"

-- #eval assertEq "unescapePattern(\"a\\*b\")"
--   (renderSymbolicString (unescape_pattern (symbolic_string_of_string "a\\*b")))
--   "a*b"

-- #eval assertEq "tryConcrete(\"ab\")"
--   (match try_concrete ssAB with | some s => s | none => "<none>")
--   "ab"

-- #eval assertEq "tryConcrete(\"a⟦SYM⟧b\")"
--   (match try_concrete ssWithSym with | some s => s | none => "<none>")
--   "<none>"

-- #eval assertEq "tryConcreteFields([\"ab\",\"ab\"])"
--   (match try_concrete_fields [ssAB, ssAB] with | some s => s | none => "<none>")
--   "ab ab"

-- #eval assertEq "try_concrete_fields_list([\"ab\",\"ab\"])"
--   (match try_concrete_fields_list [ssAB, ssAB] with | some xs => toString xs | none => "<none>")
--   "List.cons \"ab\" (List.cons \"ab\" List.nil)"

-- #eval assertEq "quote(\"a $\")" (quote "a $") "\"a \\$\""
-- #eval assertEq "quote(\"hello\")" (quote "hello") "hello"

end Smoosh
