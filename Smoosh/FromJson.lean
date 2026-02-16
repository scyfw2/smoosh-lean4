/-
  Smoosh.FromJson — JSON deserialization for Smoosh AST types.
  Converts JSON produced by OCaml `dump_ast` (via `shim.ml:json_of_stmt`) into Lean `Stmt`/`Entry` types.

  ✨ Lean-only module — no OCaml counterpart. The OCaml side serializes via `shim.ml:write_json`.
-/
import Smoosh.Prelude

namespace Smoosh.FromJson

-- Inhabited instances for mutual inductive types (needed for partial defs)
instance : Inhabited Stmt := ⟨.done⟩
instance : Inhabited Entry := ⟨.s ""⟩
instance : Inhabited Format := ⟨.normal⟩
instance : Inhabited Control := ⟨.escape ' '⟩
instance : Inhabited ExpandedWord := ⟨.usrF⟩
instance : Inhabited SymbolicChar := ⟨.c ' '⟩
instance : Inhabited Redir := ⟨.rfile .to 1 []⟩

/-! # Minimal JSON value type -/

inductive JValue where
  | null
  | bool (b : Bool)
  | num (n : Int)
  | str (s : String)
  | arr (vs : List JValue)
  | obj (kvs : List (String × JValue))
  deriving Repr, Inhabited

def JValue.field? (j : JValue) (key : String) : Option JValue :=
  match j with
  | .obj kvs => kvs.find? (fun (k, _) => k == key) |>.map (·.2)
  | _ => none

def JValue.asStr? : JValue → Option String
  | .str s => some s
  | _ => none

def JValue.asNat? : JValue → Option Nat
  | .num n => if n >= 0 then some n.toNat else none
  | _ => none

def JValue.asBool? : JValue → Option Bool
  | .bool b => some b
  | _ => none

def JValue.asArr? : JValue → Option (List JValue)
  | .arr vs => some vs
  | _ => none

def JValue.tag? (j : JValue) : Option String :=
  j.field? "tag" >>= JValue.asStr?

/-! # JSON parser operating on List Char -/

-- All JSON parsing uses List Char to avoid String.Pos API issues
/-- Parse a JSON value from a character list. Returns (value, remaining chars).
    Uses recursive descent — handles strings, objects, arrays, numbers, booleans, null. -/
partial def parseJsonValue (cs : List Char) : Option (JValue × List Char) :=
  let cs := skipWs cs
  match cs with
  | [] => none
  | '"' :: rest => parseJsonStr rest []
  | '{' :: rest => parseJsonObj (skipWs rest)
  | '[' :: rest => parseJsonArr (skipWs rest)
  | 't' :: 'r' :: 'u' :: 'e' :: rest => some (.bool true, rest)
  | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest => some (.bool false, rest)
  | 'n' :: 'u' :: 'l' :: 'l' :: rest => some (.null, rest)
  | '-' :: rest =>
    match parseDigits rest 0 with
    | (n, rest') => some (.num (-↑n), skipFracExp rest')
  | c :: _ =>
    if '0' ≤ c ∧ c ≤ '9' then
      match parseDigits cs 0 with
      | (n, rest) => some (.num (↑n), skipFracExp rest)
    else none
where
  skipWs : List Char → List Char
    | ' ' :: r | '\n' :: r | '\r' :: r | '\t' :: r => skipWs r
    | cs => cs

  parseDigits (cs : List Char) (acc : Nat) : Nat × List Char :=
    match cs with
    | c :: rest =>
      if '0' ≤ c ∧ c ≤ '9'
      then parseDigits rest (acc * 10 + (c.toNat - '0'.toNat))
      else (acc, cs)
    | [] => (acc, [])

  skipFracExp (cs : List Char) : List Char :=
    let cs := match cs with
      | '.' :: rest => (parseDigits rest 0).2
      | _ => cs
    match cs with
    | 'e' :: rest | 'E' :: rest =>
      let rest := match rest with
        | '+' :: r | '-' :: r => r
        | r => r
      (parseDigits rest 0).2
    | _ => cs

  parseJsonStr (cs : List Char) (acc : List Char) : Option (JValue × List Char) :=
    match cs with
    | [] => none
    | '"' :: rest => some (.str (String.ofList acc.reverse), rest)
    | '\\' :: 'n' :: rest => parseJsonStr rest ('\n' :: acc)
    | '\\' :: 't' :: rest => parseJsonStr rest ('\t' :: acc)
    | '\\' :: 'r' :: rest => parseJsonStr rest ('\r' :: acc)
    | '\\' :: '"' :: rest => parseJsonStr rest ('"' :: acc)
    | '\\' :: '\\' :: rest => parseJsonStr rest ('\\' :: acc)
    | '\\' :: '/' :: rest => parseJsonStr rest ('/' :: acc)
    | '\\' :: 'u' :: _ :: _ :: _ :: _ :: rest => parseJsonStr rest ('?' :: acc) -- simplified
    | '\\' :: c :: rest => parseJsonStr rest (c :: acc)
    | c :: rest => parseJsonStr rest (c :: acc)

  parseJsonObj (cs : List Char) : Option (JValue × List Char) :=
    match cs with
    | '}' :: rest => some (.obj [], rest)
    | _ => parseObjFields cs []

  parseObjFields (cs : List Char) (acc : List (String × JValue)) : Option (JValue × List Char) :=
    let cs := skipWs cs
    match cs with
    | '"' :: rest =>
      match parseJsonStr rest [] with
      | some (.str key, rest) =>
        let rest := skipWs rest
        match rest with
        | ':' :: rest =>
          match parseJsonValue rest with
          | some (val, rest) =>
            let rest := skipWs rest
            match rest with
            | ',' :: rest => parseObjFields rest ((key, val) :: acc)
            | '}' :: rest => some (.obj ((key, val) :: acc).reverse, rest)
            | _ => none
          | none => none
        | _ => none
      | _ => none
    | _ => none

  parseJsonArr (cs : List Char) : Option (JValue × List Char) :=
    match cs with
    | ']' :: rest => some (.arr [], rest)
    | _ => parseArrElems cs []

  parseArrElems (cs : List Char) (acc : List JValue) : Option (JValue × List Char) :=
    match parseJsonValue cs with
    | some (val, rest) =>
      let rest := skipWs rest
      match rest with
      | ',' :: rest => parseArrElems rest (val :: acc)
      | ']' :: rest => some (.arr (val :: acc).reverse, rest)
      | _ => none
    | none => none

/-- Parse a complete JSON string into a `JValue`. -/
def parseJsonTop (input : String) : Option JValue :=
  match parseJsonValue input.toList with
  | some (v, _) => some v
  | none => none

/-! # AST Deserialization -/

mutual

/-- Deserialize a `Format` (parameter expansion format) from JSON.
    Ref: corresponds to OCaml `shim.ml:json_of_format` (serializer). -/
partial def formatOfJson (j : JValue) : Format :=
  match j.tag? with
  | some "Normal" => .normal
  | some "Length" => .length_
  | some "Default" => .default_ (wordsOfJson (j.field? "w"))
  | some "NDefault" => .ndefault (wordsOfJson (j.field? "w"))
  | some "Assign" => .assign (wordsOfJson (j.field? "w"))
  | some "NAssign" => .nassign (wordsOfJson (j.field? "w"))
  | some "Error" => .error (wordsOfJson (j.field? "w"))
  | some "NError" => .nerror (wordsOfJson (j.field? "w"))
  | some "Alt" => .alt (wordsOfJson (j.field? "w"))
  | some "NAlt" => .nalt (wordsOfJson (j.field? "w"))
  | some "Substring" =>
    let side := match j.field? "side" >>= JValue.asStr? with
      | some "Prefix" => SubstringSide.prefix_
      | _ => SubstringSide.suffix_
    let mode := match j.field? "mode" >>= JValue.asStr? with
      | some "Shortest" => SubstringMode.shortest
      | _ => SubstringMode.longest
    .substring side mode (wordsOfJson (j.field? "w"))
  | _ => .normal

/-- Deserialize a `Control` (tilde, param, backtick, arith, quote, escape) from JSON. -/
partial def controlOfJson (j : JValue) : Control :=
  match j.tag? with
  | some "Tilde" =>
    .tilde ((j.field? "prefix" >>= JValue.asStr?).getD "")
  | some "Param" =>
    let var := (j.field? "var" >>= JValue.asStr?).getD ""
    let fmt := match j.field? "fmt" with
      | some f => formatOfJson f
      | none => .normal
    .param var fmt
  | some "Backtick" =>
    match j.field? "stmt" with
    | some s => .backtick (stmtOfJson s)
    | none => .backtick .done
  | some "Arith" =>
    .arith [] (wordsOfJson (j.field? "w"))
  | some "Quote" =>
    .quote [] (wordsOfJson (j.field? "w"))
  | some "Escape" =>
    let ch := match j.field? "character" >>= JValue.asStr? with
      | some s => match s.toList with | [c] => c | _ => ' '
      | none => ' '
    .escape ch
  | _ => .escape ' '

/-- Deserialize a word `Entry` (S=string, K=control, F=field separator) from JSON. -/
partial def entryOfJson (j : JValue) : Entry :=
  match j.tag? with
  | some "S" => .s ((j.field? "v" >>= JValue.asStr?).getD "")
  | some "K" =>
    match j.field? "v" with
    | some v => .k (controlOfJson v)
    | none => .s ""
  | some "F" => .f
  | _ => .s ""

/-- Deserialize a word list from an optional JSON array. -/
partial def wordsOfJson (mj : Option JValue) : List Entry :=
  match mj >>= JValue.asArr? with
  | some ws => ws.map entryOfJson
  | none => []

/-- Deserialize a `Redir` (file, dup, heredoc) from JSON. -/
partial def redirOfJson (j : JValue) : Redir :=
  match j.tag? with
  | some "File" =>
    let ty := match j.field? "ty" >>= JValue.asStr? with
      | some "To" => RedirType.to | some "Clobber" => .clobber
      | some "From" => .from_ | some "FromTo" => .fromTo
      | some "Append" => .append | _ => .to
    .rfile ty ((j.field? "src" >>= JValue.asNat?).getD 1) (wordsOfJson (j.field? "tgt"))
  | some "Dup" =>
    let ty := match j.field? "ty" >>= JValue.asStr? with
      | some "ToFD" => DupType.toFD | some "FromFD" => .fromFD | _ => .toFD
    .rdup ty ((j.field? "src" >>= JValue.asNat?).getD 1) (wordsOfJson (j.field? "tgt"))
  | some "Heredoc" =>
    let ty := match j.field? "ty" >>= JValue.asStr? with
      | some "Here" => HeredocType.here | some "XHere" => .xhere | _ => .here
    .rheredoc ty ((j.field? "src" >>= JValue.asNat?).getD 0) (wordsOfJson (j.field? "w"))
  | _ => .rfile .to 1 []

/-- Deserialize a `Stmt` from JSON. This is the main AST deserialization entry point.
    Handles all statement types: Command, Semi, And, Or, Not, Pipe, Redir, Background,
    Subshell, If, While, For, Case, Defun. -/
partial def stmtOfJson (j : JValue) : Stmt :=
  match j.tag? with
  | some "Command" =>
    let assigns := match j.field? "assigns" >>= JValue.asArr? with
      | some as_ => as_.filterMap fun a =>
          match a.field? "var" >>= JValue.asStr? with
          | some v => some (v, wordsOfJson (a.field? "value"))
          | none => none
      | none => []
    let rs := match j.field? "rs" >>= JValue.asArr? with
      | some rs => rs.map redirOfJson | none => []
    .command assigns (wordsOfJson (j.field? "args")) rs defaultCmdOpts
  | some "Semi" => .semi (sf j "l") (sf j "r")
  | some "And" => .and_ (sf j "l") (sf j "r")
  | some "Or" => .or_ (sf j "l") (sf j "r")
  | some "Not" => .not_ (sf j "c")
  | some "Pipe" =>
    let bg := (j.field? "bg" >>= JValue.asBool?).getD false
    let cs := match j.field? "cs" >>= JValue.asArr? with
      | some cs => cs.map stmtOfJson | none => []
    .pipe (if bg then .bg else .fg) cs
  | some "Redir" =>
    let rs := match j.field? "rs" >>= JValue.asArr? with
      | some rs => rs.map redirOfJson | none => []
    .redir (sf j "c") ([], none, rs)
  | some "Background" =>
    let rs := match j.field? "rs" >>= JValue.asArr? with
      | some rs => rs.map redirOfJson | none => []
    .background (sf j "c") ([], none, rs)
  | some "Subshell" =>
    let rs := match j.field? "rs" >>= JValue.asArr? with
      | some rs => rs.map redirOfJson | none => []
    .subshell (sf j "c") ([], none, rs)
  | some "If" => .if_ (sf j "c") (sf j "t") (sf j "e")
  | some "While" => .while_ (sf j "cond") (sf j "body")
  | some "For" =>
    .for_ ((j.field? "var" >>= JValue.asStr?).getD "x") (wordsOfJson (j.field? "args")) (sf j "body")
  | some "Case" =>
    let cases := match j.field? "cases" >>= JValue.asArr? with
      | some cs => cs.filterMap fun c =>
          match c.field? "pats" >>= JValue.asArr?, c.field? "stmt" with
          | some pats, some stmt =>
            let pl := pats.filterMap fun p => match p with
              | .arr ws => some (ws.map entryOfJson) | _ => none
            some (pl, stmtOfJson stmt)
          | _, _ => none
      | none => []
    .case_ (wordsOfJson (j.field? "args")) cases
  | some "Defun" =>
    .defun ((j.field? "name" >>= JValue.asStr?).getD "") (sf j "body")
  | _ => .done

/-- Helper: look up a key in a JSON object and deserialize it as a `Stmt`. -/
partial def sf (j : JValue) (key : String) : Stmt :=
  match j.field? key with
  | some v => stmtOfJson v
  | none => .done

end -- mutual

/-- Parse a JSON string into a Stmt -/
def parseAst (jsonStr : String) : Option Stmt :=
  match parseJsonTop jsonStr with
  | some j => some (stmtOfJson j)
  | none => none

end Smoosh.FromJson
