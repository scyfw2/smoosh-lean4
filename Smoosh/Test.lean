/-
  Smoosh.Test — POSIX test/[ expression parsing and evaluation
  Translated from test.lem (275 lines)
-/
import Smoosh.Os

/-! # Test expression AST -/

inductive TestExpr where
  -- Unary file tests
  | testBlock (path : Path)               -- -b
  | testCharacter (path : Path)           -- -c
  | testDirectory (path : Path)           -- -d
  | testExists (path : Path)              -- -e
  | testFile (path : Path)                -- -f
  | testSetgid (path : Path)              -- -g
  | testSymlink (path : Path)             -- -h, -L
  | testSticky (path : Path)              -- -k (extension)
  | testFifo (path : Path)                -- -p
  | testReadable (path : Path)            -- -r
  | testSocket (path : Path)              -- -S
  | testNonemptyFile (path : Path)        -- -s
  | testTerminalFD (fd : Fd)              -- -t
  | testSetuid (path : Path)              -- -u
  | testWriteable (path : Path)           -- -w
  | testExecutable (path : Path)          -- -x
  -- Unary string test
  | testEmptyStr (str : String)           -- -z
  -- Binary string tests
  | testEqStr (str1 str2 : String)        -- =, !=
  | testGtStr (str1 str2 : String)        -- >
  -- Binary numeric tests
  | testEqNum (n1 n2 : Int)              -- -eq
  | testGtNum (n1 n2 : Int)              -- -gt
  -- Non-standard binary file tests
  | testNewerFile (f1 f2 : String)        -- -nt
  | testOlderFile (f1 f2 : String)        -- -ot
  | testSameFile (f1 f2 : String)         -- -ef
  -- Logical connectives
  | testAnd (e1 e2 : TestExpr)            -- -a
  | testOr (e1 e2 : TestExpr)             -- -o
  | testNot (e : TestExpr)                -- !

/-! # Pretty-printing -/

mutual
partial def stringOfTestExpr (expr : TestExpr) : String :=
  stringOfTestDisjunction expr

partial def stringOfTestDisjunction : TestExpr → String
  | .testOr lhs rhs =>
    stringOfTestConjunction lhs ++ " -o " ++ stringOfTestDisjunction rhs
  | expr => stringOfTestConjunction expr

partial def stringOfTestConjunction : TestExpr → String
  | .testAnd lhs rhs =>
    stringOfTestNegation lhs ++ " -a " ++ stringOfTestConjunction rhs
  | expr => stringOfTestNegation expr

partial def stringOfTestNegation : TestExpr → String
  | .testNot (.testEqStr s1 s2) => s1 ++ " != " ++ s2
  | .testNot (.testEqNum n1 n2) => Int.repr n1 ++ " -ne " ++ Int.repr n2
  | .testNot (.testGtNum n1 n2) => Int.repr n2 ++ " -le " ++ Int.repr n1
  | .testNot (.testEmptyStr s) => "-n " ++ s
  | .testNot expr => "! " ++ stringOfTestEquality expr
  | expr => stringOfTestEquality expr

partial def stringOfTestEquality : TestExpr → String
  | .testEqStr s1 s2 => s1 ++ " = " ++ s2
  | .testGtStr s1 s2 => s1 ++ " \\> " ++ s2
  | .testNewerFile s1 s2 => s1 ++ " -nt " ++ s2
  | .testOlderFile s1 s2 => s1 ++ " -ot " ++ s2
  | .testSameFile s1 s2 => s1 ++ " -ef " ++ s2
  | .testEqNum n1 n2 => Int.repr n1 ++ " -eq " ++ Int.repr n2
  | .testGtNum n1 n2 => Int.repr n1 ++ " -gt " ++ Int.repr n2
  | expr => stringOfTestUnary expr

partial def stringOfTestUnary : TestExpr → String
  | .testBlock path => "-b " ++ path
  | .testCharacter path => "-c " ++ path
  | .testDirectory path => "-d " ++ path
  | .testExists path => "-e " ++ path
  | .testFile path => "-f " ++ path
  | .testSetgid path => "-g " ++ path
  | .testSymlink path => "-L " ++ path
  | .testSticky path => "-k " ++ path
  | .testFifo path => "-p " ++ path
  | .testReadable path => "-r " ++ path
  | .testSocket path => "-S " ++ path
  | .testNonemptyFile path => "-s " ++ path
  | .testTerminalFD fd => "-t " ++ Nat.repr fd
  | .testSetuid path => "-u " ++ path
  | .testWriteable path => "-w " ++ path
  | .testExecutable path => "-x " ++ path
  | .testEmptyStr s => "-z " ++ s
  | expr => "\\(" ++ stringOfTestDisjunction expr ++ "\\)"
end

/-! # Parser helpers -/

def readTwoNats (num1 num2 op : String) : Except String (Int × Int) :=
  match readSignedInteger 10 num1.toList, readSignedInteger 10 num2.toList with
  | .ok n1, .ok n2 => .ok (n1, n2)
  | .error msg, _ =>
    .error s!"expected number before {op}, found '{num1}' ({msg})"
  | _, .error msg =>
    .error s!"expected number after {op}, found '{num2}' ({msg})"

/-! # Recursive-descent parser -/

mutual
partial def parseTestExprDisjunction (toks : List String)
    : Except String (TestExpr × List String) :=
  match parseTestExprConjunction toks with
  | .error msg => .error msg
  | .ok (lhs, "-o" :: toks') =>
    match parseTestExprDisjunction toks' with
    | .error msg => .error msg
    | .ok (rhs, toks'') => .ok (.testOr lhs rhs, toks'')
  | .ok (expr, toks') => .ok (expr, toks')

partial def parseTestExprConjunction (toks : List String)
    : Except String (TestExpr × List String) :=
  match parseTestExprNegation toks with
  | .error msg => .error msg
  | .ok (lhs, "-a" :: toks') =>
    match parseTestExprConjunction toks' with
    | .error msg => .error msg
    | .ok (rhs, toks'') => .ok (.testAnd lhs rhs, toks'')
  | .ok (expr, toks') => .ok (expr, toks')

partial def parseTestExprNegation (toks : List String)
    : Except String (TestExpr × List String) :=
  match toks with
  | "!" :: toks' =>
    match parseTestExprEquality toks' with
    | .error msg => .error msg
    | .ok (expr, toks'') => .ok (.testNot expr, toks'')
  | _ => parseTestExprEquality toks

partial def parseTestExprEquality (toks : List String)
    : Except String (TestExpr × List String) :=
  match toks with
  | str1 :: "=" :: str2 :: toks' => .ok (.testEqStr str1 str2, toks')
  | str1 :: "!=" :: str2 :: toks' => .ok (.testNot (.testEqStr str1 str2), toks')
  | str1 :: ">" :: str2 :: toks' => .ok (.testGtStr str1 str2, toks')
  | str1 :: "<" :: str2 :: toks' => .ok (.testGtStr str2 str1, toks')
  | str1 :: "-nt" :: str2 :: toks' => .ok (.testNewerFile str1 str2, toks')
  | str1 :: "-ot" :: str2 :: toks' => .ok (.testOlderFile str1 str2, toks')
  | str1 :: "-ef" :: str2 :: toks' => .ok (.testSameFile str1 str2, toks')
  | num1 :: op :: num2 :: toks' =>
    if ! ["-eq", "-ne", "-gt", "-ge", "-lt", "-le"].contains op
    then parseTestExprUnary toks
    else
      match readTwoNats num1 num2 op with
      | .error msg => .error msg
      | .ok (n1, n2) =>
        match op with
        | "-eq" => .ok (.testEqNum n1 n2, toks')
        | "-ne" => .ok (.testNot (.testEqNum n1 n2), toks')
        | "-gt" => .ok (.testGtNum n1 n2, toks')
        | "-ge" => .ok (.testNot (.testGtNum n2 n1), toks')
        | "-lt" => .ok (.testGtNum n2 n1, toks')
        | "-le" => .ok (.testNot (.testGtNum n1 n2), toks')
        | _ => .error s!"parse_test_expr_equality: unexpected operation {op}"
  | _ => parseTestExprUnary toks

partial def parseTestExprUnary (toks : List String)
    : Except String (TestExpr × List String) :=
  match toks with
  | "-b" :: path :: toks' => .ok (.testBlock path, toks')
  | "-c" :: path :: toks' => .ok (.testCharacter path, toks')
  | "-d" :: path :: toks' => .ok (.testDirectory path, toks')
  | "-e" :: path :: toks' => .ok (.testExists path, toks')
  | "-f" :: path :: toks' => .ok (.testFile path, toks')
  | "-g" :: path :: toks' => .ok (.testSetgid path, toks')
  | "-h" :: path :: toks' => .ok (.testSymlink path, toks')
  | "-L" :: path :: toks' => .ok (.testSymlink path, toks')
  | "-k" :: path :: toks' => .ok (.testSticky path, toks')
  | "-n" :: str :: toks' => .ok (.testNot (.testEmptyStr str), toks')
  | "-p" :: path :: toks' => .ok (.testFifo path, toks')
  | "-r" :: path :: toks' => .ok (.testReadable path, toks')
  | "-S" :: path :: toks' => .ok (.testSocket path, toks')
  | "-s" :: path :: toks' => .ok (.testNonemptyFile path, toks')
  | "-t" :: fdStr :: toks' =>
    match readNat fdStr.toList with
    | .error msg => .error s!"expected fd number after -t, found '{fdStr}' ({msg})"
    | .ok fd => .ok (.testTerminalFD fd, toks')
  | "-u" :: path :: toks' => .ok (.testSetuid path, toks')
  | "-w" :: path :: toks' => .ok (.testWriteable path, toks')
  | "-x" :: path :: toks' => .ok (.testExecutable path, toks')
  | "-z" :: str :: toks' => .ok (.testEmptyStr str, toks')
  | "(" :: toks' =>
    match parseTestExprDisjunction toks' with
    | .error msg => .error msg
    | .ok (expr, ")" :: toks'') => .ok (expr, toks'')
    | .ok (expr, tok :: _) =>
      .error s!"expected ')' after {stringOfTestExpr expr}, found '{tok}'"
    | .ok (expr, []) =>
      .error s!"expected ')' after {stringOfTestExpr expr}, found end of input"
  -- plain strings are tested for non-nullness
  | str :: toks' => .ok (.testNot (.testEmptyStr str), toks')
  | [] => .error "expected unary operator, found end of input"
end

def parseTestExpr (toks : List String) : Except String TestExpr :=
  match parseTestExprDisjunction toks with
  | .error err => .error s!"parse error in '{String.intercalate " " toks}': {err}"
  | .ok (expr, []) => .ok expr
  | .ok (expr, restToks) =>
    .error s!"unexpected input after {stringOfTestExpr expr}: {String.intercalate " " restToks}"

/-! # Evaluator -/

partial def evalTestExpr [OS α] (os : OsState α) : TestExpr → Bool
  | .testBlock path => OS.osFileTypeFollow os path == some .fileBlock
  | .testCharacter path => OS.osFileTypeFollow os path == some .fileChar
  | .testDirectory path => OS.osFileTypeFollow os path == some .fileDirectory
  | .testExists path => OS.osFileExists os path
  | .testFile path => OS.osFileTypeFollow os path == some .fileRegular
  | .testSetgid path =>
    match OS.osFilePerms os path with
    | none => false
    | some perms => perms.setgid
  | .testSymlink path => OS.osFileType os path == some .fileSymlink
  | .testSticky path =>
    match OS.osFilePerms os path with
    | none => false
    | some perms => perms.sticky
  | .testFifo path => OS.osFileTypeFollow os path == some .filePipe
  | .testReadable path => OS.osIsReadable os path
  | .testSocket path => OS.osFileTypeFollow os path == some .fileSocket
  | .testNonemptyFile path =>
    match OS.osFileSize os path with
    | none => false
    | some 0 => false
    | some _ => true
  | .testTerminalFD fd => OS.osIsTty os fd
  | .testSetuid path =>
    match OS.osFilePerms os path with
    | none => false
    | some perms => perms.setuid
  | .testWriteable path => OS.osIsWriteable os path
  | .testExecutable path => OS.osIsExecutable os path
  | .testEmptyStr str => str == ""
  | .testEqStr str1 str2 => str1 == str2
  | .testGtStr str1 str2 => str1 > str2
  | .testEqNum n1 n2 => n1 == n2
  | .testGtNum n1 n2 => n1 > n2
  | .testNewerFile f1 f2 =>
    match OS.osFileMtime os f1, OS.osFileMtime os f2 with
    | none, _ => false
    | some _, none => true
    | some t1, some t2 => t1 > t2
  | .testOlderFile f1 f2 =>
    match OS.osFileMtime os f1, OS.osFileMtime os f2 with
    | none, none => false
    | none, some _ => true
    | some _, none => false
    | some t1, some t2 => t1 < t2
  | .testSameFile f1 f2 =>
    match OS.osFileNumber os f1, OS.osFileNumber os f2 with
    | none, _ => false
    | _, none => false
    | some (dev1, ino1), some (dev2, ino2) => dev1 == dev2 && ino1 == ino2
  | .testAnd e1 e2 => evalTestExpr os e1 && evalTestExpr os e2
  | .testOr e1 e2 => evalTestExpr os e1 || evalTestExpr os e2
  | .testNot e => ! evalTestExpr os e
