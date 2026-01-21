import Smoosh.Smoosh
import Smoosh.Num

namespace Smoosh
open Smoosh.Num
/-
(* TODO dash supports other flags:
   -O, -G (owner/group tests)
 *)
-/

inductive test_expr : Type
  -- UNARY; encoding -n (nonempy string)
  | TestBlock         (p : path)                 -- -b
  | TestCharacter     (p : path)                 -- -c
  | TestDirectory     (p : path)                 -- -d
  | TestExists        (p : path)                 -- -e
  | TestFile          (p : path)                 -- -f
  | TestSetgid        (p : path)                 -- -g
  | TestSymlink       (p : path)                 -- -h, -L
  | TestSticky        (p : path)                 -- -k [extension, from dash]
  | TestFifo          (p : path)                 -- -p
  | TestReadable      (p : path)                 -- -r
  | TestSocket        (p : path)                 -- -S
  | TestNonempty_file (p : path)                 -- -s
  | TestTerminalFD    (d : fd)                   -- -t
  | TestSetuid        (p : path)                 -- -u
  | TestWriteable     (p : path)                 -- -w
  | TestExecutable    (p : path)                 -- -x
  | TestEmpty_str     (s : String)               -- -z

  -- BINARY; we encode negated forms, ge, lt, and le
  | TestEq_str (s1 s2 : String)                  -- =  (along w/ !=)
  | TestGt_str (s1 s2 : String)                  -- >  (extension, from dash)
  | TestEq_num (n1 n2 : Int)                 -- -eq
  | TestGt_num (n1 n2 : Int)                 -- -gt

  -- NON-STANDARD BINARY
  | TestNewerFile (f1 f2 : String)               -- -nt
  | TestOlderFile (f1 f2 : String)               -- -ot
  | TestSameFile  (f1 f2 : String)               -- -ef

  -- TRICKSY
  | TestAnd (e1 e2 : test_expr)                  -- -a
  | TestOr  (e1 e2 : test_expr)                  -- -o
  | TestNot (e : test_expr)                      -- !
deriving Repr

-- string_of_test_expr : test_expr -> string -/
mutual
  partial def string_of_test_expr (expr : test_expr) : String :=
    string_of_test_expr_disjunction expr

  partial def string_of_test_expr_disjunction (expr : test_expr) : String :=
    match expr with
    | .TestOr lhs rhs =>
        string_of_test_expr_conjunction lhs ++ " -o " ++ string_of_test_expr_disjunction rhs
    | _ => string_of_test_expr_conjunction expr

  partial def string_of_test_expr_conjunction (expr : test_expr) : String :=
    match expr with
    | .TestAnd lhs rhs =>
        string_of_test_expr_negation lhs ++ " -a " ++ string_of_test_expr_conjunction rhs
    | _ => string_of_test_expr_negation expr

  partial def string_of_test_expr_negation (expr : test_expr) : String :=
    match expr with
    | .TestNot (.TestEq_str str1 str2) => str1 ++ " != " ++ str2
    | .TestNot (.TestEq_num n1 n2)     => Read.write n1 ++ " -ne " ++ Read.write n2
    | .TestNot (.TestGt_num n1 n2)     => Read.write n2 ++ " -le " ++ Read.write n1
    | .TestNot (.TestEmpty_str str)    => "-n " ++ str
    | .TestNot e                       => "! " ++ string_of_test_expr_equality e
    | _                                 => string_of_test_expr_equality expr

  partial def string_of_test_expr_equality (expr : test_expr) : String :=
    match expr with
    | .TestEq_str    str1 str2 => str1 ++ " = "  ++ str2
    | .TestGt_str    str1 str2 => str1 ++ " \\> " ++ str2
    | .TestNewerFile str1 str2 => str1 ++ " -nt " ++ str2
    | .TestOlderFile str1 str2 => str1 ++ " -ot " ++ str2
    | .TestSameFile  str1 str2 => str1 ++ " -ef " ++ str2
    | .TestEq_num    n1   n2   => Read.write n1 ++ " -eq " ++ Read.write n2
    | .TestGt_num    n1   n2   => Read.write n1 ++ " -gt " ++ Read.write n2
    | _                         => string_of_test_expr_unary expr

  partial def string_of_test_expr_unary (expr : test_expr) : String :=
    match expr with
    | .TestBlock p         => "-b " ++ p
    | .TestCharacter p     => "-c " ++ p
    | .TestDirectory p     => "-d " ++ p
    | .TestExists p        => "-e " ++ p
    | .TestFile p          => "-f " ++ p
    | .TestSetgid p        => "-g " ++ p
    | .TestSymlink p       => "-L " ++ p
    | .TestSticky p        => "-k " ++ p
    | .TestFifo p          => "-p " ++ p
    | .TestReadable p      => "-r " ++ p
    | .TestSocket p        => "-S " ++ p
    | .TestNonempty_file p => "-s " ++ p
    | .TestTerminalFD d    => "-t " ++ stringFromNat d
    | .TestSetuid p        => "-u " ++ p
    | .TestWriteable p     => "-w " ++ p
    | .TestExecutable p    => "-x " ++ p
    | .TestEmpty_str s     => "-z " ++ s
    | e                    => "\\(" ++ string_of_test_expr_disjunction e ++ "\\)"
end

/-
Parsing
-/

abbrev ParseResult := Except String (test_expr × List String)

-- def parse_test_expr_disjunction  : List String → ParseResult := fun _ => .error "stub"
-- def parse_test_expr_conjunction  : List String → ParseResult := fun _ => .error "stub"
-- def parse_test_expr_negation     : List String → ParseResult := fun _ => .error "stub"
-- def parse_test_expr_equality     : List String → ParseResult := fun _ => .error "stub"
-- def parse_test_expr_unary        : List String → ParseResult := fun _ => .error "stub"

def read_two_nats (num1 num2 op : String) : Except String (Int × Int) :=
  match Num.readSignedInteger 10 (toCharList num1), Num.readSignedInteger 10 (toCharList num2) with
  | .ok n1, .ok n2 => .ok (n1, n2)
  | .error msg, _  =>
      .error ("expected number before " ++ op ++ ", found '" ++ num1 ++ "' (" ++ msg ++ ")")
  | _, .error msg  =>
      .error ("expected number after " ++ op ++ ", found '" ++ num2 ++ "' (" ++ msg ++ ")")

mutual
  partial def parse_test_expr_disjunction (toks : List String) : ParseResult :=
    match parse_test_expr_conjunction toks with
    | .error msg => .error msg
    | .ok (lhs, "-o" :: toks') =>
        match parse_test_expr_disjunction toks' with
        | .error msg => .error msg
        | .ok (rhs, toks'') => .ok (.TestOr lhs rhs, toks'')
    | .ok (expr, toks') => .ok (expr, toks')

  partial def parse_test_expr_conjunction (toks : List String) : ParseResult :=
    match parse_test_expr_negation toks with
    | .error msg => .error msg
    | .ok (lhs, "-a" :: toks') =>
        match parse_test_expr_conjunction toks' with
        | .error msg => .error msg
        | .ok (rhs, toks'') => .ok (.TestAnd lhs rhs, toks'')
    | .ok (expr, toks') => .ok (expr, toks')

  partial def parse_test_expr_negation (toks : List String) : ParseResult :=
    match toks with
    | "!" :: toks' =>
        match parse_test_expr_equality toks' with
        | .error msg => .error msg
        | .ok (expr, toks'') => .ok (.TestNot expr, toks'')
    | _ => parse_test_expr_equality toks

  partial def parse_test_expr_equality (toks : List String) : ParseResult :=
    match toks with
    | str1 :: "="  :: str2 :: toks' => .ok (.TestEq_str str1 str2, toks')
    | str1 :: "!=" :: str2 :: toks' => .ok (.TestNot (.TestEq_str str1 str2), toks')
    | str1 :: ">"  :: str2 :: toks' => .ok (.TestGt_str str1 str2, toks')
    | str1 :: "<"  :: str2 :: toks' => .ok (.TestGt_str str2 str1, toks')
    | str1 :: "-nt" :: str2 :: toks' => .ok (.TestNewerFile str1 str2, toks')
    | str1 :: "-ot" :: str2 :: toks' => .ok (.TestOlderFile str1 str2, toks')
    | str1 :: "-ef" :: str2 :: toks' => .ok (.TestSameFile  str1 str2, toks')
    | num1 :: op :: num2 :: toks' =>
        let ops : List String := ["-eq", "-ne", "-gt", "-ge", "-lt", "-le"]
        if !(op ∈ ops) then
          parse_test_expr_unary toks
        else
          match read_two_nats num1 num2 op with
          | .error msg => .error msg
          | .ok (n1, n2) =>
              match op with
              | "-eq" => .ok (.TestEq_num n1 n2, toks')
              | "-ne" => .ok (.TestNot (.TestEq_num n1 n2), toks')
              | "-gt" => .ok (.TestGt_num n1 n2, toks')
              | "-ge" => .ok (.TestNot (.TestGt_num n2 n1), toks')
              | "-lt" => .ok (.TestGt_num n2 n1, toks')
              | "-le" => .ok (.TestNot (.TestGt_num n1 n2), toks')
              | _ =>
                  .error
                    ("parse_test_expr_equality: unexpected operation " ++ op)
    | _ => parse_test_expr_unary toks

  partial def parse_test_expr_unary (toks : List String) : ParseResult :=
    match toks with
    | "-b" :: p :: toks' => .ok (.TestBlock p, toks')
    | "-c" :: p :: toks' => .ok (.TestCharacter p, toks')
    | "-d" :: p :: toks' => .ok (.TestDirectory p, toks')
    | "-e" :: p :: toks' => .ok (.TestExists p, toks')
    | "-f" :: p :: toks' => .ok (.TestFile p, toks')
    | "-g" :: p :: toks' => .ok (.TestSetgid p, toks')
    | "-h" :: p :: toks' => .ok (.TestSymlink p, toks')
    | "-L" :: p :: toks' => .ok (.TestSymlink p, toks')
    | "-k" :: p :: toks' => .ok (.TestSticky p, toks')
    | "-n" :: s :: toks' => .ok (.TestNot (.TestEmpty_str s), toks')
    | "-p" :: p :: toks' => .ok (.TestFifo p, toks')
    | "-r" :: p :: toks' => .ok (.TestReadable p, toks')
    | "-S" :: p :: toks' => .ok (.TestSocket p, toks')
    | "-s" :: p :: toks' => .ok (.TestNonempty_file p, toks')
    | "-t" :: fd_s :: toks' =>
        match Num.readNat (toCharList fd_s) with
        | .error msg =>
            .error ("expected fd number after -t, found '" ++ fd_s ++ "' (" ++ msg ++ ")")
        | .ok d => .ok (.TestTerminalFD d, toks')
    | "-u" :: p :: toks' => .ok (.TestSetuid p, toks')
    | "-w" :: p :: toks' => .ok (.TestWriteable p, toks')
    | "-x" :: p :: toks' => .ok (.TestExecutable p, toks')
    | "-z" :: s :: toks' => .ok (.TestEmpty_str s, toks')
    | "(" :: toks' =>
        match parse_test_expr_disjunction toks' with
        | .error msg => .error msg
        | .ok (expr, ")" :: toks'') => .ok (expr, toks'')
        | .ok (expr, tok :: _) =>
            .error ("expected ')' after " ++ string_of_test_expr expr ++ ", found '" ++ tok ++ "'")
        | .ok (expr, []) =>
            .error ("expected ')' after " ++ string_of_test_expr expr ++ ", found end of input")
    -- plain strings are tested for non-nullness
    | s :: toks' => .ok (.TestNot (.TestEmpty_str s), toks')
    | [] => .error "expected unary operator, found end of input"
end

def parse_test_expr (toks : List String) : Except String test_expr :=
  let toksStr := String.intercalate " " toks
  match parse_test_expr_disjunction toks with
  | .error err => .error ("parse error in '" ++ toksStr ++ "': " ++ err)
  | .ok (expr, []) => .ok expr
  | .ok (expr, rest) =>
      .error
        ("unexpected input after " ++ string_of_test_expr expr ++ ": " ++ String.intercalate " " rest)

/-
Evaluation
-/

def eval_test_expr {a : Type u} [OS a] (s0 : os_state a) : test_expr → Bool
  | .TestBlock p         => decide (file_type_follow s0 p = some .FileBlock)
  | .TestCharacter p     => decide (file_type_follow s0 p = some .FileCharacter)
  | .TestDirectory p     => decide (file_type_follow s0 p = some .FileDirectory)
  | .TestExists p        => file_exists s0 p
  | .TestFile p          => decide (file_type_follow s0 p = some .FileRegular)
  | .TestSetgid p        =>
      match file_perms s0 p with
      | none => false
      | some perms => perms.setgid
  | .TestSymlink p       => decide (file_typeF s0 p = some .FileLink)
  | .TestSticky p        =>
      match file_perms s0 p with
      | none => false
      | some perms => perms.sticky
  | .TestFifo p          => decide (file_type_follow s0 p = some .FileFIFO)
  | .TestReadable p      => is_readable s0 p
  | .TestSocket p        => decide (file_type_follow s0 p = some .FileSocket)
  | .TestNonempty_file p =>
      match file_size s0 p with
      | none => false
      | some 0 => false
      | some _ => true
  | .TestTerminalFD d    => is_tty s0 d
  | .TestSetuid p        =>
      match file_perms s0 p with
      | none => false
      | some perms => perms.setuid
  | .TestWriteable p     => is_writeable s0 p
  | .TestExecutable p    => is_executable s0 p
  | .TestEmpty_str s     => decide (s = "")
  | .TestEq_str s1 s2    => decide (s1 = s2)
  | .TestGt_str s1 s2    => decide (s1 > s2)   -- TODO locale
  | .TestEq_num n1 n2    => decide (n1 = n2)
  | .TestGt_num n1 n2    => decide (n1 > n2)
  | .TestNewerFile f1 f2 =>
      match file_mtime s0 f1, file_mtime s0 f2 with
      | none, _ => false
      | some _, none => true
      | some t1, some t2 => decide (t1 > t2)
  | .TestOlderFile f1 f2 =>
      match file_mtime s0 f1, file_mtime s0 f2 with
      | none, none => false
      | none, some _ => true
      | some _, none => false
      | some t1, some t2 => decide (t1 < t2)
  | .TestSameFile f1 f2  =>
      match file_number s0 f1, file_number s0 f2 with
      | none, _ => false
      | _, none => false
      | some (dev1, ino1), some (dev2, ino2) =>
          decide (dev1 = dev2) && decide (ino1 = ino2)
  | .TestAnd e1 e2       => eval_test_expr s0 e1 && eval_test_expr s0 e2
  | .TestOr  e1 e2       => eval_test_expr s0 e1 || eval_test_expr s0 e2
  | .TestNot e           => not (eval_test_expr s0 e)

end Smoosh
