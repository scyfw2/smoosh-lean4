import Smoosh.Prelude.All
import Smoosh.Map
import Smoosh.Set
import Smoosh.os.OsState
import Smoosh.Num

universe u

/-- Lem: val default_block : nat -/
def default_block : Nat := 10

/-- Lem: read_eof type -/
inductive read_eof where
  | ReadEOF
  | ReadContinue
deriving DecidableEq, Repr

/-- Lem: val read_eof : read_eof -> bool -/
def read_eof_toBool : read_eof → Bool
  | .ReadEOF      => true
  | .ReadContinue => false

/-- Lem: read_result 'a type -/
inductive read_result (α : Type u) where
  | ReadError   (msg : String)
  | ReadBlocked (pid : Nat)
  | ReadSuccess (val : α) (eof : read_eof)
deriving DecidableEq, Repr

/-- Lem: file type -/
inductive file (α : Type u) where
  | File
  | Dir (info : α)
deriving DecidableEq, Repr

/-- Lem: file_type type -/
inductive file_type where
  | FileRegular
  | FileDirectory
  | FileCharacter
  | FileBlock
  | FileLink
  | FileFIFO
  | FileSocket
deriving DecidableEq, Repr

-- declare ocaml target_rep type file_type = `Unix.file_kind`
-- declare ocaml target_rep function FileRegular   = `Unix.S_REG`
-- declare ocaml target_rep function FileDirectory = `Unix.S_DIR`
-- declare ocaml target_rep function FileCharacter = `Unix.S_CHR`
-- declare ocaml target_rep function FileBlock     = `Unix.S_BLK`
-- declare ocaml target_rep function FileLink      = `Unix.S_LNK`
-- declare ocaml target_rep function FileFIFO      = `Unix.S_FIFO`
-- declare ocaml target_rep function FileSocket    = `Unix.S_SOCK`
