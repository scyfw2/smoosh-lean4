import Smoosh.Compat.PervasivesExtra
import Smoosh.BuildInfo
import Smoosh.Platform.SignalPlatform
import Smoosh.Num
import Smoosh.Prelude.Locales
import Smoosh.Prelude.Utility
import Smoosh.Set
universe u

namespace Smoosh

variable {α β : Type u}

open Smoosh

/-- Lem: type file_perm = Read | Write | Execute -/
inductive file_perm
  | Read | Write | Execute
deriving Repr, DecidableEq

/-- Lem: type perms = <| ... user: set file_perm; ... |> -/
structure perms where
  setuid : Bool
  setgid : Bool
  sticky : Bool
  user   : Set.Set file_perm
  group  : Set.Set file_perm
  other  : Set.Set file_perm
deriving Repr, DecidableEq

/-- Lem: perms_all_clear -/
def perms_all_clear : perms :=
  { setuid := false
    setgid := false
    sticky := false
    user   := Set.Set.empty
    group  := Set.Set.empty
    other  := Set.Set.empty }

/-- Lem: all_file_perms = Set.fromList [Read; Write; Execute] -/
def all_file_perms : Set.Set file_perm :=
  Set.Set.fromList [.Read, .Write, .Execute]

/-- Lem: default_umask -/
def default_umask : perms :=
  { setuid := false
    setgid := false
    sticky := false
    user   := Set.Set.empty
    group  := Set.Set.singleton .Write
    other  := Set.Set.singleton .Write }

/-- Lem: invert_file_perms fperms = Set.difference all_file_perms fperms -/
def invert_file_perms (fperms : Set.Set file_perm) : Set.Set file_perm :=
  Set.Set.difference all_file_perms fperms

/-- Lem: invert_perms -/
def invert_perms (p : perms) : perms :=
  { setuid := !p.setuid
    setgid := !p.setgid
    sticky := !p.sticky
    user   := invert_file_perms p.user
    group  := invert_file_perms p.group
    other  := invert_file_perms p.other }

/-
(**********************************************************************)
(* Symbolic file permissions a la chmod *******************************)
(**********************************************************************)
-/

/-
wholist          : who | wholist who
who              : 'u' | 'g' | 'o' | 'a'
-/

/-- Lem: type perms_who = WhoU | WhoG | WhoO -/
inductive perms_who
  | WhoU | WhoG | WhoO
deriving Repr, DecidableEq

/-- Lem: perms_wholist_all = Set.fromList [WhoU; WhoG; WhoO] -/
def perms_wholist_all : Set.Set perms_who :=
  Set.Set.fromList [.WhoU, .WhoG, .WhoO]

/-- Lem: perms_who : perms_who -> perms -> set file_perm -/
def perms_Who (who : perms_who) (p : perms) :Set.Set file_perm :=
  match who with
  | .WhoU => p.user
  | .WhoG => p.group
  | .WhoO => p.other

/-- Lem: perms_for : (set file_perm -> set file_perm) -> perms_who -> perms -> perms -/
def perms_for (f : Set.Set file_perm → Set.Set file_perm)
    (who : perms_who) (p : perms) : perms :=
  match who with
  | .WhoU => { p with user  := f p.user }
  | .WhoG => { p with group := f p.group }
  | .WhoO => { p with other := f p.other }

/-- Lem: perms_for_many ... = foldr (perms_for f) perms (Set.toList who) -/
def perms_for_many (f : Set.Set file_perm → Set.Set file_perm)
    (who : Set.Set perms_who) (p : perms) : perms :=
  List.foldr (perms_for f) p (Set.Set.toList who)

/-- Lem: perms_clear who perms = perms_for_many (fun _ -> Set.empty) who perms -/
def perms_clear (who : Set.Set perms_who) (p : perms) : perms :=
  perms_for_many (fun _ => Set.Set.empty) who p

/--
Lem:
val perms_wholist_of_cl
  : set perms_who -> list char -> either string (set perms_who * list char)
-/
def perms_wholist_of_cl
    (who : Set.Set perms_who) (cs : List Char)
    : Except String (Set.Set perms_who × List Char) :=
  match cs with
  | 'u' :: cs' => perms_wholist_of_cl (Set.Set.insert .WhoU who) cs'
  | 'g' :: cs' => perms_wholist_of_cl (Set.Set.insert .WhoG who) cs'
  | 'o' :: cs' => perms_wholist_of_cl (Set.Set.insert .WhoO who) cs'
  | 'a' :: cs' => perms_wholist_of_cl perms_wholist_all cs'
  | _ =>
      if Set.Set.null who then
        .error "empty wholist: need to specify one of ugoa"
      else
        .ok (who, cs)

/-
permlist         : perm | perm permlist
perm             : 'r' | 'w' | 'x' | 'X' | 's' | 't'
-/

/-- Lem: type perms_flag = PermR | PermW | PermX | PermBigX | PermS | PermT -/
inductive perms_flag
  | PermR | PermW | PermX | PermBigX | PermS | PermT
deriving Repr, DecidableEq

/-- Lem: flag_of_file_perm : file_perm -> perms_flag -/
def flag_of_file_perm : file_perm → perms_flag
  | .Read    => .PermR
  | .Write   => .PermW
  | .Execute => .PermX

/--
Lem:
val perms_flaglist_of_cl
  : set perms_flag -> list char -> either string (set perms_flag * list char)
-/
def perms_flaglist_of_cl
    (perms : Set.Set perms_flag) (cs : List Char)
    : Except String (Set.Set perms_flag × List Char) :=
  match cs with
  | 'r' :: cs' => perms_flaglist_of_cl (Set.Set.insert .PermR perms) cs'
  | 'w' :: cs' => perms_flaglist_of_cl (Set.Set.insert .PermW perms) cs'
  | 'x' :: cs' => perms_flaglist_of_cl (Set.Set.insert .PermX perms) cs'
  | 'X' :: cs' => perms_flaglist_of_cl (Set.Set.insert .PermBigX perms) cs'
  | 's' :: cs' => perms_flaglist_of_cl (Set.Set.insert .PermS perms) cs'
  | 't' :: cs' => perms_flaglist_of_cl (Set.Set.insert .PermT perms) cs'
  | _ =>
      if Set.Set.null perms then
        .error "empty permlist: need to specify one of rwxXst"
      else
        .ok (perms, cs)

/-
actionlist       : action | actionlist action
action           : op | op permlist | op permcopy
permcopy         : 'u' | 'g' | 'o'
op               : '+' | '-' | '='
-/

/-- Lem: type perms_op = OpPlus | OpMinus | OpEqual -/
inductive perms_op
  | OpPlus | OpMinus | OpEqual
deriving Repr, DecidableEq

/-- Lem: type perms_action = ActOp | ActPerms | ActCopy -/
inductive perms_action where
  | ActOp    : perms_op → perms_action
  | ActPerms : perms_op → Set.Set perms_flag → perms_action
  | ActCopy  : perms_op → perms_who → perms_action
deriving Repr, DecidableEq

/-- Lem: perms_op_of_cl : list char -> either string (perms_op * list char) -/
@[simp] def perms_op_of_cl : List Char → Except String (perms_op × List Char)
  | '+' :: cs' => .ok (.OpPlus, cs')
  | '-' :: cs' => .ok (.OpMinus, cs')
  | '=' :: cs' => .ok (.OpEqual, cs')
  | c :: _     => .error s!"expected op (one of +-=), got '{String.ofList [c]}'"
  | []         => .error "expected op (one of +-=, got empty string"

theorem perms_op_of_cl_len_lt
    {cs cs' : List Char} {op : perms_op} :
    perms_op_of_cl cs = .ok (op, cs') → cs'.length < cs.length := by
  intro hOk
  cases cs with
  | nil => simp [perms_op_of_cl] at hOk
  | cons c rest =>
    by_cases hp : c = '+'
    . subst hp
      have hOk' := hOk
      simp [perms_op_of_cl] at hOk'
      cases hOk'
      simp; subst rest; omega
    . by_cases hm : c = '-'
      . subst hm
        have hOk' := hOk
        simp [perms_op_of_cl] at hOk'
        cases hOk'
        simp; subst rest; omega
      . by_cases he : c = '='
        . subst he
          have hOk' := hOk
          simp [perms_op_of_cl] at hOk'
          cases hOk'
          simp; subst rest; omega
        . have hOk' := hOk
          simp [perms_op_of_cl] at hOk'

theorem perms_flaglist_of_cl_len_le
    (perms : Set.Set perms_flag)
    {cs cs'' : List Char} {permlist : Set.Set perms_flag} :
    perms_flaglist_of_cl (perms := perms) cs = .ok (permlist, cs'') →
      cs''.length ≤ cs.length := by
  intro hOk
  induction cs generalizing perms permlist cs'' with
  | nil =>
      by_cases hn : Set.Set.null perms
      . simp [perms_flaglist_of_cl, hn] at hOk
      . simp [perms_flaglist_of_cl, hn] at hOk
        cases hOk
        simp; assumption
  | cons c rest ih =>
      by_cases hr : c = 'r'
      . subst hr
        have hRec :
            perms_flaglist_of_cl (perms := Set.Set.insert .PermR perms) rest
              = .ok (permlist, cs'') := by
          simpa [perms_flaglist_of_cl] using hOk
        have leRest : cs''.length ≤ rest.length :=
          ih (perms := Set.Set.insert .PermR perms) hRec
        exact Nat.le_trans leRest (by simp)
      . by_cases hw : c = 'w'
        . subst hw
          have hRec :
              perms_flaglist_of_cl (perms := Set.Set.insert .PermW perms) rest
                = .ok (permlist, cs'') := by
            simpa [perms_flaglist_of_cl] using hOk
          have leRest : cs''.length ≤ rest.length :=
            ih (perms := Set.Set.insert .PermW perms) hRec
          exact Nat.le_trans leRest (by simp)
        . by_cases hx : c = 'x'
          . subst hx
            have hRec :
                perms_flaglist_of_cl (perms := Set.Set.insert .PermX perms) rest
                  = .ok (permlist, cs'') := by
              simpa [perms_flaglist_of_cl] using hOk
            have leRest : cs''.length ≤ rest.length :=
              ih (perms := Set.Set.insert .PermX perms) hRec
            exact Nat.le_trans leRest (by simp)
          . by_cases hX : c = 'X'
            . subst hX
              have hRec :
                  perms_flaglist_of_cl (perms := Set.Set.insert .PermBigX perms) rest
                    = .ok (permlist, cs'') := by
                simpa [perms_flaglist_of_cl] using hOk
              have leRest : cs''.length ≤ rest.length :=
                ih (perms := Set.Set.insert .PermBigX perms) hRec
              exact Nat.le_trans leRest (by simp)
            . by_cases hs : c = 's'
              . subst hs
                have hRec :
                    perms_flaglist_of_cl (perms := Set.Set.insert .PermS perms) rest
                      = .ok (permlist, cs'') := by
                  simp [perms_flaglist_of_cl] at hOk
                  assumption
                have leRest : cs''.length ≤ rest.length :=
                  ih (perms := Set.Set.insert .PermS perms) hRec
                exact Nat.le_trans leRest (by simp)
              . by_cases ht : c = 't'
                . subst ht
                  have hRec :
                      perms_flaglist_of_cl (perms := Set.Set.insert .PermT perms) rest
                        = .ok (permlist, cs'') := by
                    simpa [perms_flaglist_of_cl] using hOk
                  have leRest : cs''.length ≤ rest.length :=
                    ih (perms := Set.Set.insert .PermT perms) hRec
                  exact Nat.le_trans leRest (by simp)
                . by_cases hn : Set.Set.null perms
                  . simp [perms_flaglist_of_cl, hr, hw, hx, hX, hs, ht, hn] at hOk
                  . simp [perms_flaglist_of_cl, hr, hw, hx, hX, hs, ht, hn] at hOk
                    cases hOk
                    simp; subst cs''; simp

theorem perms_flaglist_of_cl_len_lt
    {cs' cs'' : List Char} {permlist : Set.Set perms_flag} :
    perms_flaglist_of_cl (perms := Set.Set.empty) cs' = .ok (permlist, cs'') →
      cs''.length < cs'.length := by
  intro hOk
  cases cs' with
  | nil => cases hOk
  | cons c rest =>
      by_cases hr : c = 'r'
      . subst hr
        have hRec :
            perms_flaglist_of_cl (perms := Set.Set.insert .PermR Set.Set.empty) rest
              = .ok (permlist, cs'') := by
          simpa [perms_flaglist_of_cl] using hOk
        have leRest : cs''.length ≤ rest.length :=
          perms_flaglist_of_cl_len_le (perms := Set.Set.insert .PermR Set.Set.empty) hRec
        exact Nat.lt_of_le_of_lt leRest (by simp)
      . by_cases hw : c = 'w'
        . subst hw
          have hRec :
              perms_flaglist_of_cl (perms := Set.Set.insert .PermW Set.Set.empty) rest
                = .ok (permlist, cs'') := by
            simpa [perms_flaglist_of_cl] using hOk
          have leRest : cs''.length ≤ rest.length :=
            perms_flaglist_of_cl_len_le (perms := Set.Set.insert .PermW Set.Set.empty) hRec
          exact Nat.lt_of_le_of_lt leRest (by simp)
        . by_cases hx : c = 'x'
          . subst hx
            have hRec :
                perms_flaglist_of_cl (perms := Set.Set.insert .PermX Set.Set.empty) rest
                  = .ok (permlist, cs'') := by
              simpa [perms_flaglist_of_cl] using hOk
            have leRest : cs''.length ≤ rest.length :=
              perms_flaglist_of_cl_len_le (perms := Set.Set.insert .PermX Set.Set.empty) hRec
            exact Nat.lt_of_le_of_lt leRest (by simp)
          . by_cases hX : c = 'X'
            . subst hX
              have hRec :
                  perms_flaglist_of_cl (perms := Set.Set.insert .PermBigX Set.Set.empty) rest
                    = .ok (permlist, cs'') := by
                simpa [perms_flaglist_of_cl] using hOk
              have leRest : cs''.length ≤ rest.length :=
                perms_flaglist_of_cl_len_le (perms := Set.Set.insert .PermBigX Set.Set.empty) hRec
              exact Nat.lt_of_le_of_lt leRest (by simp)
            . by_cases hs : c = 's'
              . subst hs
                have hRec :
                    perms_flaglist_of_cl (perms := Set.Set.insert .PermS Set.Set.empty) rest
                      = .ok (permlist, cs'') := by
                  simpa [perms_flaglist_of_cl] using hOk
                have leRest : cs''.length ≤ rest.length :=
                  perms_flaglist_of_cl_len_le (perms := Set.Set.insert .PermS Set.Set.empty) hRec
                exact Nat.lt_of_le_of_lt leRest (by simp)
              . by_cases ht : c = 't'
                . subst ht
                  have hRec :
                      perms_flaglist_of_cl (perms := Set.Set.insert .PermT Set.Set.empty) rest
                        = .ok (permlist, cs'') := by
                    simpa [perms_flaglist_of_cl] using hOk
                  have leRest : cs''.length ≤ rest.length :=
                    perms_flaglist_of_cl_len_le (perms := Set.Set.insert .PermT Set.Set.empty) hRec
                  exact Nat.lt_of_le_of_lt leRest (by simp)
                . cases hnull : Set.Set.null (Set.Set.empty : Set.Set perms_flag) with
                  | true =>
                      have : Except.error "empty permlist: need to specify one of rwxXst"
                            = Except.ok (permlist, cs'') := by
                        simp [perms_flaglist_of_cl, hr, hw, hx, hX, hs, ht] at hOk
                        cases hOk
                      cases this
                  | false => cases hnull

/--
Lem:
val perms_actionlist_of_cl
  : list perms_action -> list char -> either string (list perms_action * list char)
-/
def perms_actionlist_of_cl
    (actions : List perms_action) (cs : List Char)
    : Except String (List perms_action × List Char) :=
  match _h : perms_op_of_cl cs with
  | .ok (op, cs') =>
      match cs' with
      | 'u' :: cs'' =>
          perms_actionlist_of_cl (.ActCopy op .WhoU :: actions) cs''
      | 'g' :: cs'' =>
          perms_actionlist_of_cl (.ActCopy op .WhoG :: actions) cs''
      | 'o' :: cs'' =>
          perms_actionlist_of_cl (.ActCopy op .WhoO :: actions) cs''
      | _ =>
          match _h2 : perms_flaglist_of_cl (perms := Set.Set.empty) cs' with
          | .ok (permlist, cs'') =>
              perms_actionlist_of_cl (.ActPerms op permlist :: actions) cs''
          | .error _ =>
              perms_actionlist_of_cl (.ActOp op :: actions) cs'
  | .error msg =>
      if actions.isEmpty then
        .error ("empty actionlist: " ++ msg)
      else
        .ok (actions.reverse, cs)
termination_by
  cs.length
decreasing_by
  . have hlt' : ('u' :: cs'').length < cs.length :=
      perms_op_of_cl_len_lt (cs := cs) (op := op) (cs' := ('u' :: cs'')) (by exact _h)
    have : cs''.length < ('u' :: cs'').length := by simp
    exact Nat.lt_trans this hlt'
  . have hlt' : ('g' :: cs'').length < cs.length :=
        perms_op_of_cl_len_lt (cs := cs) (op := op) (cs' := ('g' :: cs'')) (by exact _h)
    have : cs''.length < ('g' :: cs'').length := by simp
    exact Nat.lt_trans this hlt'
  . have hlt' : ('o' :: cs'').length < cs.length :=
      perms_op_of_cl_len_lt (cs := cs) (op := op) (cs' := ('o' :: cs'')) (by exact _h)
    have : cs''.length < ('o' :: cs'').length := by simp
    exact Nat.lt_trans this hlt'
  . have hlt1 : cs''.length < cs'.length :=
      perms_flaglist_of_cl_len_lt
        (cs' := cs') (cs'' := cs'') (permlist := permlist) (by simpa [_h2])
    have hlt2 : cs'.length < cs.length :=
      perms_op_of_cl_len_lt (cs := cs) (op := op) (cs' := cs') (by (expose_names; exact _h_1))
    exact Nat.lt_trans hlt1 hlt2
  . exact perms_op_of_cl_len_lt (cs := cs) (op := op) (cs' := cs') (by (expose_names; exact _h_1))

/-
clause : actionlist | wholist actionlist
-/

/-- Lem: type perms_clause = (set perms_who) * list perms_action -/
abbrev perms_clause : Type :=
  (Set.Set perms_who) × List perms_action

/--
Lem:
val perms_clause_of_cl : list char -> either string (perms_clause * list char)
-/
def perms_clause_of_cl (cs : List Char) :
    Except String (perms_clause × List Char) :=
  let (who, cs') :=
    match perms_wholist_of_cl (who := Set.Set.empty) cs with
    | .ok (who, cs') => (who, cs')
    | .error _ =>
        -- when unspecified, perms mean ALL
        (perms_wholist_all, cs)
  match perms_actionlist_of_cl (actions := []) cs' with
  | .ok (actions, cs'') =>
      .ok (((who, actions), cs''))
  | .error msg =>
      .error ("bad clause: " ++ msg)

/-
symbolic_mode : clause | symbolic_mode ',' clause
-/

/-- Lem: perms_symbolic = list perms_clause -/
abbrev perms_symbolic : Type :=
  List perms_clause

theorem perms_wholist_of_cl_len_le
    (who0 : Set.Set perms_who)
    {cs cs' : List Char} {who : Set.Set perms_who} :
    perms_wholist_of_cl (who := who0) cs = .ok (who, cs') →
      cs'.length ≤ cs.length := by
  intro hOk
  induction cs generalizing who0 who cs' with
  | nil =>
      by_cases hnull : Set.Set.null who0
      . simp [perms_wholist_of_cl, hnull] at hOk
      . simp [perms_wholist_of_cl, hnull] at hOk
        cases hOk
        simp; assumption
  | cons c rest ih =>
      by_cases hu : c = 'u'
      . subst hu
        have hRec :
            perms_wholist_of_cl (who := Set.Set.insert .WhoU who0) rest
              = .ok (who, cs') := by
          simpa [perms_wholist_of_cl] using hOk
        have leRest : cs'.length ≤ rest.length :=
          ih (who0 := Set.Set.insert .WhoU who0) hRec
        exact Nat.le_trans leRest (by simp)
      . by_cases hg : c = 'g'
        . subst hg
          have hRec :
              perms_wholist_of_cl (who := Set.Set.insert .WhoG who0) rest
                = .ok (who, cs') := by
            simpa [perms_wholist_of_cl] using hOk
          have leRest : cs'.length ≤ rest.length :=
            ih (who0 := Set.Set.insert .WhoG who0) hRec
          exact Nat.le_trans leRest (by simp)
        . by_cases ho : c = 'o'
          . subst ho
            have hRec :
                perms_wholist_of_cl (who := Set.Set.insert .WhoO who0) rest
                  = .ok (who, cs') := by
              simpa [perms_wholist_of_cl] using hOk
            have leRest : cs'.length ≤ rest.length :=
              ih (who0 := Set.Set.insert .WhoO who0) hRec
            exact Nat.le_trans leRest (by simp)
          . by_cases ha : c = 'a'
            . subst ha
              have hRec :
                  perms_wholist_of_cl (who := perms_wholist_all) rest
                    = .ok (who, cs') := by
                simpa [perms_wholist_of_cl] using hOk
              have leRest : cs'.length ≤ rest.length :=
                ih (who0 := perms_wholist_all) hRec
              exact Nat.le_trans leRest (by simp)
            . by_cases hnull : Set.Set.null who0
              . simp [perms_wholist_of_cl, hu, hg, ho, ha, hnull] at hOk
              . simp [perms_wholist_of_cl, hu, hg, ho, ha, hnull] at hOk
                cases hOk
                simp; subst cs'; exact Nat.le_refl (c :: rest).length

-- theorem perms_actionlist_of_cl_comma_len_lt
--     {cs cs' : List Char} {actions : List perms_action} :
--     perms_actionlist_of_cl (actions := []) cs = .ok (actions, ',' :: cs') →
--       cs'.length < cs.length := by
--   intro hOk
--   exact perms_actionlist_of_cl_comma_len_lt_gen_core [] cs cs' actions hOk

-- #check perms_actionlist_of_cl.eq_def

-- theorem perms_actionlist_of_cl_comma_len_lt_gen
--     (actions0 : List perms_action)
--     {cs cs' : List Char} {actions : List perms_action} :
--     perms_actionlist_of_cl (actions := actions0) cs = .ok (actions, ',' :: cs') →
--       cs'.length < cs.length := by sorry

-- theorem perms_actionlist_of_cl_comma_len_lt
--     {cs cs' : List Char} {actions : List perms_action} :
--     perms_actionlist_of_cl (actions := []) cs = .ok (actions, ',' :: cs') →
--       cs'.length < cs.length := by
--   intro hOk
--   exact perms_actionlist_of_cl_comma_len_lt_gen [] (cs := cs) (cs' := cs') (actions := actions) hOk

-- theorem perms_clause_of_cl_comma_len_lt
--     {cs cs' : List Char} {clause : perms_clause} :
--     perms_clause_of_cl cs = .ok (clause, ',' :: cs') →
--       cs'.length < cs.length := by
--   intro hOk
--   simp [perms_clause_of_cl] at hOk
--   cases hw : perms_wholist_of_cl { elems := [] } cs with
--   | error _ =>
--     cases ha : perms_actionlist_of_cl (actions := []) cs with
--     | error msg =>
--       simp [hw, ha] at hOk
--     | ok actions_cs2 =>
--       rcases actions_cs2 with ⟨actions, cs2⟩
--       have hcs2 : cs2 = ',' :: cs' := by
--         simp [hw, ha] at hOk
--         cases hOk; assumption
--       have : cs'.length < cs.length :=
--         perms_actionlist_of_cl_comma_len_lt (cs := cs) (cs' := cs') (actions := actions) (by simpa [hcs2] using ha)
--       exact this
--   | ok who_cs1 =>
--     rcases who_cs1 with ⟨who, cs1⟩
--     cases ha : perms_actionlist_of_cl (actions := []) cs1 with
--     | error msg =>
--       simp [hw, ha] at hOk
--     | ok actions_cs2 =>
--       rcases actions_cs2 with ⟨actions, cs2⟩
--       simp [hw, ha] at hOk
--       cases hOk
--       have hAct : cs'.length < cs1.length :=
--         perms_actionlist_of_cl_comma_len_lt (cs := cs1) (cs' := cs') (actions := actions) (by expose_names; subst right; assumption)
--       have hWho : cs1.length ≤ cs.length :=
--         perms_wholist_of_cl_len_le (who0 := Set.Set.empty) (cs := cs) (cs' := cs1) (who := who) (by simpa using hw)
--       exact Nat.lt_of_lt_of_le hAct hWho

/-- Lem: perms_symbolic_of_cl : perms_symbolic -> list char -> either string (perms_symbolic * list char) -/

/-
def perms_symbolic_of_cl (perms : perms_symbolic) (cs : List Char)
    : Except String (perms_symbolic × List Char) :=
  match _h : perms_clause_of_cl cs with
  | .error msg => .error ("no clauses found: " ++ msg)
  | .ok (clause, []) => .ok (clause :: perms, [])
  | .ok (clause, ',' :: cs') =>
      perms_symbolic_of_cl (clause :: perms) cs'
  | .ok (_, c :: _) =>
      .error ("expected comma between clauses, found '" ++ charsToString [c] ++ "'")
termination_by
  cs.length
decreasing_by
  simpa using perms_clause_of_cl_comma_len_lt (cs := cs) (clause := clause) (cs' := cs') (by exact _h)
-/

abbrev Fuel := Nat

def perms_symbolic_of_cl (fuel : Fuel) (perms : perms_symbolic) (cs : List Char)
    : Except String (perms_symbolic × List Char) :=
  match fuel with
  | 0 =>
      .error "perms_symbolic_of_cl: out of fuel"
  | .succ fuel =>
      match perms_clause_of_cl cs with
      | .error msg =>
          .error ("no clauses found: " ++ msg)
      | .ok (clause, []) =>
          .ok (clause :: perms, [])
      | .ok (clause, ',' :: cs') =>
          perms_symbolic_of_cl fuel (clause :: perms) cs'
      | .ok (_, c :: _) =>
          .error ("expected comma between clauses, found '" ++ charsToString [c] ++ "'")

-- def perms_symbolic_of_cl_default (perms : perms_symbolic) (cs : List Char)
--     : Except String (perms_symbolic × List Char) :=
--   perms_symbolic_of_cl (cs.length + 1) perms cs

/-- Lem: perms_symbolic_of_string : string -> either string perms_symbolic -/
def perms_symbolic_of_string (fuel : Fuel) (s : String) : Except String perms_symbolic :=
  match perms_symbolic_of_cl fuel [] (toCharList s) with
  | .error msg => .error msg
  | .ok (perms, []) => .ok perms
  | .ok (_, cs') => .error ("invalid symbolic permissions: " ++ charsToString cs')


end Smoosh
