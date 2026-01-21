import Smoosh.Compat.PervasivesExtra
import Smoosh.BuildInfo
import Smoosh.Platform.SignalPlatform
import Smoosh.Signal
import Smoosh.Prelude.FilePerm
import Smoosh.Map
import Smoosh.Prelude.Pattern
import Smoosh.Prelude.Redirect
import Smoosh.Prelude.ShellOptions
import Smoosh.Prelude.Locales
import Smoosh.Prelude.AST

open Smoosh

mutual
  -- option
  private def decEqOptionExpandingRedir :
      (a b : Option expanding_redir) → Decidable (a = b)
  | none, none => isTrue rfl
  | some x, some y =>
      match decEqExpandingRedir x y with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro hxy; cases hxy; exact h rfl)
  | none, some _ => isFalse (by intro h; cases h)
  | some _, none => isFalse (by intro h; cases h)
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by repeat' (simp_wf; omega)

  private def decEqOptionNat :
      (a b : Option Nat) → Decidable (a = b)
  | none, none => isTrue rfl
  | some x, some y =>
      match (inferInstance : Decidable (x = y)) with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro hxy; cases hxy; exact h rfl)
  | none, some _ => isFalse (by intro h; cases h)
  | some _, none => isFalse (by intro h; cases h)
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by repeat' (simp_wf; omega)
  -- list
  private def decEqListSymbolicChar :
      (xs ys : List symbolic_char) → Decidable (xs = ys)
  | [], [] => isTrue rfl
  | x::xs, y::ys =>
      match decEqSymbolicChar x y, decEqListSymbolicChar xs ys with
      | isTrue hx, isTrue hxs => isTrue (by cases hx; cases hxs; rfl)
      | isFalse hx, _         => isFalse (by intro h; cases h; exact hx rfl)
      | _, isFalse hxs        => isFalse (by intro h; cases h; exact hxs rfl)
  | [], _::_ => isFalse (by intro h; cases h)
  | _::_, [] => isFalse (by intro h; cases h)
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by repeat' (simp_wf; omega)

  private def decEqListListSymbolicChar :
      (xs ys : List (List symbolic_char)) → Decidable (xs = ys)
  | [], [] => isTrue rfl
  | x::xs, y::ys =>
      match decEqListSymbolicChar x y, decEqListListSymbolicChar xs ys with
      | isTrue hx, isTrue hxs => isTrue (by cases hx; cases hxs; rfl)
      | isFalse hx, _         => isFalse (by intro h; cases h; exact hx rfl)
      | _, isFalse hxs        => isFalse (by intro h; cases h; exact hxs rfl)
  | [], _::_ => isFalse (by intro h; cases h)
  | _::_, [] => isFalse (by intro h; cases h)
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by repeat' (simp_wf; omega)

  private def decEqListEntry : (xs ys : List entry) → Decidable (xs = ys)
  | [], [] => isTrue rfl
  | x::xs, y::ys =>
      match decEqEntry x y, decEqListEntry xs ys with
      | isTrue hx, isTrue hxs => isTrue (by cases hx; cases hxs; rfl)
      | isFalse hx, _         => isFalse (by intro h; cases h; exact hx rfl)
      | _, isFalse hxs        => isFalse (by intro h; cases h; exact hxs rfl)
  | [], _::_ => isFalse (by intro h; cases h)
  | _::_, [] => isFalse (by intro h; cases h)
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by repeat' (simp_wf; omega)

  private def decEqListListEntry : (xs ys : List (List entry)) → Decidable (xs = ys)
  | [], [] => isTrue rfl
  | x::xs, y::ys =>
      match decEqListEntry x y, decEqListListEntry xs ys with
      | isTrue hx, isTrue hxs => isTrue (by cases hx; cases hxs; rfl)
      | isFalse hx, _         => isFalse (by intro h; cases h; exact hx rfl)
      | _, isFalse hxs        => isFalse (by intro h; cases h; exact hxs rfl)
  | [], _::_ => isFalse (by intro h; cases h)
  | _::_, [] => isFalse (by intro h; cases h)
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by repeat' (simp_wf; omega)

  private def decEqListExpandedWord :
      (xs ys : List expanded_word) → Decidable (xs = ys)
  | [], [] => isTrue rfl
  | x::xs, y::ys =>
      match decEqExpandedWord x y, decEqListExpandedWord xs ys with
      | isTrue hx, isTrue hxs => isTrue (by cases hx; cases hxs; rfl)
      | isFalse hx, _         => isFalse (by intro h; cases h; exact hx rfl)
      | _, isFalse hxs        => isFalse (by intro h; cases h; exact hxs rfl)
  | [], _::_ => isFalse (by intro h; cases h)
  | _::_, [] => isFalse (by intro h; cases h)
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by repeat' (simp_wf; omega)

  private def decEqListTmpField :
      (xs ys : List tmp_field) → Decidable (xs = ys)
  | [], [] => isTrue rfl
  | x::xs, y::ys =>
      match decEqTmpField x y, decEqListTmpField xs ys with
      | isTrue hx, isTrue hxs => isTrue (by cases hx; cases hxs; rfl)
      | isFalse hx, _         => isFalse (by intro h; cases h; exact hx rfl)
      | _, isFalse hxs        => isFalse (by intro h; cases h; exact hxs rfl)
  | [], _::_ => isFalse (by intro h; cases h)
  | _::_, [] => isFalse (by intro h; cases h)
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by repeat' (simp_wf; omega)

  private def decEqListRedir :
      (xs ys : List redir) → Decidable (xs = ys)
  | [], [] => isTrue rfl
  | x::xs, y::ys =>
      match decEqRedir x y, decEqListRedir xs ys with
      | isTrue hx, isTrue hxs => isTrue (by cases hx; cases hxs; rfl)
      | isFalse hx, _         => isFalse (by intro h; cases h; exact hx rfl)
      | _, isFalse hxs        => isFalse (by intro h; cases h; exact hxs rfl)
  | [], _::_ => isFalse (by intro h; cases h)
  | _::_, [] => isFalse (by intro h; cases h)
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by repeat' (simp_wf; omega)

  private def decEqListExpandedRedir :
      (xs ys : List expanded_redir) → Decidable (xs = ys)
  | [], [] => isTrue rfl
  | x::xs, y::ys =>
      match decEqExpandedRedir x y, decEqListExpandedRedir xs ys with
      | isTrue hx, isTrue hxs => isTrue (by cases hx; cases hxs; rfl)
      | isFalse hx, _         => isFalse (by intro h; cases h; exact hx rfl)
      | _, isFalse hxs        => isFalse (by intro h; cases h; exact hxs rfl)
  | [], _::_ => isFalse (by intro h; cases h)
  | _::_, [] => isFalse (by intro h; cases h)
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by repeat' (simp_wf; omega)

  private def decEqListStmt : (xs ys : List stmt) → Decidable (xs = ys)
  | [], [] => isTrue rfl
  | x::xs, y::ys =>
      match decEqStmt x y, decEqListStmt xs ys with
      | isTrue hx, isTrue hxs => isTrue (by cases hx; cases hxs; rfl)
      | isFalse hx, _         => isFalse (by intro h; cases h; exact hx rfl)
      | _, isFalse hxs        => isFalse (by intro h; cases h; exact hxs rfl)
  | [], _::_ => isFalse (by intro h; cases h)
  | _::_, [] => isFalse (by intro h; cases h)
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by repeat' (simp_wf; omega)
  -- prod
  -- (String × List entry)
  private def decEqProdStringListEntry :
      (a b : String × List entry) → Decidable (a = b)
  | (s1, ws1), (s2, ws2) =>
      match (inferInstance : Decidable (s1 = s2)),
            decEqListEntry ws1 ws2 with
      | isTrue h1, isTrue h2 => isTrue (by cases h1; cases h2; rfl)
      | isFalse h, _ => isFalse (by intro h'; cases h'; exact h rfl)
      | _, isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by repeat' (simp_wf; omega)

  private def decEqListProdStringListEntry :
      (xs ys : List (String × List entry)) → Decidable (xs = ys)
  | [], [] => isTrue rfl
  | x::xs, y::ys =>
      match decEqProdStringListEntry x y, decEqListProdStringListEntry xs ys with
      | isTrue hx, isTrue hxs => isTrue (by cases hx; cases hxs; rfl)
      | isFalse hx, _         => isFalse (by intro h; cases h; exact hx rfl)
      | _, isFalse hxs        => isFalse (by intro h; cases h; exact hxs rfl)
  | [], _::_ => isFalse (by intro h; cases h)
  | _::_, [] => isFalse (by intro h; cases h)
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by repeat' (simp_wf; omega)
  -- (String × expansion_state)
  private def decEqProdStringExpansionState :
      (a b : String × expansion_state) → Decidable (a = b)
  | (s1, st1), (s2, st2) =>
      match (inferInstance : Decidable (s1 = s2)),
            decEqExpansionState st1 st2 with
      | isTrue h1, isTrue h2 => isTrue (by cases h1; cases h2; rfl)
      | isFalse h, _ => isFalse (by intro h'; cases h'; exact h rfl)
      | _, isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by repeat' (simp_wf; omega)

  private def decEqListProdStringExpansionState :
      (xs ys : List (String × expansion_state)) → Decidable (xs = ys)
  | [], [] => isTrue rfl
  | x::xs, y::ys =>
      match decEqProdStringExpansionState x y,
            decEqListProdStringExpansionState xs ys with
      | isTrue hx, isTrue hxs => isTrue (by cases hx; cases hxs; rfl)
      | isFalse hx, _         => isFalse (by intro h; cases h; exact hx rfl)
      | _, isFalse hxs        => isFalse (by intro h; cases h; exact hxs rfl)
  | [], _::_ => isFalse (by intro h; cases h)
  | _::_, [] => isFalse (by intro h; cases h)
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by repeat' (simp_wf; omega)
  -- (String × List symbolic_char)
  private def decEqProdStringListSymbolicChar :
      (a b : String × List symbolic_char) → Decidable (a = b)
  | (s1, xs1), (s2, xs2) =>
      match (inferInstance : Decidable (s1 = s2)),
            decEqListSymbolicChar xs1 xs2 with
      | isTrue h1, isTrue h2 => isTrue (by cases h1; cases h2; rfl)
      | isFalse h, _ => isFalse (by intro h'; cases h'; exact h rfl)
      | _, isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by repeat' (simp_wf; omega)

  private def decEqListProdStringListSymbolicChar :
      (xs ys : List (String × List symbolic_char)) → Decidable (xs = ys)
  | [], [] => isTrue rfl
  | x::xs, y::ys =>
      match decEqProdStringListSymbolicChar x y,
            decEqListProdStringListSymbolicChar xs ys with
      | isTrue hx, isTrue hxs => isTrue (by cases hx; cases hxs; rfl)
      | isFalse hx, _         => isFalse (by intro h; cases h; exact hx rfl)
      | _, isFalse hxs        => isFalse (by intro h; cases h; exact hxs rfl)
  | [], _::_ => isFalse (by intro h; cases h)
  | _::_, [] => isFalse (by intro h; cases h)
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by repeat' (simp_wf; omega)
  -- (List (List entry) × stmt)  —— for Case branches
  private def decEqProdListListEntryStmt :
      (a b : List (List entry) × stmt) → Decidable (a = b)
  | (ps1, st1), (ps2, st2) =>
      match decEqListListEntry ps1 ps2,
            decEqStmt st1 st2 with
      | isTrue h1, isTrue h2 => isTrue (by cases h1; cases h2; rfl)
      | isFalse h, _ => isFalse (by intro h'; cases h'; exact h rfl)
      | _, isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by repeat' (simp_wf; omega)

  private def decEqListProdListListEntryStmt :
      (xs ys : List (List (List entry) × stmt)) → Decidable (xs = ys)
  | [], [] => isTrue rfl
  | x::xs, y::ys =>
      match decEqProdListListEntryStmt x y,
            decEqListProdListListEntryStmt xs ys with
      | isTrue hx, isTrue hxs => isTrue (by cases hx; cases hxs; rfl)
      | isFalse hx, _         => isFalse (by intro h; cases h; exact hx rfl)
      | _, isFalse hxs        => isFalse (by intro h; cases h; exact hxs rfl)
  | [], _::_ => isFalse (by intro h; cases h)
  | _::_, [] => isFalse (by intro h; cases h)
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by repeat' (simp_wf; omega)
  -- (List expanded_redir × Option expanding_redir × List redir)
  private def decEqRsTriple :
      (a b : (List expanded_redir) × Option expanding_redir × List redir) →
      Decidable (a = b)
  | (l1, o1, r1), (l2, o2, r2) =>
      match decEqListExpandedRedir l1 l2,
            decEqOptionExpandingRedir o1 o2,
            decEqListRedir r1 r2 with
      | isTrue h1, isTrue h2, isTrue h3 =>
          isTrue (by cases h1; cases h2; cases h3; rfl)
      | isFalse h, _, _ =>
          isFalse (by intro h'; cases h'; exact h rfl)
      | _, isFalse h, _ =>
          isFalse (by intro h'; cases h'; exact h rfl)
      | _, _, isFalse h =>
          isFalse (by intro h'; cases h'; exact h rfl)
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by repeat' (simp_wf; omega)

  private def decEqFormat : (a b : format) → Decidable (a = b)
  | .Normal, .Normal => isTrue rfl
  | .Default ws1, .Default ws2 =>
      match decEqListEntry ws1 ws2 with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .NDefault ws1, .NDefault ws2 =>
      match decEqListEntry ws1 ws2 with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .Assign ws1, .Assign ws2 =>
      match decEqListEntry ws1 ws2 with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .NAssign ws1, .NAssign ws2 =>
      match decEqListEntry ws1 ws2 with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .Error ws1, .Error ws2 =>
      match decEqListEntry ws1 ws2 with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .NError ws1, .NError ws2 =>
      match decEqListEntry ws1 ws2 with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .Alt ws1, .Alt ws2 =>
      match decEqListEntry ws1 ws2 with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .NAlt ws1, .NAlt ws2 =>
      match decEqListEntry ws1 ws2 with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .Length, .Length => isTrue rfl
  | .Substring side1 mode1 ws1, .Substring side2 mode2 ws2 =>
      match (inferInstance : Decidable (side1 = side2)),
            (inferInstance : Decidable (mode1 = mode2)),
            decEqListEntry ws1 ws2 with
      | isTrue h1, isTrue h2, isTrue h3 =>
          isTrue (by cases h1; cases h2; cases h3; rfl)
      | isFalse h, _, _ =>
          isFalse (by intro h'; cases h'; exact h rfl)
      | _, isFalse h, _ =>
          isFalse (by intro h'; cases h'; exact h rfl)
      | _, _, isFalse h =>
          isFalse (by intro h'; cases h'; exact h rfl)
  | .Normal, .Default _ => isFalse (by intro h; cases h)
  | .Normal, .NDefault _ => isFalse (by intro h; cases h)
  | .Normal, .Assign _ => isFalse (by intro h; cases h)
  | .Normal, .NAssign _ => isFalse (by intro h; cases h)
  | .Normal, .Error _ => isFalse (by intro h; cases h)
  | .Normal, .NError _ => isFalse (by intro h; cases h)
  | .Normal, .Alt _ => isFalse (by intro h; cases h)
  | .Normal, .NAlt _ => isFalse (by intro h; cases h)
  | .Normal, .Length => isFalse (by intro h; cases h)
  | .Normal, .Substring _ _ _ => isFalse (by intro h; cases h)

  | .Default _, .Normal => isFalse (by intro h; cases h)
  | .Default _, .NDefault _ => isFalse (by intro h; cases h)
  | .Default _, .Assign _ => isFalse (by intro h; cases h)
  | .Default _, .NAssign _ => isFalse (by intro h; cases h)
  | .Default _, .Error _ => isFalse (by intro h; cases h)
  | .Default _, .NError _ => isFalse (by intro h; cases h)
  | .Default _, .Alt _ => isFalse (by intro h; cases h)
  | .Default _, .NAlt _ => isFalse (by intro h; cases h)
  | .Default _, .Length => isFalse (by intro h; cases h)
  | .Default _, .Substring _ _ _ => isFalse (by intro h; cases h)

  | .NDefault _, .Normal => isFalse (by intro h; cases h)
  | .NDefault _, .Default _ => isFalse (by intro h; cases h)
  | .NDefault _, .Assign _ => isFalse (by intro h; cases h)
  | .NDefault _, .NAssign _ => isFalse (by intro h; cases h)
  | .NDefault _, .Error _ => isFalse (by intro h; cases h)
  | .NDefault _, .NError _ => isFalse (by intro h; cases h)
  | .NDefault _, .Alt _ => isFalse (by intro h; cases h)
  | .NDefault _, .NAlt _ => isFalse (by intro h; cases h)
  | .NDefault _, .Length => isFalse (by intro h; cases h)
  | .NDefault _, .Substring _ _ _ => isFalse (by intro h; cases h)

  | .Assign _, .Normal => isFalse (by intro h; cases h)
  | .Assign _, .Default _ => isFalse (by intro h; cases h)
  | .Assign _, .NDefault _ => isFalse (by intro h; cases h)
  | .Assign _, .NAssign _ => isFalse (by intro h; cases h)
  | .Assign _, .Error _ => isFalse (by intro h; cases h)
  | .Assign _, .NError _ => isFalse (by intro h; cases h)
  | .Assign _, .Alt _ => isFalse (by intro h; cases h)
  | .Assign _, .NAlt _ => isFalse (by intro h; cases h)
  | .Assign _, .Length => isFalse (by intro h; cases h)
  | .Assign _, .Substring _ _ _ => isFalse (by intro h; cases h)

  | .NAssign _, .Normal => isFalse (by intro h; cases h)
  | .NAssign _, .Default _ => isFalse (by intro h; cases h)
  | .NAssign _, .NDefault _ => isFalse (by intro h; cases h)
  | .NAssign _, .Assign _ => isFalse (by intro h; cases h)
  | .NAssign _, .Error _ => isFalse (by intro h; cases h)
  | .NAssign _, .NError _ => isFalse (by intro h; cases h)
  | .NAssign _, .Alt _ => isFalse (by intro h; cases h)
  | .NAssign _, .NAlt _ => isFalse (by intro h; cases h)
  | .NAssign _, .Length => isFalse (by intro h; cases h)
  | .NAssign _, .Substring _ _ _ => isFalse (by intro h; cases h)

  | .Error _, .Normal => isFalse (by intro h; cases h)
  | .Error _, .Default _ => isFalse (by intro h; cases h)
  | .Error _, .NDefault _ => isFalse (by intro h; cases h)
  | .Error _, .Assign _ => isFalse (by intro h; cases h)
  | .Error _, .NAssign _ => isFalse (by intro h; cases h)
  | .Error _, .NError _ => isFalse (by intro h; cases h)
  | .Error _, .Alt _ => isFalse (by intro h; cases h)
  | .Error _, .NAlt _ => isFalse (by intro h; cases h)
  | .Error _, .Length => isFalse (by intro h; cases h)
  | .Error _, .Substring _ _ _ => isFalse (by intro h; cases h)

  | .NError _, .Normal => isFalse (by intro h; cases h)
  | .NError _, .Default _ => isFalse (by intro h; cases h)
  | .NError _, .NDefault _ => isFalse (by intro h; cases h)
  | .NError _, .Assign _ => isFalse (by intro h; cases h)
  | .NError _, .NAssign _ => isFalse (by intro h; cases h)
  | .NError _, .Error _ => isFalse (by intro h; cases h)
  | .NError _, .Alt _ => isFalse (by intro h; cases h)
  | .NError _, .NAlt _ => isFalse (by intro h; cases h)
  | .NError _, .Length => isFalse (by intro h; cases h)
  | .NError _, .Substring _ _ _ => isFalse (by intro h; cases h)

  | .Alt _, .Normal => isFalse (by intro h; cases h)
  | .Alt _, .Default _ => isFalse (by intro h; cases h)
  | .Alt _, .NDefault _ => isFalse (by intro h; cases h)
  | .Alt _, .Assign _ => isFalse (by intro h; cases h)
  | .Alt _, .NAssign _ => isFalse (by intro h; cases h)
  | .Alt _, .Error _ => isFalse (by intro h; cases h)
  | .Alt _, .NError _ => isFalse (by intro h; cases h)
  | .Alt _, .NAlt _ => isFalse (by intro h; cases h)
  | .Alt _, .Length => isFalse (by intro h; cases h)
  | .Alt _, .Substring _ _ _ => isFalse (by intro h; cases h)

  | .NAlt _, .Normal => isFalse (by intro h; cases h)
  | .NAlt _, .Default _ => isFalse (by intro h; cases h)
  | .NAlt _, .NDefault _ => isFalse (by intro h; cases h)
  | .NAlt _, .Assign _ => isFalse (by intro h; cases h)
  | .NAlt _, .NAssign _ => isFalse (by intro h; cases h)
  | .NAlt _, .Error _ => isFalse (by intro h; cases h)
  | .NAlt _, .NError _ => isFalse (by intro h; cases h)
  | .NAlt _, .Alt _ => isFalse (by intro h; cases h)
  | .NAlt _, .Length => isFalse (by intro h; cases h)
  | .NAlt _, .Substring _ _ _ => isFalse (by intro h; cases h)

  | .Length, .Normal => isFalse (by intro h; cases h)
  | .Length, .Default _ => isFalse (by intro h; cases h)
  | .Length, .NDefault _ => isFalse (by intro h; cases h)
  | .Length, .Assign _ => isFalse (by intro h; cases h)
  | .Length, .NAssign _ => isFalse (by intro h; cases h)
  | .Length, .Error _ => isFalse (by intro h; cases h)
  | .Length, .NError _ => isFalse (by intro h; cases h)
  | .Length, .Alt _ => isFalse (by intro h; cases h)
  | .Length, .NAlt _ => isFalse (by intro h; cases h)
  | .Length, .Substring _ _ _ => isFalse (by intro h; cases h)

  | .Substring _ _ _, .Normal => isFalse (by intro h; cases h)
  | .Substring _ _ _, .Default _ => isFalse (by intro h; cases h)
  | .Substring _ _ _, .NDefault _ => isFalse (by intro h; cases h)
  | .Substring _ _ _, .Assign _ => isFalse (by intro h; cases h)
  | .Substring _ _ _, .NAssign _ => isFalse (by intro h; cases h)
  | .Substring _ _ _, .Error _ => isFalse (by intro h; cases h)
  | .Substring _ _ _, .NError _ => isFalse (by intro h; cases h)
  | .Substring _ _ _, .Alt _ => isFalse (by intro h; cases h)
  | .Substring _ _ _, .NAlt _ => isFalse (by intro h; cases h)
  | .Substring _ _ _, .Length => isFalse (by intro h; cases h)
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by repeat' (simp_wf; omega)

  private def decEqControl : (a b : control) → Decidable (a = b)
  | .Tilde s1, .Tilde s2 =>
      match (inferInstance : Decidable (s1 = s2)) with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .Param n1 f1, .Param n2 f2 =>
      match (inferInstance : Decidable (n1 = n2)),
            decEqFormat f1 f2 with
      | isTrue h1, isTrue h2 => isTrue (by cases h1; cases h2; rfl)
      | isFalse h, _ => isFalse (by intro h'; cases h'; exact h rfl)
      | _, isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .LAssign n1 ew1 ws1, .LAssign n2 ew2 ws2 =>
      match (inferInstance : Decidable (n1 = n2)),
            decEqListExpandedWord ew1 ew2,
            decEqListEntry ws1 ws2 with
      | isTrue h1, isTrue h2, isTrue h3 =>
          isTrue (by cases h1; cases h2; cases h3; rfl)
      | isFalse h, _, _ => isFalse (by intro h'; cases h'; exact h rfl)
      | _, isFalse h, _ => isFalse (by intro h'; cases h'; exact h rfl)
      | _, _, isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .LMatch fs1 side1 mode1 ew1 ws1, .LMatch fs2 side2 mode2 ew2 ws2 =>
      match (inferInstance : Decidable (fs1 = fs2)),
            (inferInstance : Decidable (side1 = side2)),
            (inferInstance : Decidable (mode1 = mode2)),
            decEqListExpandedWord ew1 ew2,
            decEqListEntry ws1 ws2 with
      | isTrue h1, isTrue h2, isTrue h3, isTrue h4, isTrue h5 =>
          isTrue (by cases h1; cases h2; cases h3; cases h4; cases h5; rfl)
      | isFalse h, _, _, _, _ => isFalse (by intro h'; cases h'; exact h rfl)
      | _, isFalse h, _, _, _ => isFalse (by intro h'; cases h'; exact h rfl)
      | _, _, isFalse h, _, _ => isFalse (by intro h'; cases h'; exact h rfl)
      | _, _, _, isFalse h, _ => isFalse (by intro h'; cases h'; exact h rfl)
      | _, _, _, _, isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .LError n1 ew1 ws1, .LError n2 ew2 ws2 =>
      match (inferInstance : Decidable (n1 = n2)),
            decEqListExpandedWord ew1 ew2,
            decEqListEntry ws1 ws2 with
      | isTrue h1, isTrue h2, isTrue h3 =>
          isTrue (by cases h1; cases h2; cases h3; rfl)
      | isFalse h, _, _ => isFalse (by intro h'; cases h'; exact h rfl)
      | _, isFalse h, _ => isFalse (by intro h'; cases h'; exact h rfl)
      | _, _, isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .Backtick st1, .Backtick st2 =>
      match decEqStmt st1 st2 with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .LBacktick orig1 p1 f1, .LBacktick orig2 p2 f2 =>
      match decEqStmt orig1 orig2,
            (inferInstance : Decidable (p1 = p2)),
            (inferInstance : Decidable (f1 = f2)) with
      | isTrue h1, isTrue h2, isTrue h3 =>
          isTrue (by cases h1; cases h2; cases h3; rfl)
      | isFalse h, _, _ => isFalse (by intro h'; cases h'; exact h rfl)
      | _, isFalse h, _ => isFalse (by intro h'; cases h'; exact h rfl)
      | _, _, isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .LBacktickWait orig1 p1 r1, .LBacktickWait orig2 p2 r2 =>
      match decEqStmt orig1 orig2,
            (inferInstance : Decidable (p1 = p2)),
            (inferInstance : Decidable (r1 = r2)) with
      | isTrue h1, isTrue h2, isTrue h3 =>
          isTrue (by cases h1; cases h2; cases h3; rfl)
      | isFalse h, _, _ => isFalse (by intro h'; cases h'; exact h rfl)
      | _, isFalse h, _ => isFalse (by intro h'; cases h'; exact h rfl)
      | _, _, isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .Arith ew1 ws1, .Arith ew2 ws2 =>
      match decEqListExpandedWord ew1 ew2, decEqListEntry ws1 ws2 with
      | isTrue h1, isTrue h2 => isTrue (by cases h1; cases h2; rfl)
      | isFalse h, _ => isFalse (by intro h'; cases h'; exact h rfl)
      | _, isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .Quote ew1 ws1, .Quote ew2 ws2 =>
      match decEqListExpandedWord ew1 ew2, decEqListEntry ws1 ws2 with
      | isTrue h1, isTrue h2 => isTrue (by cases h1; cases h2; rfl)
      | isFalse h, _ => isFalse (by intro h'; cases h'; exact h rfl)
      | _, isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .Escape c1, .Escape c2 =>
      match (inferInstance : Decidable (c1 = c2)) with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)

  | .Tilde _, .Param _ _ => isFalse (by intro h; cases h)
  | .Tilde _, .LAssign _ _ _ => isFalse (by intro h; cases h)
  | .Tilde _, .LMatch _ _ _ _ _ => isFalse (by intro h; cases h)
  | .Tilde _, .LError _ _ _ => isFalse (by intro h; cases h)
  | .Tilde _, .Backtick _ => isFalse (by intro h; cases h)
  | .Tilde _, .LBacktick _ _ _ => isFalse (by intro h; cases h)
  | .Tilde _, .LBacktickWait _ _ _ => isFalse (by intro h; cases h)
  | .Tilde _, .Arith _ _ => isFalse (by intro h; cases h)
  | .Tilde _, .Quote _ _ => isFalse (by intro h; cases h)
  | .Tilde _, .Escape _ => isFalse (by intro h; cases h)

  | .Param _ _, .Tilde _ => isFalse (by intro h; cases h)
  | .Param _ _, .LAssign _ _ _ => isFalse (by intro h; cases h)
  | .Param _ _, .LMatch _ _ _ _ _ => isFalse (by intro h; cases h)
  | .Param _ _, .LError _ _ _ => isFalse (by intro h; cases h)
  | .Param _ _, .Backtick _ => isFalse (by intro h; cases h)
  | .Param _ _, .LBacktick _ _ _ => isFalse (by intro h; cases h)
  | .Param _ _, .LBacktickWait _ _ _ => isFalse (by intro h; cases h)
  | .Param _ _, .Arith _ _ => isFalse (by intro h; cases h)
  | .Param _ _, .Quote _ _ => isFalse (by intro h; cases h)
  | .Param _ _, .Escape _ => isFalse (by intro h; cases h)

  | .LAssign _ _ _, .Tilde _ => isFalse (by intro h; cases h)
  | .LAssign _ _ _, .Param _ _ => isFalse (by intro h; cases h)
  | .LAssign _ _ _, .LMatch _ _ _ _ _ => isFalse (by intro h; cases h)
  | .LAssign _ _ _, .LError _ _ _ => isFalse (by intro h; cases h)
  | .LAssign _ _ _, .Backtick _ => isFalse (by intro h; cases h)
  | .LAssign _ _ _, .LBacktick _ _ _ => isFalse (by intro h; cases h)
  | .LAssign _ _ _, .LBacktickWait _ _ _ => isFalse (by intro h; cases h)
  | .LAssign _ _ _, .Arith _ _ => isFalse (by intro h; cases h)
  | .LAssign _ _ _, .Quote _ _ => isFalse (by intro h; cases h)
  | .LAssign _ _ _, .Escape _ => isFalse (by intro h; cases h)

  | .LMatch _ _ _ _ _, .Tilde _ => isFalse (by intro h; cases h)
  | .LMatch _ _ _ _ _, .Param _ _ => isFalse (by intro h; cases h)
  | .LMatch _ _ _ _ _, .LAssign _ _ _ => isFalse (by intro h; cases h)
  | .LMatch _ _ _ _ _, .LError _ _ _ => isFalse (by intro h; cases h)
  | .LMatch _ _ _ _ _, .Backtick _ => isFalse (by intro h; cases h)
  | .LMatch _ _ _ _ _, .LBacktick _ _ _ => isFalse (by intro h; cases h)
  | .LMatch _ _ _ _ _, .LBacktickWait _ _ _ => isFalse (by intro h; cases h)
  | .LMatch _ _ _ _ _, .Arith _ _ => isFalse (by intro h; cases h)
  | .LMatch _ _ _ _ _, .Quote _ _ => isFalse (by intro h; cases h)
  | .LMatch _ _ _ _ _, .Escape _ => isFalse (by intro h; cases h)

  | .LError _ _ _, .Tilde _ => isFalse (by intro h; cases h)
  | .LError _ _ _, .Param _ _ => isFalse (by intro h; cases h)
  | .LError _ _ _, .LAssign _ _ _ => isFalse (by intro h; cases h)
  | .LError _ _ _, .LMatch _ _ _ _ _ => isFalse (by intro h; cases h)
  | .LError _ _ _, .Backtick _ => isFalse (by intro h; cases h)
  | .LError _ _ _, .LBacktick _ _ _ => isFalse (by intro h; cases h)
  | .LError _ _ _, .LBacktickWait _ _ _ => isFalse (by intro h; cases h)
  | .LError _ _ _, .Arith _ _ => isFalse (by intro h; cases h)
  | .LError _ _ _, .Quote _ _ => isFalse (by intro h; cases h)
  | .LError _ _ _, .Escape _ => isFalse (by intro h; cases h)

  | .Backtick _, .Tilde _ => isFalse (by intro h; cases h)
  | .Backtick _, .Param _ _ => isFalse (by intro h; cases h)
  | .Backtick _, .LAssign _ _ _ => isFalse (by intro h; cases h)
  | .Backtick _, .LMatch _ _ _ _ _ => isFalse (by intro h; cases h)
  | .Backtick _, .LError _ _ _ => isFalse (by intro h; cases h)
  | .Backtick _, .LBacktick _ _ _ => isFalse (by intro h; cases h)
  | .Backtick _, .LBacktickWait _ _ _ => isFalse (by intro h; cases h)
  | .Backtick _, .Arith _ _ => isFalse (by intro h; cases h)
  | .Backtick _, .Quote _ _ => isFalse (by intro h; cases h)
  | .Backtick _, .Escape _ => isFalse (by intro h; cases h)

  | .LBacktick _ _ _, .Tilde _ => isFalse (by intro h; cases h)
  | .LBacktick _ _ _, .Param _ _ => isFalse (by intro h; cases h)
  | .LBacktick _ _ _, .LAssign _ _ _ => isFalse (by intro h; cases h)
  | .LBacktick _ _ _, .LMatch _ _ _ _ _ => isFalse (by intro h; cases h)
  | .LBacktick _ _ _, .LError _ _ _ => isFalse (by intro h; cases h)
  | .LBacktick _ _ _, .Backtick _ => isFalse (by intro h; cases h)
  | .LBacktick _ _ _, .LBacktickWait _ _ _ => isFalse (by intro h; cases h)
  | .LBacktick _ _ _, .Arith _ _ => isFalse (by intro h; cases h)
  | .LBacktick _ _ _, .Quote _ _ => isFalse (by intro h; cases h)
  | .LBacktick _ _ _, .Escape _ => isFalse (by intro h; cases h)

  | .LBacktickWait _ _ _, .Tilde _ => isFalse (by intro h; cases h)
  | .LBacktickWait _ _ _, .Param _ _ => isFalse (by intro h; cases h)
  | .LBacktickWait _ _ _, .LAssign _ _ _ => isFalse (by intro h; cases h)
  | .LBacktickWait _ _ _, .LMatch _ _ _ _ _ => isFalse (by intro h; cases h)
  | .LBacktickWait _ _ _, .LError _ _ _ => isFalse (by intro h; cases h)
  | .LBacktickWait _ _ _, .Backtick _ => isFalse (by intro h; cases h)
  | .LBacktickWait _ _ _, .LBacktick _ _ _ => isFalse (by intro h; cases h)
  | .LBacktickWait _ _ _, .Arith _ _ => isFalse (by intro h; cases h)
  | .LBacktickWait _ _ _, .Quote _ _ => isFalse (by intro h; cases h)
  | .LBacktickWait _ _ _, .Escape _ => isFalse (by intro h; cases h)

  | .Arith _ _, .Tilde _ => isFalse (by intro h; cases h)
  | .Arith _ _, .Param _ _ => isFalse (by intro h; cases h)
  | .Arith _ _, .LAssign _ _ _ => isFalse (by intro h; cases h)
  | .Arith _ _, .LMatch _ _ _ _ _ => isFalse (by intro h; cases h)
  | .Arith _ _, .LError _ _ _ => isFalse (by intro h; cases h)
  | .Arith _ _, .Backtick _ => isFalse (by intro h; cases h)
  | .Arith _ _, .LBacktick _ _ _ => isFalse (by intro h; cases h)
  | .Arith _ _, .LBacktickWait _ _ _ => isFalse (by intro h; cases h)
  | .Arith _ _, .Quote _ _ => isFalse (by intro h; cases h)
  | .Arith _ _, .Escape _ => isFalse (by intro h; cases h)

  | .Quote _ _, .Tilde _ => isFalse (by intro h; cases h)
  | .Quote _ _, .Param _ _ => isFalse (by intro h; cases h)
  | .Quote _ _, .LAssign _ _ _ => isFalse (by intro h; cases h)
  | .Quote _ _, .LMatch _ _ _ _ _ => isFalse (by intro h; cases h)
  | .Quote _ _, .LError _ _ _ => isFalse (by intro h; cases h)
  | .Quote _ _, .Backtick _ => isFalse (by intro h; cases h)
  | .Quote _ _, .LBacktick _ _ _ => isFalse (by intro h; cases h)
  | .Quote _ _, .LBacktickWait _ _ _ => isFalse (by intro h; cases h)
  | .Quote _ _, .Arith _ _ => isFalse (by intro h; cases h)
  | .Quote _ _, .Escape _ => isFalse (by intro h; cases h)

  | .Escape _, .Tilde _ => isFalse (by intro h; cases h)
  | .Escape _, .Param _ _ => isFalse (by intro h; cases h)
  | .Escape _, .LAssign _ _ _ => isFalse (by intro h; cases h)
  | .Escape _, .LMatch _ _ _ _ _ => isFalse (by intro h; cases h)
  | .Escape _, .LError _ _ _ => isFalse (by intro h; cases h)
  | .Escape _, .Backtick _ => isFalse (by intro h; cases h)
  | .Escape _, .LBacktick _ _ _ => isFalse (by intro h; cases h)
  | .Escape _, .LBacktickWait _ _ _ => isFalse (by intro h; cases h)
  | .Escape _, .Arith _ _ => isFalse (by intro h; cases h)
  | .Escape _, .Quote _ _ => isFalse (by intro h; cases h)
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by repeat' (simp_wf; omega)

  private def decEqEntry : (a b : entry) → Decidable (a = b)
    | .S s1, .S s2 =>
        match (inferInstance : Decidable (s1 = s2)) with
        | isTrue h  => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .K c1, .K c2 =>
        match decEqControl c1 c2 with
        | isTrue h  => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .F, .F =>
        isTrue rfl
    | .ESym x1, .ESym x2 =>
        match decEqSym x1 x2 with
        | isTrue h  => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)

    | .S _, .K _ => isFalse (by intro h; cases h)
    | .S _, .F => isFalse (by intro h; cases h)
    | .S _, .ESym _ => isFalse (by intro h; cases h)

    | .K _, .S _ => isFalse (by intro h; cases h)
    | .K _, .F => isFalse (by intro h; cases h)
    | .K _, .ESym _ => isFalse (by intro h; cases h)

    | .F, .S _ => isFalse (by intro h; cases h)
    | .F, .K _ => isFalse (by intro h; cases h)
    | .F, .ESym _ => isFalse (by intro h; cases h)

    | .ESym _, .S _ => isFalse (by intro h; cases h)
    | .ESym _, .K _ => isFalse (by intro h; cases h)
    | .ESym _, .F => isFalse (by intro h; cases h)
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by repeat' (simp_wf; omega)

  private def decEqRedir : (a b : redir) → Decidable (a = b)
    | .RFile rt1 n1 ws1, .RFile rt2 n2 ws2 =>
        match (inferInstance : Decidable (rt1 = rt2)),
              (inferInstance : Decidable (n1 = n2)),
              decEqListEntry ws1 ws2 with
        | isTrue h1, isTrue h2, isTrue h3 =>
            isTrue (by cases h1; cases h2; cases h3; rfl)
        | isFalse h, _, _ =>
            isFalse (by intro h'; cases h'; exact h rfl)
        | _, isFalse h, _ =>
            isFalse (by intro h'; cases h'; exact h rfl)
        | _, _, isFalse h =>
            isFalse (by intro h'; cases h'; exact h rfl)
    | .RDup dt1 n1 ws1, .RDup dt2 n2 ws2 =>
        match (inferInstance : Decidable (dt1 = dt2)),
              (inferInstance : Decidable (n1 = n2)),
              decEqListEntry ws1 ws2 with
        | isTrue h1, isTrue h2, isTrue h3 =>
            isTrue (by cases h1; cases h2; cases h3; rfl)
        | isFalse h, _, _ =>
            isFalse (by intro h'; cases h'; exact h rfl)
        | _, isFalse h, _ =>
            isFalse (by intro h'; cases h'; exact h rfl)
        | _, _, isFalse h =>
            isFalse (by intro h'; cases h'; exact h rfl)
    | .RHeredoc ht1 n1 ws1, .RHeredoc ht2 n2 ws2 =>
        match (inferInstance : Decidable (ht1 = ht2)),
              (inferInstance : Decidable (n1 = n2)),
              decEqListEntry ws1 ws2 with
        | isTrue h1, isTrue h2, isTrue h3 =>
            isTrue (by cases h1; cases h2; cases h3; rfl)
        | isFalse h, _, _ =>
            isFalse (by intro h'; cases h'; exact h rfl)
        | _, isFalse h, _ =>
            isFalse (by intro h'; cases h'; exact h rfl)
        | _, _, isFalse h =>
            isFalse (by intro h'; cases h'; exact h rfl)

    | .RFile _ _ _, .RDup _ _ _ => isFalse (by intro h; cases h)
    | .RFile _ _ _, .RHeredoc _ _ _ => isFalse (by intro h; cases h)

    | .RDup _ _ _, .RFile _ _ _ => isFalse (by intro h; cases h)
    | .RDup _ _ _, .RHeredoc _ _ _ => isFalse (by intro h; cases h)

    | .RHeredoc _ _ _, .RFile _ _ _ => isFalse (by intro h; cases h)
    | .RHeredoc _ _ _, .RDup _ _ _ => isFalse (by intro h; cases h)
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by repeat' (simp_wf; omega)

  private def decEqExpandingRedir : (a b : expanding_redir) → Decidable (a = b)
    | .XRFile rt1 n1 st1, .XRFile rt2 n2 st2 =>
        match (inferInstance : Decidable (rt1 = rt2)),
              (inferInstance : Decidable (n1 = n2)),
              decEqExpansionState st1 st2 with
        | isTrue h1, isTrue h2, isTrue h3 =>
            isTrue (by cases h1; cases h2; cases h3; rfl)
        | isFalse h, _, _ =>
            isFalse (by intro h'; cases h'; exact h rfl)
        | _, isFalse h, _ =>
            isFalse (by intro h'; cases h'; exact h rfl)
        | _, _, isFalse h =>
            isFalse (by intro h'; cases h'; exact h rfl)
    | .XRDup dt1 n1 st1, .XRDup dt2 n2 st2 =>
        match (inferInstance : Decidable (dt1 = dt2)),
              (inferInstance : Decidable (n1 = n2)),
              decEqExpansionState st1 st2 with
        | isTrue h1, isTrue h2, isTrue h3 =>
            isTrue (by cases h1; cases h2; cases h3; rfl)
        | isFalse h, _, _ =>
            isFalse (by intro h'; cases h'; exact h rfl)
        | _, isFalse h, _ =>
            isFalse (by intro h'; cases h'; exact h rfl)
        | _, _, isFalse h =>
            isFalse (by intro h'; cases h'; exact h rfl)
    | .XRHeredoc ht1 n1 st1, .XRHeredoc ht2 n2 st2 =>
        match (inferInstance : Decidable (ht1 = ht2)),
              (inferInstance : Decidable (n1 = n2)),
              decEqExpansionState st1 st2 with
        | isTrue h1, isTrue h2, isTrue h3 =>
            isTrue (by cases h1; cases h2; cases h3; rfl)
        | isFalse h, _, _ =>
            isFalse (by intro h'; cases h'; exact h rfl)
        | _, isFalse h, _ =>
            isFalse (by intro h'; cases h'; exact h rfl)
        | _, _, isFalse h =>
            isFalse (by intro h'; cases h'; exact h rfl)

    | .XRFile _ _ _, .XRDup _ _ _ => isFalse (by intro h; cases h)
    | .XRFile _ _ _, .XRHeredoc _ _ _ => isFalse (by intro h; cases h)

    | .XRDup _ _ _, .XRFile _ _ _ => isFalse (by intro h; cases h)
    | .XRDup _ _ _, .XRHeredoc _ _ _ => isFalse (by intro h; cases h)

    | .XRHeredoc _ _ _, .XRFile _ _ _ => isFalse (by intro h; cases h)
    | .XRHeredoc _ _ _, .XRDup _ _ _ => isFalse (by intro h; cases h)
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by repeat' (simp_wf; omega)

  private def decEqExpandedRedir : (a b : expanded_redir) → Decidable (a = b)
    | .ERFile rt1 n1 s1, .ERFile rt2 n2 s2 =>
        match (inferInstance : Decidable (rt1 = rt2)),
              (inferInstance : Decidable (n1 = n2)),
              decEqListSymbolicChar s1 s2 with
        | isTrue h1, isTrue h2, isTrue h3 =>
            isTrue (by cases h1; cases h2; cases h3; rfl)
        | isFalse h, _, _ =>
            isFalse (by intro h'; cases h'; exact h rfl)
        | _, isFalse h, _ =>
            isFalse (by intro h'; cases h'; exact h rfl)
        | _, _, isFalse h =>
            isFalse (by intro h'; cases h'; exact h rfl)
    | .ERDup dt1 orig1 n1 m1, .ERDup dt2 orig2 n2 m2 =>
        match (inferInstance : Decidable (dt1 = dt2)),
              (inferInstance : Decidable (orig1 = orig2)),
              (inferInstance : Decidable (n1 = n2)),
              decEqOptionNat m1 m2 with
        | isTrue h1, isTrue h2, isTrue h3, isTrue h4 =>
            isTrue (by cases h1; cases h2; cases h3; cases h4; rfl)
        | isFalse h, _, _, _ =>
            isFalse (by intro h'; cases h'; exact h rfl)
        | _, isFalse h, _, _ =>
            isFalse (by intro h'; cases h'; exact h rfl)
        | _, _, isFalse h, _ =>
            isFalse (by intro h'; cases h'; exact h rfl)
        | _, _, _, isFalse h =>
            isFalse (by intro h'; cases h'; exact h rfl)
    | .ERHeredoc ht1 n1 s1, .ERHeredoc ht2 n2 s2 =>
        match (inferInstance : Decidable (ht1 = ht2)),
              (inferInstance : Decidable (n1 = n2)),
              decEqListSymbolicChar s1 s2 with
        | isTrue h1, isTrue h2, isTrue h3 =>
            isTrue (by cases h1; cases h2; cases h3; rfl)
        | isFalse h, _, _ =>
            isFalse (by intro h'; cases h'; exact h rfl)
        | _, isFalse h, _ =>
            isFalse (by intro h'; cases h'; exact h rfl)
        | _, _, isFalse h =>
            isFalse (by intro h'; cases h'; exact h rfl)

    | .ERFile _ _ _, .ERDup _ _ _ _ => isFalse (by intro h; cases h)
    | .ERFile _ _ _, .ERHeredoc _ _ _ => isFalse (by intro h; cases h)

    | .ERDup _ _ _ _, .ERFile _ _ _ => isFalse (by intro h; cases h)
    | .ERDup _ _ _ _, .ERHeredoc _ _ _ => isFalse (by intro h; cases h)

    | .ERHeredoc _ _ _, .ERFile _ _ _ => isFalse (by intro h; cases h)
    | .ERHeredoc _ _ _, .ERDup _ _ _ _ => isFalse (by intro h; cases h)
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by repeat' (simp_wf; omega)

  private def decEqSymbolicChar : (a b : symbolic_char) → Decidable (a = b)
  | .C c1, .C c2 =>
      match (inferInstance : Decidable (c1 = c2)) with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .Sym s1, .Sym s2 =>
      match decEqSym s1 s2 with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)

  | .C _, .Sym _ => isFalse (by intro h; cases h)
  | .Sym _, .C _ => isFalse (by intro h; cases h)
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by repeat' (simp_wf; omega)

  private def decEqSym : (a b : sym) → Decidable (a = b)
  | .SymArith fs1, .SymArith fs2 =>
      match decEqListListSymbolicChar fs1 fs2 with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .SymCommand st1, .SymCommand st2 =>
      match decEqStmt st1 st2 with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .SymPat side1 mode1 pat1 str1, .SymPat side2 mode2 pat2 str2 =>
      match (inferInstance : Decidable (side1 = side2)),
            (inferInstance : Decidable (mode1 = mode2)),
            decEqListSymbolicChar pat1 pat2,
            decEqListSymbolicChar str1 str2 with
      | isTrue h1, isTrue h2, isTrue h3, isTrue h4 =>
          isTrue (by cases h1; cases h2; cases h3; cases h4; rfl)
      | isFalse h, _, _, _ =>
          isFalse (by intro h'; cases h'; exact h rfl)
      | _, isFalse h, _, _ =>
          isFalse (by intro h'; cases h'; exact h rfl)
      | _, _, isFalse h, _ =>
          isFalse (by intro h'; cases h'; exact h rfl)
      | _, _, _, isFalse h =>
          isFalse (by intro h'; cases h'; exact h rfl)

  | .SymArith _, .SymCommand _ => isFalse (by intro h; cases h)
  | .SymArith _, .SymPat _ _ _ _ => isFalse (by intro h; cases h)

  | .SymCommand _, .SymArith _ => isFalse (by intro h; cases h)
  | .SymCommand _, .SymPat _ _ _ _ => isFalse (by intro h; cases h)

  | .SymPat _ _ _ _, .SymArith _ => isFalse (by intro h; cases h)
  | .SymPat _ _ _ _, .SymCommand _ => isFalse (by intro h; cases h)
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by repeat' (simp_wf; omega)

  private def decEqExpandedWord : (a b : expanded_word) → Decidable (a = b)
    | .UsrF, .UsrF =>
        isTrue rfl
    | .ExpS s1, .ExpS s2 =>
        match (inferInstance : Decidable (s1 = s2)) with
        | isTrue h  => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .UsrS s1, .UsrS s2 =>
        match (inferInstance : Decidable (s1 = s2)) with
        | isTrue h  => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .At fs1, .At fs2 =>
        match decEqListListSymbolicChar fs1 fs2 with
        | isTrue h  => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .DQuo s1, .DQuo s2 =>
        match decEqListSymbolicChar s1 s2 with
        | isTrue h  => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .EWSym x1, .EWSym x2 =>
        match decEqSym x1 x2 with
        | isTrue h  => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)

    | .UsrF, .ExpS _ => isFalse (by intro h; cases h)
    | .UsrF, .UsrS _ => isFalse (by intro h; cases h)
    | .UsrF, .At _ => isFalse (by intro h; cases h)
    | .UsrF, .DQuo _ => isFalse (by intro h; cases h)
    | .UsrF, .EWSym _ => isFalse (by intro h; cases h)

    | .ExpS _, .UsrF => isFalse (by intro h; cases h)
    | .ExpS _, .UsrS _ => isFalse (by intro h; cases h)
    | .ExpS _, .At _ => isFalse (by intro h; cases h)
    | .ExpS _, .DQuo _ => isFalse (by intro h; cases h)
    | .ExpS _, .EWSym _ => isFalse (by intro h; cases h)

    | .UsrS _, .UsrF => isFalse (by intro h; cases h)
    | .UsrS _, .ExpS _ => isFalse (by intro h; cases h)
    | .UsrS _, .At _ => isFalse (by intro h; cases h)
    | .UsrS _, .DQuo _ => isFalse (by intro h; cases h)
    | .UsrS _, .EWSym _ => isFalse (by intro h; cases h)

    | .At _, .UsrF => isFalse (by intro h; cases h)
    | .At _, .ExpS _ => isFalse (by intro h; cases h)
    | .At _, .UsrS _ => isFalse (by intro h; cases h)
    | .At _, .DQuo _ => isFalse (by intro h; cases h)
    | .At _, .EWSym _ => isFalse (by intro h; cases h)

    | .DQuo _, .UsrF => isFalse (by intro h; cases h)
    | .DQuo _, .ExpS _ => isFalse (by intro h; cases h)
    | .DQuo _, .UsrS _ => isFalse (by intro h; cases h)
    | .DQuo _, .At _ => isFalse (by intro h; cases h)
    | .DQuo _, .EWSym _ => isFalse (by intro h; cases h)

    | .EWSym _, .UsrF => isFalse (by intro h; cases h)
    | .EWSym _, .ExpS _ => isFalse (by intro h; cases h)
    | .EWSym _, .UsrS _ => isFalse (by intro h; cases h)
    | .EWSym _, .At _ => isFalse (by intro h; cases h)
    | .EWSym _, .DQuo _ => isFalse (by intro h; cases h)
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by repeat' (simp_wf; omega)

  private def decEqTmpField : (a b : tmp_field) → Decidable (a = b)
  | .WFS, .WFS => isTrue rfl
  | .FS, .FS => isTrue rfl
  | .Field s1, .Field s2 =>
      match decEqListSymbolicChar s1 s2 with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .QField s1, .QField s2 =>
      match decEqListSymbolicChar s1 s2 with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)

  | .WFS, .FS => isFalse (by intro h; cases h)
  | .WFS, .Field _ => isFalse (by intro h; cases h)
  | .WFS, .QField _ => isFalse (by intro h; cases h)

  | .FS, .WFS => isFalse (by intro h; cases h)
  | .FS, .Field _ => isFalse (by intro h; cases h)
  | .FS, .QField _ => isFalse (by intro h; cases h)

  | .Field _, .WFS => isFalse (by intro h; cases h)
  | .Field _, .FS => isFalse (by intro h; cases h)
  | .Field _, .QField _ => isFalse (by intro h; cases h)

  | .QField _, .WFS => isFalse (by intro h; cases h)
  | .QField _, .FS => isFalse (by intro h; cases h)
  | .QField _, .Field _ => isFalse (by intro h; cases h)
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by repeat' (simp_wf; omega)

  private def decEqExpansionState : (a b : expansion_state) → Decidable (a = b)
  | .ExpStart opts1 ws1, .ExpStart opts2 ws2 =>
      match decEqExpansionOpts opts1 opts2,
            decEqListEntry ws1 ws2 with
      | isTrue h1, isTrue h2 => isTrue (by cases h1; cases h2; rfl)
      | isFalse h, _ => isFalse (by intro h'; cases h'; exact h rfl)
      | _, isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .ExpExpand opts1 ews1 ws1, .ExpExpand opts2 ews2 ws2 =>
      match decEqExpansionOpts opts1 opts2,
            decEqListExpandedWord ews1 ews2,
            decEqListEntry ws1 ws2 with
      | isTrue h1, isTrue h2, isTrue h3 =>
          isTrue (by cases h1; cases h2; cases h3; rfl)
      | isFalse h, _, _ =>
          isFalse (by intro h'; cases h'; exact h rfl)
      | _, isFalse h, _ =>
          isFalse (by intro h'; cases h'; exact h rfl)
      | _, _, isFalse h =>
          isFalse (by intro h'; cases h'; exact h rfl)
  | .ExpSplit opts1 ews1, .ExpSplit opts2 ews2 =>
      match decEqExpansionOpts opts1 opts2,
            decEqListExpandedWord ews1 ews2 with
      | isTrue h1, isTrue h2 =>
          isTrue (by cases h1; cases h2; rfl)
      | isFalse h, _ =>
          isFalse (by intro h'; cases h'; exact h rfl)
      | _, isFalse h =>
          isFalse (by intro h'; cases h'; exact h rfl)
  | .ExpPath opts1 ifs1, .ExpPath opts2 ifs2 =>
      match decEqExpansionOpts opts1 opts2,
            decEqListTmpField ifs1 ifs2 with
      | isTrue h1, isTrue h2 =>
          isTrue (by cases h1; cases h2; rfl)
      | isFalse h, _ =>
          isFalse (by intro h'; cases h'; exact h rfl)
      | _, isFalse h =>
          isFalse (by intro h'; cases h'; exact h rfl)
  | .ExpQuote opts1 ifs1, .ExpQuote opts2 ifs2 =>
      match decEqExpansionOpts opts1 opts2,
            decEqListTmpField ifs1 ifs2 with
      | isTrue h1, isTrue h2 =>
          isTrue (by cases h1; cases h2; rfl)
      | isFalse h, _ =>
          isFalse (by intro h'; cases h'; exact h rfl)
      | _, isFalse h =>
          isFalse (by intro h'; cases h'; exact h rfl)
  | .ExpError fs1, .ExpError fs2 =>
      match decEqListListSymbolicChar fs1 fs2 with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .ExpDone fs1, .ExpDone fs2 =>
      match decEqListListSymbolicChar fs1 fs2 with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)

  | .ExpStart _ _, .ExpExpand _ _ _ => isFalse (by intro h; cases h)
  | .ExpStart _ _, .ExpSplit _ _ => isFalse (by intro h; cases h)
  | .ExpStart _ _, .ExpPath _ _ => isFalse (by intro h; cases h)
  | .ExpStart _ _, .ExpQuote _ _ => isFalse (by intro h; cases h)
  | .ExpStart _ _, .ExpError _ => isFalse (by intro h; cases h)
  | .ExpStart _ _, .ExpDone _ => isFalse (by intro h; cases h)

  | .ExpExpand _ _ _, .ExpStart _ _ => isFalse (by intro h; cases h)
  | .ExpExpand _ _ _, .ExpSplit _ _ => isFalse (by intro h; cases h)
  | .ExpExpand _ _ _, .ExpPath _ _ => isFalse (by intro h; cases h)
  | .ExpExpand _ _ _, .ExpQuote _ _ => isFalse (by intro h; cases h)
  | .ExpExpand _ _ _, .ExpError _ => isFalse (by intro h; cases h)
  | .ExpExpand _ _ _, .ExpDone _ => isFalse (by intro h; cases h)

  | .ExpSplit _ _, .ExpStart _ _ => isFalse (by intro h; cases h)
  | .ExpSplit _ _, .ExpExpand _ _ _ => isFalse (by intro h; cases h)
  | .ExpSplit _ _, .ExpPath _ _ => isFalse (by intro h; cases h)
  | .ExpSplit _ _, .ExpQuote _ _ => isFalse (by intro h; cases h)
  | .ExpSplit _ _, .ExpError _ => isFalse (by intro h; cases h)
  | .ExpSplit _ _, .ExpDone _ => isFalse (by intro h; cases h)

  | .ExpPath _ _, .ExpStart _ _ => isFalse (by intro h; cases h)
  | .ExpPath _ _, .ExpExpand _ _ _ => isFalse (by intro h; cases h)
  | .ExpPath _ _, .ExpSplit _ _ => isFalse (by intro h; cases h)
  | .ExpPath _ _, .ExpQuote _ _ => isFalse (by intro h; cases h)
  | .ExpPath _ _, .ExpError _ => isFalse (by intro h; cases h)
  | .ExpPath _ _, .ExpDone _ => isFalse (by intro h; cases h)

  | .ExpQuote _ _, .ExpStart _ _ => isFalse (by intro h; cases h)
  | .ExpQuote _ _, .ExpExpand _ _ _ => isFalse (by intro h; cases h)
  | .ExpQuote _ _, .ExpSplit _ _ => isFalse (by intro h; cases h)
  | .ExpQuote _ _, .ExpPath _ _ => isFalse (by intro h; cases h)
  | .ExpQuote _ _, .ExpError _ => isFalse (by intro h; cases h)
  | .ExpQuote _ _, .ExpDone _ => isFalse (by intro h; cases h)

  | .ExpError _, .ExpStart _ _ => isFalse (by intro h; cases h)
  | .ExpError _, .ExpExpand _ _ _ => isFalse (by intro h; cases h)
  | .ExpError _, .ExpSplit _ _ => isFalse (by intro h; cases h)
  | .ExpError _, .ExpPath _ _ => isFalse (by intro h; cases h)
  | .ExpError _, .ExpQuote _ _ => isFalse (by intro h; cases h)
  | .ExpError _, .ExpDone _ => isFalse (by intro h; cases h)

  | .ExpDone _, .ExpStart _ _ => isFalse (by intro h; cases h)
  | .ExpDone _, .ExpExpand _ _ _ => isFalse (by intro h; cases h)
  | .ExpDone _, .ExpSplit _ _ => isFalse (by intro h; cases h)
  | .ExpDone _, .ExpPath _ _ => isFalse (by intro h; cases h)
  | .ExpDone _, .ExpQuote _ _ => isFalse (by intro h; cases h)
  | .ExpDone _, .ExpError _ => isFalse (by intro h; cases h)
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by repeat' (simp_wf; omega)

  private def decEqParseResult : (a b : parse_result) → Decidable (a = b)
  | .ParseDone, .ParseDone =>
      isTrue rfl
  | .ParseError m1, .ParseError m2 =>
      match (inferInstance : Decidable (m1 = m2)) with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .ParseNull, .ParseNull =>
      isTrue rfl
  | .ParseStmt st1, .ParseStmt st2 =>
      match decEqStmt st1 st2 with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)

  | .ParseDone, .ParseError _ => isFalse (by intro h; cases h)
  | .ParseDone, .ParseNull => isFalse (by intro h; cases h)
  | .ParseDone, .ParseStmt _ => isFalse (by intro h; cases h)

  | .ParseError _, .ParseDone => isFalse (by intro h; cases h)
  | .ParseError _, .ParseNull => isFalse (by intro h; cases h)
  | .ParseError _, .ParseStmt _ => isFalse (by intro h; cases h)

  | .ParseNull, .ParseDone => isFalse (by intro h; cases h)
  | .ParseNull, .ParseError _ => isFalse (by intro h; cases h)
  | .ParseNull, .ParseStmt _ => isFalse (by intro h; cases h)

  | .ParseStmt _, .ParseDone => isFalse (by intro h; cases h)
  | .ParseStmt _, .ParseError _ => isFalse (by intro h; cases h)
  | .ParseStmt _, .ParseNull => isFalse (by intro h; cases h)
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by repeat' (simp_wf; omega)

  private def decEqExpansionStep : (a b : expansion_step) → Decidable (a = b)
  | .ESTilde s1, .ESTilde s2 =>
      match (inferInstance : Decidable (s1 = s2)) with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .ESParam s1, .ESParam s2 =>
      match (inferInstance : Decidable (s1 = s2)) with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .ESCommand s1, .ESCommand s2 =>
      match (inferInstance : Decidable (s1 = s2)) with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .ESArith s1, .ESArith s2 =>
      match (inferInstance : Decidable (s1 = s2)) with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .ESSplit s1, .ESSplit s2 =>
      match (inferInstance : Decidable (s1 = s2)) with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .ESPath s1, .ESPath s2 =>
      match (inferInstance : Decidable (s1 = s2)) with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .ESQuote s1, .ESQuote s2 =>
      match (inferInstance : Decidable (s1 = s2)) with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .ESEscape s1, .ESEscape s2 =>
      match (inferInstance : Decidable (s1 = s2)) with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .ESStep s1, .ESStep s2 =>
      match (inferInstance : Decidable (s1 = s2)) with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .ESNested a1 b1, .ESNested a2 b2 =>
      match decEqExpansionStep a1 a2, decEqExpansionStep b1 b2 with
      | isTrue h1, isTrue h2 =>
          isTrue (by cases h1; cases h2; rfl)
      | isFalse h, _ =>
          isFalse (by intro h'; cases h'; exact h rfl)
      | _, isFalse h =>
          isFalse (by intro h'; cases h'; exact h rfl)
  | .ESEval es1 xs1, .ESEval es2 xs2 =>
      match decEqExpansionStep es1 es2, decEqEvaluationStep xs1 xs2 with
      | isTrue h1, isTrue h2 =>
          isTrue (by cases h1; cases h2; rfl)
      | isFalse h, _ =>
          isFalse (by intro h'; cases h'; exact h rfl)
      | _, isFalse h =>
          isFalse (by intro h'; cases h'; exact h rfl)

  | .ESTilde _, .ESParam _ => isFalse (by intro h; cases h)
  | .ESTilde _, .ESCommand _ => isFalse (by intro h; cases h)
  | .ESTilde _, .ESArith _ => isFalse (by intro h; cases h)
  | .ESTilde _, .ESSplit _ => isFalse (by intro h; cases h)
  | .ESTilde _, .ESPath _ => isFalse (by intro h; cases h)
  | .ESTilde _, .ESQuote _ => isFalse (by intro h; cases h)
  | .ESTilde _, .ESEscape _ => isFalse (by intro h; cases h)
  | .ESTilde _, .ESStep _ => isFalse (by intro h; cases h)
  | .ESTilde _, .ESNested _ _ => isFalse (by intro h; cases h)
  | .ESTilde _, .ESEval _ _ => isFalse (by intro h; cases h)

  | .ESParam _, .ESTilde _ => isFalse (by intro h; cases h)
  | .ESParam _, .ESCommand _ => isFalse (by intro h; cases h)
  | .ESParam _, .ESArith _ => isFalse (by intro h; cases h)
  | .ESParam _, .ESSplit _ => isFalse (by intro h; cases h)
  | .ESParam _, .ESPath _ => isFalse (by intro h; cases h)
  | .ESParam _, .ESQuote _ => isFalse (by intro h; cases h)
  | .ESParam _, .ESEscape _ => isFalse (by intro h; cases h)
  | .ESParam _, .ESStep _ => isFalse (by intro h; cases h)
  | .ESParam _, .ESNested _ _ => isFalse (by intro h; cases h)
  | .ESParam _, .ESEval _ _ => isFalse (by intro h; cases h)

  | .ESCommand _, .ESTilde _ => isFalse (by intro h; cases h)
  | .ESCommand _, .ESParam _ => isFalse (by intro h; cases h)
  | .ESCommand _, .ESArith _ => isFalse (by intro h; cases h)
  | .ESCommand _, .ESSplit _ => isFalse (by intro h; cases h)
  | .ESCommand _, .ESPath _ => isFalse (by intro h; cases h)
  | .ESCommand _, .ESQuote _ => isFalse (by intro h; cases h)
  | .ESCommand _, .ESEscape _ => isFalse (by intro h; cases h)
  | .ESCommand _, .ESStep _ => isFalse (by intro h; cases h)
  | .ESCommand _, .ESNested _ _ => isFalse (by intro h; cases h)
  | .ESCommand _, .ESEval _ _ => isFalse (by intro h; cases h)

  | .ESArith _, .ESTilde _ => isFalse (by intro h; cases h)
  | .ESArith _, .ESParam _ => isFalse (by intro h; cases h)
  | .ESArith _, .ESCommand _ => isFalse (by intro h; cases h)
  | .ESArith _, .ESSplit _ => isFalse (by intro h; cases h)
  | .ESArith _, .ESPath _ => isFalse (by intro h; cases h)
  | .ESArith _, .ESQuote _ => isFalse (by intro h; cases h)
  | .ESArith _, .ESEscape _ => isFalse (by intro h; cases h)
  | .ESArith _, .ESStep _ => isFalse (by intro h; cases h)
  | .ESArith _, .ESNested _ _ => isFalse (by intro h; cases h)
  | .ESArith _, .ESEval _ _ => isFalse (by intro h; cases h)

  | .ESSplit _, .ESTilde _ => isFalse (by intro h; cases h)
  | .ESSplit _, .ESParam _ => isFalse (by intro h; cases h)
  | .ESSplit _, .ESCommand _ => isFalse (by intro h; cases h)
  | .ESSplit _, .ESArith _ => isFalse (by intro h; cases h)
  | .ESSplit _, .ESPath _ => isFalse (by intro h; cases h)
  | .ESSplit _, .ESQuote _ => isFalse (by intro h; cases h)
  | .ESSplit _, .ESEscape _ => isFalse (by intro h; cases h)
  | .ESSplit _, .ESStep _ => isFalse (by intro h; cases h)
  | .ESSplit _, .ESNested _ _ => isFalse (by intro h; cases h)
  | .ESSplit _, .ESEval _ _ => isFalse (by intro h; cases h)

  | .ESPath _, .ESTilde _ => isFalse (by intro h; cases h)
  | .ESPath _, .ESParam _ => isFalse (by intro h; cases h)
  | .ESPath _, .ESCommand _ => isFalse (by intro h; cases h)
  | .ESPath _, .ESArith _ => isFalse (by intro h; cases h)
  | .ESPath _, .ESSplit _ => isFalse (by intro h; cases h)
  | .ESPath _, .ESQuote _ => isFalse (by intro h; cases h)
  | .ESPath _, .ESEscape _ => isFalse (by intro h; cases h)
  | .ESPath _, .ESStep _ => isFalse (by intro h; cases h)
  | .ESPath _, .ESNested _ _ => isFalse (by intro h; cases h)
  | .ESPath _, .ESEval _ _ => isFalse (by intro h; cases h)

  | .ESQuote _, .ESTilde _ => isFalse (by intro h; cases h)
  | .ESQuote _, .ESParam _ => isFalse (by intro h; cases h)
  | .ESQuote _, .ESCommand _ => isFalse (by intro h; cases h)
  | .ESQuote _, .ESArith _ => isFalse (by intro h; cases h)
  | .ESQuote _, .ESSplit _ => isFalse (by intro h; cases h)
  | .ESQuote _, .ESPath _ => isFalse (by intro h; cases h)
  | .ESQuote _, .ESEscape _ => isFalse (by intro h; cases h)
  | .ESQuote _, .ESStep _ => isFalse (by intro h; cases h)
  | .ESQuote _, .ESNested _ _ => isFalse (by intro h; cases h)
  | .ESQuote _, .ESEval _ _ => isFalse (by intro h; cases h)

  | .ESEscape _, .ESTilde _ => isFalse (by intro h; cases h)
  | .ESEscape _, .ESParam _ => isFalse (by intro h; cases h)
  | .ESEscape _, .ESCommand _ => isFalse (by intro h; cases h)
  | .ESEscape _, .ESArith _ => isFalse (by intro h; cases h)
  | .ESEscape _, .ESSplit _ => isFalse (by intro h; cases h)
  | .ESEscape _, .ESPath _ => isFalse (by intro h; cases h)
  | .ESEscape _, .ESQuote _ => isFalse (by intro h; cases h)
  | .ESEscape _, .ESStep _ => isFalse (by intro h; cases h)
  | .ESEscape _, .ESNested _ _ => isFalse (by intro h; cases h)
  | .ESEscape _, .ESEval _ _ => isFalse (by intro h; cases h)

  | .ESStep _, .ESTilde _ => isFalse (by intro h; cases h)
  | .ESStep _, .ESParam _ => isFalse (by intro h; cases h)
  | .ESStep _, .ESCommand _ => isFalse (by intro h; cases h)
  | .ESStep _, .ESArith _ => isFalse (by intro h; cases h)
  | .ESStep _, .ESSplit _ => isFalse (by intro h; cases h)
  | .ESStep _, .ESPath _ => isFalse (by intro h; cases h)
  | .ESStep _, .ESQuote _ => isFalse (by intro h; cases h)
  | .ESStep _, .ESEscape _ => isFalse (by intro h; cases h)
  | .ESStep _, .ESNested _ _ => isFalse (by intro h; cases h)
  | .ESStep _, .ESEval _ _ => isFalse (by intro h; cases h)

  | .ESNested _ _, .ESTilde _ => isFalse (by intro h; cases h)
  | .ESNested _ _, .ESParam _ => isFalse (by intro h; cases h)
  | .ESNested _ _, .ESCommand _ => isFalse (by intro h; cases h)
  | .ESNested _ _, .ESArith _ => isFalse (by intro h; cases h)
  | .ESNested _ _, .ESSplit _ => isFalse (by intro h; cases h)
  | .ESNested _ _, .ESPath _ => isFalse (by intro h; cases h)
  | .ESNested _ _, .ESQuote _ => isFalse (by intro h; cases h)
  | .ESNested _ _, .ESEscape _ => isFalse (by intro h; cases h)
  | .ESNested _ _, .ESStep _ => isFalse (by intro h; cases h)
  | .ESNested _ _, .ESEval _ _ => isFalse (by intro h; cases h)

  | .ESEval _ _, .ESTilde _ => isFalse (by intro h; cases h)
  | .ESEval _ _, .ESParam _ => isFalse (by intro h; cases h)
  | .ESEval _ _, .ESCommand _ => isFalse (by intro h; cases h)
  | .ESEval _ _, .ESArith _ => isFalse (by intro h; cases h)
  | .ESEval _ _, .ESSplit _ => isFalse (by intro h; cases h)
  | .ESEval _ _, .ESPath _ => isFalse (by intro h; cases h)
  | .ESEval _ _, .ESQuote _ => isFalse (by intro h; cases h)
  | .ESEval _ _, .ESEscape _ => isFalse (by intro h; cases h)
  | .ESEval _ _, .ESStep _ => isFalse (by intro h; cases h)
  | .ESEval _ _, .ESNested _ _ => isFalse (by intro h; cases h)
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by repeat' (simp_wf; omega)

  private def decEqEvaluationStep : (a b : evaluation_step) → Decidable (a = b)
  | .XSSimple s1, .XSSimple s2 =>
      match (inferInstance : Decidable (s1 = s2)) with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .XSPipe s1, .XSPipe s2 =>
      match (inferInstance : Decidable (s1 = s2)) with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .XSRedir s1, .XSRedir s2 =>
      match (inferInstance : Decidable (s1 = s2)) with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .XSBackground s1, .XSBackground s2 =>
      match (inferInstance : Decidable (s1 = s2)) with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .XSSubshell s1, .XSSubshell s2 =>
      match (inferInstance : Decidable (s1 = s2)) with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .XSAnd s1, .XSAnd s2 =>
      match (inferInstance : Decidable (s1 = s2)) with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .XSOr s1, .XSOr s2 =>
      match (inferInstance : Decidable (s1 = s2)) with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .XSNot s1, .XSNot s2 =>
      match (inferInstance : Decidable (s1 = s2)) with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .XSSemi s1, .XSSemi s2 =>
      match (inferInstance : Decidable (s1 = s2)) with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .XSIf s1, .XSIf s2 =>
      match (inferInstance : Decidable (s1 = s2)) with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .XSWhile s1, .XSWhile s2 =>
      match (inferInstance : Decidable (s1 = s2)) with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .XSFor s1, .XSFor s2 =>
      match (inferInstance : Decidable (s1 = s2)) with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .XSCase s1, .XSCase s2 =>
      match (inferInstance : Decidable (s1 = s2)) with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .XSDefun s1, .XSDefun s2 =>
      match (inferInstance : Decidable (s1 = s2)) with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .XSStack f1 st1, .XSStack f2 st2 =>
      match (inferInstance : Decidable (f1 = f2)), decEqEvaluationStep st1 st2 with
      | isTrue h1, isTrue h2 => isTrue (by cases h1; cases h2; rfl)
      | isFalse h, _ => isFalse (by intro h'; cases h'; exact h rfl)
      | _, isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .XSStep s1, .XSStep s2 =>
      match (inferInstance : Decidable (s1 = s2)) with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .XSExec s1, .XSExec s2 =>
      match (inferInstance : Decidable (s1 = s2)) with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .XSEval n1 src1 s1, .XSEval n2 src2 s2 =>
      match (inferInstance : Decidable (n1 = n2)),
            (inferInstance : Decidable (src1 = src2)),
            (inferInstance : Decidable (s1 = s2)) with
      | isTrue h1, isTrue h2, isTrue h3 =>
          isTrue (by cases h1; cases h2; cases h3; rfl)
      | isFalse h, _, _ =>
          isFalse (by intro h'; cases h'; exact h rfl)
      | _, isFalse h, _ =>
          isFalse (by intro h'; cases h'; exact h rfl)
      | _, _, isFalse h =>
          isFalse (by intro h'; cases h'; exact h rfl)
  | .XSWait s1, .XSWait s2 =>
      match (inferInstance : Decidable (s1 = s2)) with
      | isTrue h  => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .XSTrap sig1 s1, .XSTrap sig2 s2 =>
      match (inferInstance : Decidable (sig1 = sig2)),
            (inferInstance : Decidable (s1 = s2)) with
      | isTrue h1, isTrue h2 => isTrue (by cases h1; cases h2; rfl)
      | isFalse h, _ => isFalse (by intro h'; cases h'; exact h rfl)
      | _, isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .XSProc p1 st1, .XSProc p2 st2 =>
      match (inferInstance : Decidable (p1 = p2)), decEqStmt st1 st2 with
      | isTrue h1, isTrue h2 => isTrue (by cases h1; cases h2; rfl)
      | isFalse h, _ => isFalse (by intro h'; cases h'; exact h rfl)
      | _, isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .XSNested a1 b1, .XSNested a2 b2 =>
      match decEqEvaluationStep a1 a2, decEqEvaluationStep b1 b2 with
      | isTrue h1, isTrue h2 => isTrue (by cases h1; cases h2; rfl)
      | isFalse h, _ => isFalse (by intro h'; cases h'; exact h rfl)
      | _, isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .XSExpand ev1 ex1, .XSExpand ev2 ex2 =>
    match decEqEvaluationStep ex1 ex2, decEqExpansionStep ev1 ev2 with
      | isTrue h1, isTrue h2 =>
          isTrue (by cases h1; cases h2; rfl)
      | isFalse h, _ =>
          isFalse (by intro h'; cases h'; exact h rfl)
      | _, isFalse h =>
          isFalse (by intro h'; cases h'; exact h rfl)

  | .XSSimple _, .XSPipe _ => isFalse (by intro h; cases h)
  | .XSSimple _, .XSRedir _ => isFalse (by intro h; cases h)
  | .XSSimple _, .XSBackground _ => isFalse (by intro h; cases h)
  | .XSSimple _, .XSSubshell _ => isFalse (by intro h; cases h)
  | .XSSimple _, .XSAnd _ => isFalse (by intro h; cases h)
  | .XSSimple _, .XSOr _ => isFalse (by intro h; cases h)
  | .XSSimple _, .XSNot _ => isFalse (by intro h; cases h)
  | .XSSimple _, .XSSemi _ => isFalse (by intro h; cases h)
  | .XSSimple _, .XSIf _ => isFalse (by intro h; cases h)
  | .XSSimple _, .XSWhile _ => isFalse (by intro h; cases h)
  | .XSSimple _, .XSFor _ => isFalse (by intro h; cases h)
  | .XSSimple _, .XSCase _ => isFalse (by intro h; cases h)
  | .XSSimple _, .XSDefun _ => isFalse (by intro h; cases h)
  | .XSSimple _, .XSStack _ _ => isFalse (by intro h; cases h)
  | .XSSimple _, .XSStep _ => isFalse (by intro h; cases h)
  | .XSSimple _, .XSExec _ => isFalse (by intro h; cases h)
  | .XSSimple _, .XSEval _ _ _ => isFalse (by intro h; cases h)
  | .XSSimple _, .XSWait _ => isFalse (by intro h; cases h)
  | .XSSimple _, .XSTrap _ _ => isFalse (by intro h; cases h)
  | .XSSimple _, .XSProc _ _ => isFalse (by intro h; cases h)
  | .XSSimple _, .XSNested _ _ => isFalse (by intro h; cases h)
  | .XSSimple _, .XSExpand _ _ => isFalse (by intro h; cases h)

  | .XSPipe _, .XSSimple _ => isFalse (by intro h; cases h)
  | .XSPipe _, .XSRedir _ => isFalse (by intro h; cases h)
  | .XSPipe _, .XSBackground _ => isFalse (by intro h; cases h)
  | .XSPipe _, .XSSubshell _ => isFalse (by intro h; cases h)
  | .XSPipe _, .XSAnd _ => isFalse (by intro h; cases h)
  | .XSPipe _, .XSOr _ => isFalse (by intro h; cases h)
  | .XSPipe _, .XSNot _ => isFalse (by intro h; cases h)
  | .XSPipe _, .XSSemi _ => isFalse (by intro h; cases h)
  | .XSPipe _, .XSIf _ => isFalse (by intro h; cases h)
  | .XSPipe _, .XSWhile _ => isFalse (by intro h; cases h)
  | .XSPipe _, .XSFor _ => isFalse (by intro h; cases h)
  | .XSPipe _, .XSCase _ => isFalse (by intro h; cases h)
  | .XSPipe _, .XSDefun _ => isFalse (by intro h; cases h)
  | .XSPipe _, .XSStack _ _ => isFalse (by intro h; cases h)
  | .XSPipe _, .XSStep _ => isFalse (by intro h; cases h)
  | .XSPipe _, .XSExec _ => isFalse (by intro h; cases h)
  | .XSPipe _, .XSEval _ _ _ => isFalse (by intro h; cases h)
  | .XSPipe _, .XSWait _ => isFalse (by intro h; cases h)
  | .XSPipe _, .XSTrap _ _ => isFalse (by intro h; cases h)
  | .XSPipe _, .XSProc _ _ => isFalse (by intro h; cases h)
  | .XSPipe _, .XSNested _ _ => isFalse (by intro h; cases h)
  | .XSPipe _, .XSExpand _ _ => isFalse (by intro h; cases h)

  | .XSRedir _, .XSSimple _ => isFalse (by intro h; cases h)
  | .XSRedir _, .XSPipe _ => isFalse (by intro h; cases h)
  | .XSRedir _, .XSBackground _ => isFalse (by intro h; cases h)
  | .XSRedir _, .XSSubshell _ => isFalse (by intro h; cases h)
  | .XSRedir _, .XSAnd _ => isFalse (by intro h; cases h)
  | .XSRedir _, .XSOr _ => isFalse (by intro h; cases h)
  | .XSRedir _, .XSNot _ => isFalse (by intro h; cases h)
  | .XSRedir _, .XSSemi _ => isFalse (by intro h; cases h)
  | .XSRedir _, .XSIf _ => isFalse (by intro h; cases h)
  | .XSRedir _, .XSWhile _ => isFalse (by intro h; cases h)
  | .XSRedir _, .XSFor _ => isFalse (by intro h; cases h)
  | .XSRedir _, .XSCase _ => isFalse (by intro h; cases h)
  | .XSRedir _, .XSDefun _ => isFalse (by intro h; cases h)
  | .XSRedir _, .XSStack _ _ => isFalse (by intro h; cases h)
  | .XSRedir _, .XSStep _ => isFalse (by intro h; cases h)
  | .XSRedir _, .XSExec _ => isFalse (by intro h; cases h)
  | .XSRedir _, .XSEval _ _ _ => isFalse (by intro h; cases h)
  | .XSRedir _, .XSWait _ => isFalse (by intro h; cases h)
  | .XSRedir _, .XSTrap _ _ => isFalse (by intro h; cases h)
  | .XSRedir _, .XSProc _ _ => isFalse (by intro h; cases h)
  | .XSRedir _, .XSNested _ _ => isFalse (by intro h; cases h)
  | .XSRedir _, .XSExpand _ _ => isFalse (by intro h; cases h)

  | .XSBackground _, .XSSimple _ => isFalse (by intro h; cases h)
  | .XSBackground _, .XSPipe _ => isFalse (by intro h; cases h)
  | .XSBackground _, .XSRedir _ => isFalse (by intro h; cases h)
  | .XSBackground _, .XSSubshell _ => isFalse (by intro h; cases h)
  | .XSBackground _, .XSAnd _ => isFalse (by intro h; cases h)
  | .XSBackground _, .XSOr _ => isFalse (by intro h; cases h)
  | .XSBackground _, .XSNot _ => isFalse (by intro h; cases h)
  | .XSBackground _, .XSSemi _ => isFalse (by intro h; cases h)
  | .XSBackground _, .XSIf _ => isFalse (by intro h; cases h)
  | .XSBackground _, .XSWhile _ => isFalse (by intro h; cases h)
  | .XSBackground _, .XSFor _ => isFalse (by intro h; cases h)
  | .XSBackground _, .XSCase _ => isFalse (by intro h; cases h)
  | .XSBackground _, .XSDefun _ => isFalse (by intro h; cases h)
  | .XSBackground _, .XSStack _ _ => isFalse (by intro h; cases h)
  | .XSBackground _, .XSStep _ => isFalse (by intro h; cases h)
  | .XSBackground _, .XSExec _ => isFalse (by intro h; cases h)
  | .XSBackground _, .XSEval _ _ _ => isFalse (by intro h; cases h)
  | .XSBackground _, .XSWait _ => isFalse (by intro h; cases h)
  | .XSBackground _, .XSTrap _ _ => isFalse (by intro h; cases h)
  | .XSBackground _, .XSProc _ _ => isFalse (by intro h; cases h)
  | .XSBackground _, .XSNested _ _ => isFalse (by intro h; cases h)
  | .XSBackground _, .XSExpand _ _ => isFalse (by intro h; cases h)

  | .XSSubshell _, .XSSimple _ => isFalse (by intro h; cases h)
  | .XSSubshell _, .XSPipe _ => isFalse (by intro h; cases h)
  | .XSSubshell _, .XSRedir _ => isFalse (by intro h; cases h)
  | .XSSubshell _, .XSBackground _ => isFalse (by intro h; cases h)
  | .XSSubshell _, .XSAnd _ => isFalse (by intro h; cases h)
  | .XSSubshell _, .XSOr _ => isFalse (by intro h; cases h)
  | .XSSubshell _, .XSNot _ => isFalse (by intro h; cases h)
  | .XSSubshell _, .XSSemi _ => isFalse (by intro h; cases h)
  | .XSSubshell _, .XSIf _ => isFalse (by intro h; cases h)
  | .XSSubshell _, .XSWhile _ => isFalse (by intro h; cases h)
  | .XSSubshell _, .XSFor _ => isFalse (by intro h; cases h)
  | .XSSubshell _, .XSCase _ => isFalse (by intro h; cases h)
  | .XSSubshell _, .XSDefun _ => isFalse (by intro h; cases h)
  | .XSSubshell _, .XSStack _ _ => isFalse (by intro h; cases h)
  | .XSSubshell _, .XSStep _ => isFalse (by intro h; cases h)
  | .XSSubshell _, .XSExec _ => isFalse (by intro h; cases h)
  | .XSSubshell _, .XSEval _ _ _ => isFalse (by intro h; cases h)
  | .XSSubshell _, .XSWait _ => isFalse (by intro h; cases h)
  | .XSSubshell _, .XSTrap _ _ => isFalse (by intro h; cases h)
  | .XSSubshell _, .XSProc _ _ => isFalse (by intro h; cases h)
  | .XSSubshell _, .XSNested _ _ => isFalse (by intro h; cases h)
  | .XSSubshell _, .XSExpand _ _ => isFalse (by intro h; cases h)

  | .XSAnd _, .XSSimple _ => isFalse (by intro h; cases h)
  | .XSAnd _, .XSPipe _ => isFalse (by intro h; cases h)
  | .XSAnd _, .XSRedir _ => isFalse (by intro h; cases h)
  | .XSAnd _, .XSBackground _ => isFalse (by intro h; cases h)
  | .XSAnd _, .XSSubshell _ => isFalse (by intro h; cases h)
  | .XSAnd _, .XSOr _ => isFalse (by intro h; cases h)
  | .XSAnd _, .XSNot _ => isFalse (by intro h; cases h)
  | .XSAnd _, .XSSemi _ => isFalse (by intro h; cases h)
  | .XSAnd _, .XSIf _ => isFalse (by intro h; cases h)
  | .XSAnd _, .XSWhile _ => isFalse (by intro h; cases h)
  | .XSAnd _, .XSFor _ => isFalse (by intro h; cases h)
  | .XSAnd _, .XSCase _ => isFalse (by intro h; cases h)
  | .XSAnd _, .XSDefun _ => isFalse (by intro h; cases h)
  | .XSAnd _, .XSStack _ _ => isFalse (by intro h; cases h)
  | .XSAnd _, .XSStep _ => isFalse (by intro h; cases h)
  | .XSAnd _, .XSExec _ => isFalse (by intro h; cases h)
  | .XSAnd _, .XSEval _ _ _ => isFalse (by intro h; cases h)
  | .XSAnd _, .XSWait _ => isFalse (by intro h; cases h)
  | .XSAnd _, .XSTrap _ _ => isFalse (by intro h; cases h)
  | .XSAnd _, .XSProc _ _ => isFalse (by intro h; cases h)
  | .XSAnd _, .XSNested _ _ => isFalse (by intro h; cases h)
  | .XSAnd _, .XSExpand _ _ => isFalse (by intro h; cases h)

  | .XSOr _, .XSSimple _ => isFalse (by intro h; cases h)
  | .XSOr _, .XSPipe _ => isFalse (by intro h; cases h)
  | .XSOr _, .XSRedir _ => isFalse (by intro h; cases h)
  | .XSOr _, .XSBackground _ => isFalse (by intro h; cases h)
  | .XSOr _, .XSSubshell _ => isFalse (by intro h; cases h)
  | .XSOr _, .XSAnd _ => isFalse (by intro h; cases h)
  | .XSOr _, .XSNot _ => isFalse (by intro h; cases h)
  | .XSOr _, .XSSemi _ => isFalse (by intro h; cases h)
  | .XSOr _, .XSIf _ => isFalse (by intro h; cases h)
  | .XSOr _, .XSWhile _ => isFalse (by intro h; cases h)
  | .XSOr _, .XSFor _ => isFalse (by intro h; cases h)
  | .XSOr _, .XSCase _ => isFalse (by intro h; cases h)
  | .XSOr _, .XSDefun _ => isFalse (by intro h; cases h)
  | .XSOr _, .XSStack _ _ => isFalse (by intro h; cases h)
  | .XSOr _, .XSStep _ => isFalse (by intro h; cases h)
  | .XSOr _, .XSExec _ => isFalse (by intro h; cases h)
  | .XSOr _, .XSEval _ _ _ => isFalse (by intro h; cases h)
  | .XSOr _, .XSWait _ => isFalse (by intro h; cases h)
  | .XSOr _, .XSTrap _ _ => isFalse (by intro h; cases h)
  | .XSOr _, .XSProc _ _ => isFalse (by intro h; cases h)
  | .XSOr _, .XSNested _ _ => isFalse (by intro h; cases h)
  | .XSOr _, .XSExpand _ _ => isFalse (by intro h; cases h)

  | .XSNot _, .XSSimple _ => isFalse (by intro h; cases h)
  | .XSNot _, .XSPipe _ => isFalse (by intro h; cases h)
  | .XSNot _, .XSRedir _ => isFalse (by intro h; cases h)
  | .XSNot _, .XSBackground _ => isFalse (by intro h; cases h)
  | .XSNot _, .XSSubshell _ => isFalse (by intro h; cases h)
  | .XSNot _, .XSAnd _ => isFalse (by intro h; cases h)
  | .XSNot _, .XSOr _ => isFalse (by intro h; cases h)
  | .XSNot _, .XSSemi _ => isFalse (by intro h; cases h)
  | .XSNot _, .XSIf _ => isFalse (by intro h; cases h)
  | .XSNot _, .XSWhile _ => isFalse (by intro h; cases h)
  | .XSNot _, .XSFor _ => isFalse (by intro h; cases h)
  | .XSNot _, .XSCase _ => isFalse (by intro h; cases h)
  | .XSNot _, .XSDefun _ => isFalse (by intro h; cases h)
  | .XSNot _, .XSStack _ _ => isFalse (by intro h; cases h)
  | .XSNot _, .XSStep _ => isFalse (by intro h; cases h)
  | .XSNot _, .XSExec _ => isFalse (by intro h; cases h)
  | .XSNot _, .XSEval _ _ _ => isFalse (by intro h; cases h)
  | .XSNot _, .XSWait _ => isFalse (by intro h; cases h)
  | .XSNot _, .XSTrap _ _ => isFalse (by intro h; cases h)
  | .XSNot _, .XSProc _ _ => isFalse (by intro h; cases h)
  | .XSNot _, .XSNested _ _ => isFalse (by intro h; cases h)
  | .XSNot _, .XSExpand _ _ => isFalse (by intro h; cases h)

  | .XSSemi _, .XSSimple _ => isFalse (by intro h; cases h)
  | .XSSemi _, .XSPipe _ => isFalse (by intro h; cases h)
  | .XSSemi _, .XSRedir _ => isFalse (by intro h; cases h)
  | .XSSemi _, .XSBackground _ => isFalse (by intro h; cases h)
  | .XSSemi _, .XSSubshell _ => isFalse (by intro h; cases h)
  | .XSSemi _, .XSAnd _ => isFalse (by intro h; cases h)
  | .XSSemi _, .XSOr _ => isFalse (by intro h; cases h)
  | .XSSemi _, .XSNot _ => isFalse (by intro h; cases h)
  | .XSSemi _, .XSIf _ => isFalse (by intro h; cases h)
  | .XSSemi _, .XSWhile _ => isFalse (by intro h; cases h)
  | .XSSemi _, .XSFor _ => isFalse (by intro h; cases h)
  | .XSSemi _, .XSCase _ => isFalse (by intro h; cases h)
  | .XSSemi _, .XSDefun _ => isFalse (by intro h; cases h)
  | .XSSemi _, .XSStack _ _ => isFalse (by intro h; cases h)
  | .XSSemi _, .XSStep _ => isFalse (by intro h; cases h)
  | .XSSemi _, .XSExec _ => isFalse (by intro h; cases h)
  | .XSSemi _, .XSEval _ _ _ => isFalse (by intro h; cases h)
  | .XSSemi _, .XSWait _ => isFalse (by intro h; cases h)
  | .XSSemi _, .XSTrap _ _ => isFalse (by intro h; cases h)
  | .XSSemi _, .XSProc _ _ => isFalse (by intro h; cases h)
  | .XSSemi _, .XSNested _ _ => isFalse (by intro h; cases h)
  | .XSSemi _, .XSExpand _ _ => isFalse (by intro h; cases h)

  | .XSIf _, .XSSimple _ => isFalse (by intro h; cases h)
  | .XSIf _, .XSPipe _ => isFalse (by intro h; cases h)
  | .XSIf _, .XSRedir _ => isFalse (by intro h; cases h)
  | .XSIf _, .XSBackground _ => isFalse (by intro h; cases h)
  | .XSIf _, .XSSubshell _ => isFalse (by intro h; cases h)
  | .XSIf _, .XSAnd _ => isFalse (by intro h; cases h)
  | .XSIf _, .XSOr _ => isFalse (by intro h; cases h)
  | .XSIf _, .XSNot _ => isFalse (by intro h; cases h)
  | .XSIf _, .XSSemi _ => isFalse (by intro h; cases h)
  | .XSIf _, .XSWhile _ => isFalse (by intro h; cases h)
  | .XSIf _, .XSFor _ => isFalse (by intro h; cases h)
  | .XSIf _, .XSCase _ => isFalse (by intro h; cases h)
  | .XSIf _, .XSDefun _ => isFalse (by intro h; cases h)
  | .XSIf _, .XSStack _ _ => isFalse (by intro h; cases h)
  | .XSIf _, .XSStep _ => isFalse (by intro h; cases h)
  | .XSIf _, .XSExec _ => isFalse (by intro h; cases h)
  | .XSIf _, .XSEval _ _ _ => isFalse (by intro h; cases h)
  | .XSIf _, .XSWait _ => isFalse (by intro h; cases h)
  | .XSIf _, .XSTrap _ _ => isFalse (by intro h; cases h)
  | .XSIf _, .XSProc _ _ => isFalse (by intro h; cases h)
  | .XSIf _, .XSNested _ _ => isFalse (by intro h; cases h)
  | .XSIf _, .XSExpand _ _ => isFalse (by intro h; cases h)

  | .XSWhile _, .XSSimple _ => isFalse (by intro h; cases h)
  | .XSWhile _, .XSPipe _ => isFalse (by intro h; cases h)
  | .XSWhile _, .XSRedir _ => isFalse (by intro h; cases h)
  | .XSWhile _, .XSBackground _ => isFalse (by intro h; cases h)
  | .XSWhile _, .XSSubshell _ => isFalse (by intro h; cases h)
  | .XSWhile _, .XSAnd _ => isFalse (by intro h; cases h)
  | .XSWhile _, .XSOr _ => isFalse (by intro h; cases h)
  | .XSWhile _, .XSNot _ => isFalse (by intro h; cases h)
  | .XSWhile _, .XSSemi _ => isFalse (by intro h; cases h)
  | .XSWhile _, .XSIf _ => isFalse (by intro h; cases h)
  | .XSWhile _, .XSFor _ => isFalse (by intro h; cases h)
  | .XSWhile _, .XSCase _ => isFalse (by intro h; cases h)
  | .XSWhile _, .XSDefun _ => isFalse (by intro h; cases h)
  | .XSWhile _, .XSStack _ _ => isFalse (by intro h; cases h)
  | .XSWhile _, .XSStep _ => isFalse (by intro h; cases h)
  | .XSWhile _, .XSExec _ => isFalse (by intro h; cases h)
  | .XSWhile _, .XSEval _ _ _ => isFalse (by intro h; cases h)
  | .XSWhile _, .XSWait _ => isFalse (by intro h; cases h)
  | .XSWhile _, .XSTrap _ _ => isFalse (by intro h; cases h)
  | .XSWhile _, .XSProc _ _ => isFalse (by intro h; cases h)
  | .XSWhile _, .XSNested _ _ => isFalse (by intro h; cases h)
  | .XSWhile _, .XSExpand _ _ => isFalse (by intro h; cases h)

  | .XSFor _, .XSSimple _ => isFalse (by intro h; cases h)
  | .XSFor _, .XSPipe _ => isFalse (by intro h; cases h)
  | .XSFor _, .XSRedir _ => isFalse (by intro h; cases h)
  | .XSFor _, .XSBackground _ => isFalse (by intro h; cases h)
  | .XSFor _, .XSSubshell _ => isFalse (by intro h; cases h)
  | .XSFor _, .XSAnd _ => isFalse (by intro h; cases h)
  | .XSFor _, .XSOr _ => isFalse (by intro h; cases h)
  | .XSFor _, .XSNot _ => isFalse (by intro h; cases h)
  | .XSFor _, .XSSemi _ => isFalse (by intro h; cases h)
  | .XSFor _, .XSIf _ => isFalse (by intro h; cases h)
  | .XSFor _, .XSWhile _ => isFalse (by intro h; cases h)
  | .XSFor _, .XSCase _ => isFalse (by intro h; cases h)
  | .XSFor _, .XSDefun _ => isFalse (by intro h; cases h)
  | .XSFor _, .XSStack _ _ => isFalse (by intro h; cases h)
  | .XSFor _, .XSStep _ => isFalse (by intro h; cases h)
  | .XSFor _, .XSExec _ => isFalse (by intro h; cases h)
  | .XSFor _, .XSEval _ _ _ => isFalse (by intro h; cases h)
  | .XSFor _, .XSWait _ => isFalse (by intro h; cases h)
  | .XSFor _, .XSTrap _ _ => isFalse (by intro h; cases h)
  | .XSFor _, .XSProc _ _ => isFalse (by intro h; cases h)
  | .XSFor _, .XSNested _ _ => isFalse (by intro h; cases h)
  | .XSFor _, .XSExpand _ _ => isFalse (by intro h; cases h)

  | .XSCase _, .XSSimple _ => isFalse (by intro h; cases h)
  | .XSCase _, .XSPipe _ => isFalse (by intro h; cases h)
  | .XSCase _, .XSRedir _ => isFalse (by intro h; cases h)
  | .XSCase _, .XSBackground _ => isFalse (by intro h; cases h)
  | .XSCase _, .XSSubshell _ => isFalse (by intro h; cases h)
  | .XSCase _, .XSAnd _ => isFalse (by intro h; cases h)
  | .XSCase _, .XSOr _ => isFalse (by intro h; cases h)
  | .XSCase _, .XSNot _ => isFalse (by intro h; cases h)
  | .XSCase _, .XSSemi _ => isFalse (by intro h; cases h)
  | .XSCase _, .XSIf _ => isFalse (by intro h; cases h)
  | .XSCase _, .XSWhile _ => isFalse (by intro h; cases h)
  | .XSCase _, .XSFor _ => isFalse (by intro h; cases h)
  | .XSCase _, .XSDefun _ => isFalse (by intro h; cases h)
  | .XSCase _, .XSStack _ _ => isFalse (by intro h; cases h)
  | .XSCase _, .XSStep _ => isFalse (by intro h; cases h)
  | .XSCase _, .XSExec _ => isFalse (by intro h; cases h)
  | .XSCase _, .XSEval _ _ _ => isFalse (by intro h; cases h)
  | .XSCase _, .XSWait _ => isFalse (by intro h; cases h)
  | .XSCase _, .XSTrap _ _ => isFalse (by intro h; cases h)
  | .XSCase _, .XSProc _ _ => isFalse (by intro h; cases h)
  | .XSCase _, .XSNested _ _ => isFalse (by intro h; cases h)
  | .XSCase _, .XSExpand _ _ => isFalse (by intro h; cases h)

  | .XSDefun _, .XSSimple _ => isFalse (by intro h; cases h)
  | .XSDefun _, .XSPipe _ => isFalse (by intro h; cases h)
  | .XSDefun _, .XSRedir _ => isFalse (by intro h; cases h)
  | .XSDefun _, .XSBackground _ => isFalse (by intro h; cases h)
  | .XSDefun _, .XSSubshell _ => isFalse (by intro h; cases h)
  | .XSDefun _, .XSAnd _ => isFalse (by intro h; cases h)
  | .XSDefun _, .XSOr _ => isFalse (by intro h; cases h)
  | .XSDefun _, .XSNot _ => isFalse (by intro h; cases h)
  | .XSDefun _, .XSSemi _ => isFalse (by intro h; cases h)
  | .XSDefun _, .XSIf _ => isFalse (by intro h; cases h)
  | .XSDefun _, .XSWhile _ => isFalse (by intro h; cases h)
  | .XSDefun _, .XSFor _ => isFalse (by intro h; cases h)
  | .XSDefun _, .XSCase _ => isFalse (by intro h; cases h)
  | .XSDefun _, .XSStack _ _ => isFalse (by intro h; cases h)
  | .XSDefun _, .XSStep _ => isFalse (by intro h; cases h)
  | .XSDefun _, .XSExec _ => isFalse (by intro h; cases h)
  | .XSDefun _, .XSEval _ _ _ => isFalse (by intro h; cases h)
  | .XSDefun _, .XSWait _ => isFalse (by intro h; cases h)
  | .XSDefun _, .XSTrap _ _ => isFalse (by intro h; cases h)
  | .XSDefun _, .XSProc _ _ => isFalse (by intro h; cases h)
  | .XSDefun _, .XSNested _ _ => isFalse (by intro h; cases h)
  | .XSDefun _, .XSExpand _ _ => isFalse (by intro h; cases h)

  | .XSStack _ _, .XSSimple _ => isFalse (by intro h; cases h)
  | .XSStack _ _, .XSPipe _ => isFalse (by intro h; cases h)
  | .XSStack _ _, .XSRedir _ => isFalse (by intro h; cases h)
  | .XSStack _ _, .XSBackground _ => isFalse (by intro h; cases h)
  | .XSStack _ _, .XSSubshell _ => isFalse (by intro h; cases h)
  | .XSStack _ _, .XSAnd _ => isFalse (by intro h; cases h)
  | .XSStack _ _, .XSOr _ => isFalse (by intro h; cases h)
  | .XSStack _ _, .XSNot _ => isFalse (by intro h; cases h)
  | .XSStack _ _, .XSSemi _ => isFalse (by intro h; cases h)
  | .XSStack _ _, .XSIf _ => isFalse (by intro h; cases h)
  | .XSStack _ _, .XSWhile _ => isFalse (by intro h; cases h)
  | .XSStack _ _, .XSFor _ => isFalse (by intro h; cases h)
  | .XSStack _ _, .XSCase _ => isFalse (by intro h; cases h)
  | .XSStack _ _, .XSDefun _ => isFalse (by intro h; cases h)
  | .XSStack _ _, .XSStep _ => isFalse (by intro h; cases h)
  | .XSStack _ _, .XSExec _ => isFalse (by intro h; cases h)
  | .XSStack _ _, .XSEval _ _ _ => isFalse (by intro h; cases h)
  | .XSStack _ _, .XSWait _ => isFalse (by intro h; cases h)
  | .XSStack _ _, .XSTrap _ _ => isFalse (by intro h; cases h)
  | .XSStack _ _, .XSProc _ _ => isFalse (by intro h; cases h)
  | .XSStack _ _, .XSNested _ _ => isFalse (by intro h; cases h)
  | .XSStack _ _, .XSExpand _ _ => isFalse (by intro h; cases h)

  | .XSStep _, .XSSimple _ => isFalse (by intro h; cases h)
  | .XSStep _, .XSPipe _ => isFalse (by intro h; cases h)
  | .XSStep _, .XSRedir _ => isFalse (by intro h; cases h)
  | .XSStep _, .XSBackground _ => isFalse (by intro h; cases h)
  | .XSStep _, .XSSubshell _ => isFalse (by intro h; cases h)
  | .XSStep _, .XSAnd _ => isFalse (by intro h; cases h)
  | .XSStep _, .XSOr _ => isFalse (by intro h; cases h)
  | .XSStep _, .XSNot _ => isFalse (by intro h; cases h)
  | .XSStep _, .XSSemi _ => isFalse (by intro h; cases h)
  | .XSStep _, .XSIf _ => isFalse (by intro h; cases h)
  | .XSStep _, .XSWhile _ => isFalse (by intro h; cases h)
  | .XSStep _, .XSFor _ => isFalse (by intro h; cases h)
  | .XSStep _, .XSCase _ => isFalse (by intro h; cases h)
  | .XSStep _, .XSDefun _ => isFalse (by intro h; cases h)
  | .XSStep _, .XSStack _ _ => isFalse (by intro h; cases h)
  | .XSStep _, .XSExec _ => isFalse (by intro h; cases h)
  | .XSStep _, .XSEval _ _ _ => isFalse (by intro h; cases h)
  | .XSStep _, .XSWait _ => isFalse (by intro h; cases h)
  | .XSStep _, .XSTrap _ _ => isFalse (by intro h; cases h)
  | .XSStep _, .XSProc _ _ => isFalse (by intro h; cases h)
  | .XSStep _, .XSNested _ _ => isFalse (by intro h; cases h)
  | .XSStep _, .XSExpand _ _ => isFalse (by intro h; cases h)

  | .XSExec _, .XSSimple _ => isFalse (by intro h; cases h)
  | .XSExec _, .XSPipe _ => isFalse (by intro h; cases h)
  | .XSExec _, .XSRedir _ => isFalse (by intro h; cases h)
  | .XSExec _, .XSBackground _ => isFalse (by intro h; cases h)
  | .XSExec _, .XSSubshell _ => isFalse (by intro h; cases h)
  | .XSExec _, .XSAnd _ => isFalse (by intro h; cases h)
  | .XSExec _, .XSOr _ => isFalse (by intro h; cases h)
  | .XSExec _, .XSNot _ => isFalse (by intro h; cases h)
  | .XSExec _, .XSSemi _ => isFalse (by intro h; cases h)
  | .XSExec _, .XSIf _ => isFalse (by intro h; cases h)
  | .XSExec _, .XSWhile _ => isFalse (by intro h; cases h)
  | .XSExec _, .XSFor _ => isFalse (by intro h; cases h)
  | .XSExec _, .XSCase _ => isFalse (by intro h; cases h)
  | .XSExec _, .XSDefun _ => isFalse (by intro h; cases h)
  | .XSExec _, .XSStack _ _ => isFalse (by intro h; cases h)
  | .XSExec _, .XSStep _ => isFalse (by intro h; cases h)
  | .XSExec _, .XSEval _ _ _ => isFalse (by intro h; cases h)
  | .XSExec _, .XSWait _ => isFalse (by intro h; cases h)
  | .XSExec _, .XSTrap _ _ => isFalse (by intro h; cases h)
  | .XSExec _, .XSProc _ _ => isFalse (by intro h; cases h)
  | .XSExec _, .XSNested _ _ => isFalse (by intro h; cases h)
  | .XSExec _, .XSExpand _ _ => isFalse (by intro h; cases h)

  | .XSEval _ _ _, .XSSimple _ => isFalse (by intro h; cases h)
  | .XSEval _ _ _, .XSPipe _ => isFalse (by intro h; cases h)
  | .XSEval _ _ _, .XSRedir _ => isFalse (by intro h; cases h)
  | .XSEval _ _ _, .XSBackground _ => isFalse (by intro h; cases h)
  | .XSEval _ _ _, .XSSubshell _ => isFalse (by intro h; cases h)
  | .XSEval _ _ _, .XSAnd _ => isFalse (by intro h; cases h)
  | .XSEval _ _ _, .XSOr _ => isFalse (by intro h; cases h)
  | .XSEval _ _ _, .XSNot _ => isFalse (by intro h; cases h)
  | .XSEval _ _ _, .XSSemi _ => isFalse (by intro h; cases h)
  | .XSEval _ _ _, .XSIf _ => isFalse (by intro h; cases h)
  | .XSEval _ _ _, .XSWhile _ => isFalse (by intro h; cases h)
  | .XSEval _ _ _, .XSFor _ => isFalse (by intro h; cases h)
  | .XSEval _ _ _, .XSCase _ => isFalse (by intro h; cases h)
  | .XSEval _ _ _, .XSDefun _ => isFalse (by intro h; cases h)
  | .XSEval _ _ _, .XSStack _ _ => isFalse (by intro h; cases h)
  | .XSEval _ _ _, .XSStep _ => isFalse (by intro h; cases h)
  | .XSEval _ _ _, .XSExec _ => isFalse (by intro h; cases h)
  | .XSEval _ _ _, .XSWait _ => isFalse (by intro h; cases h)
  | .XSEval _ _ _, .XSTrap _ _ => isFalse (by intro h; cases h)
  | .XSEval _ _ _, .XSProc _ _ => isFalse (by intro h; cases h)
  | .XSEval _ _ _, .XSNested _ _ => isFalse (by intro h; cases h)
  | .XSEval _ _ _, .XSExpand _ _ => isFalse (by intro h; cases h)

  | .XSWait _, .XSSimple _ => isFalse (by intro h; cases h)
  | .XSWait _, .XSPipe _ => isFalse (by intro h; cases h)
  | .XSWait _, .XSRedir _ => isFalse (by intro h; cases h)
  | .XSWait _, .XSBackground _ => isFalse (by intro h; cases h)
  | .XSWait _, .XSSubshell _ => isFalse (by intro h; cases h)
  | .XSWait _, .XSAnd _ => isFalse (by intro h; cases h)
  | .XSWait _, .XSOr _ => isFalse (by intro h; cases h)
  | .XSWait _, .XSNot _ => isFalse (by intro h; cases h)
  | .XSWait _, .XSSemi _ => isFalse (by intro h; cases h)
  | .XSWait _, .XSIf _ => isFalse (by intro h; cases h)
  | .XSWait _, .XSWhile _ => isFalse (by intro h; cases h)
  | .XSWait _, .XSFor _ => isFalse (by intro h; cases h)
  | .XSWait _, .XSCase _ => isFalse (by intro h; cases h)
  | .XSWait _, .XSDefun _ => isFalse (by intro h; cases h)
  | .XSWait _, .XSStack _ _ => isFalse (by intro h; cases h)
  | .XSWait _, .XSStep _ => isFalse (by intro h; cases h)
  | .XSWait _, .XSExec _ => isFalse (by intro h; cases h)
  | .XSWait _, .XSEval _ _ _ => isFalse (by intro h; cases h)
  | .XSWait _, .XSTrap _ _ => isFalse (by intro h; cases h)
  | .XSWait _, .XSProc _ _ => isFalse (by intro h; cases h)
  | .XSWait _, .XSNested _ _ => isFalse (by intro h; cases h)
  | .XSWait _, .XSExpand _ _ => isFalse (by intro h; cases h)

  | .XSTrap _ _, .XSSimple _ => isFalse (by intro h; cases h)
  | .XSTrap _ _, .XSPipe _ => isFalse (by intro h; cases h)
  | .XSTrap _ _, .XSRedir _ => isFalse (by intro h; cases h)
  | .XSTrap _ _, .XSBackground _ => isFalse (by intro h; cases h)
  | .XSTrap _ _, .XSSubshell _ => isFalse (by intro h; cases h)
  | .XSTrap _ _, .XSAnd _ => isFalse (by intro h; cases h)
  | .XSTrap _ _, .XSOr _ => isFalse (by intro h; cases h)
  | .XSTrap _ _, .XSNot _ => isFalse (by intro h; cases h)
  | .XSTrap _ _, .XSSemi _ => isFalse (by intro h; cases h)
  | .XSTrap _ _, .XSIf _ => isFalse (by intro h; cases h)
  | .XSTrap _ _, .XSWhile _ => isFalse (by intro h; cases h)
  | .XSTrap _ _, .XSFor _ => isFalse (by intro h; cases h)
  | .XSTrap _ _, .XSCase _ => isFalse (by intro h; cases h)
  | .XSTrap _ _, .XSDefun _ => isFalse (by intro h; cases h)
  | .XSTrap _ _, .XSStack _ _ => isFalse (by intro h; cases h)
  | .XSTrap _ _, .XSStep _ => isFalse (by intro h; cases h)
  | .XSTrap _ _, .XSExec _ => isFalse (by intro h; cases h)
  | .XSTrap _ _, .XSEval _ _ _ => isFalse (by intro h; cases h)
  | .XSTrap _ _, .XSWait _ => isFalse (by intro h; cases h)
  | .XSTrap _ _, .XSProc _ _ => isFalse (by intro h; cases h)
  | .XSTrap _ _, .XSNested _ _ => isFalse (by intro h; cases h)
  | .XSTrap _ _, .XSExpand _ _ => isFalse (by intro h; cases h)

  | .XSProc _ _, .XSSimple _ => isFalse (by intro h; cases h)
  | .XSProc _ _, .XSPipe _ => isFalse (by intro h; cases h)
  | .XSProc _ _, .XSRedir _ => isFalse (by intro h; cases h)
  | .XSProc _ _, .XSBackground _ => isFalse (by intro h; cases h)
  | .XSProc _ _, .XSSubshell _ => isFalse (by intro h; cases h)
  | .XSProc _ _, .XSAnd _ => isFalse (by intro h; cases h)
  | .XSProc _ _, .XSOr _ => isFalse (by intro h; cases h)
  | .XSProc _ _, .XSNot _ => isFalse (by intro h; cases h)
  | .XSProc _ _, .XSSemi _ => isFalse (by intro h; cases h)
  | .XSProc _ _, .XSIf _ => isFalse (by intro h; cases h)
  | .XSProc _ _, .XSWhile _ => isFalse (by intro h; cases h)
  | .XSProc _ _, .XSFor _ => isFalse (by intro h; cases h)
  | .XSProc _ _, .XSCase _ => isFalse (by intro h; cases h)
  | .XSProc _ _, .XSDefun _ => isFalse (by intro h; cases h)
  | .XSProc _ _, .XSStack _ _ => isFalse (by intro h; cases h)
  | .XSProc _ _, .XSStep _ => isFalse (by intro h; cases h)
  | .XSProc _ _, .XSExec _ => isFalse (by intro h; cases h)
  | .XSProc _ _, .XSEval _ _ _ => isFalse (by intro h; cases h)
  | .XSProc _ _, .XSWait _ => isFalse (by intro h; cases h)
  | .XSProc _ _, .XSTrap _ _ => isFalse (by intro h; cases h)
  | .XSProc _ _, .XSNested _ _ => isFalse (by intro h; cases h)
  | .XSProc _ _, .XSExpand _ _ => isFalse (by intro h; cases h)

  | .XSNested _ _, .XSSimple _ => isFalse (by intro h; cases h)
  | .XSNested _ _, .XSPipe _ => isFalse (by intro h; cases h)
  | .XSNested _ _, .XSRedir _ => isFalse (by intro h; cases h)
  | .XSNested _ _, .XSBackground _ => isFalse (by intro h; cases h)
  | .XSNested _ _, .XSSubshell _ => isFalse (by intro h; cases h)
  | .XSNested _ _, .XSAnd _ => isFalse (by intro h; cases h)
  | .XSNested _ _, .XSOr _ => isFalse (by intro h; cases h)
  | .XSNested _ _, .XSNot _ => isFalse (by intro h; cases h)
  | .XSNested _ _, .XSSemi _ => isFalse (by intro h; cases h)
  | .XSNested _ _, .XSIf _ => isFalse (by intro h; cases h)
  | .XSNested _ _, .XSWhile _ => isFalse (by intro h; cases h)
  | .XSNested _ _, .XSFor _ => isFalse (by intro h; cases h)
  | .XSNested _ _, .XSCase _ => isFalse (by intro h; cases h)
  | .XSNested _ _, .XSDefun _ => isFalse (by intro h; cases h)
  | .XSNested _ _, .XSStack _ _ => isFalse (by intro h; cases h)
  | .XSNested _ _, .XSStep _ => isFalse (by intro h; cases h)
  | .XSNested _ _, .XSExec _ => isFalse (by intro h; cases h)
  | .XSNested _ _, .XSEval _ _ _ => isFalse (by intro h; cases h)
  | .XSNested _ _, .XSWait _ => isFalse (by intro h; cases h)
  | .XSNested _ _, .XSTrap _ _ => isFalse (by intro h; cases h)
  | .XSNested _ _, .XSProc _ _ => isFalse (by intro h; cases h)
  | .XSNested _ _, .XSExpand _ _ => isFalse (by intro h; cases h)

  | .XSExpand _ _, .XSSimple _ => isFalse (by intro h; cases h)
  | .XSExpand _ _, .XSPipe _ => isFalse (by intro h; cases h)
  | .XSExpand _ _, .XSRedir _ => isFalse (by intro h; cases h)
  | .XSExpand _ _, .XSBackground _ => isFalse (by intro h; cases h)
  | .XSExpand _ _, .XSSubshell _ => isFalse (by intro h; cases h)
  | .XSExpand _ _, .XSAnd _ => isFalse (by intro h; cases h)
  | .XSExpand _ _, .XSOr _ => isFalse (by intro h; cases h)
  | .XSExpand _ _, .XSNot _ => isFalse (by intro h; cases h)
  | .XSExpand _ _, .XSSemi _ => isFalse (by intro h; cases h)
  | .XSExpand _ _, .XSIf _ => isFalse (by intro h; cases h)
  | .XSExpand _ _, .XSWhile _ => isFalse (by intro h; cases h)
  | .XSExpand _ _, .XSFor _ => isFalse (by intro h; cases h)
  | .XSExpand _ _, .XSCase _ => isFalse (by intro h; cases h)
  | .XSExpand _ _, .XSDefun _ => isFalse (by intro h; cases h)
  | .XSExpand _ _, .XSStack _ _ => isFalse (by intro h; cases h)
  | .XSExpand _ _, .XSStep _ => isFalse (by intro h; cases h)
  | .XSExpand _ _, .XSExec _ => isFalse (by intro h; cases h)
  | .XSExpand _ _, .XSEval _ _ _ => isFalse (by intro h; cases h)
  | .XSExpand _ _, .XSWait _ => isFalse (by intro h; cases h)
  | .XSExpand _ _, .XSTrap _ _ => isFalse (by intro h; cases h)
  | .XSExpand _ _, .XSProc _ _ => isFalse (by intro h; cases h)
  | .XSExpand _ _, .XSNested _ _ => isFalse (by intro h; cases h)
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by repeat' (simp_wf; omega)

end
