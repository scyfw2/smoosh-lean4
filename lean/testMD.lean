universe u

inductive SS : Type
| SS_1
| SS_2
deriving DecidableEq, Repr

inductive SM : Type
| SM_1
| SM_2
deriving DecidableEq, Repr

inductive P : Type u
| Mk (p1 : SS) (p2 : SM)
deriving DecidableEq, Repr

mutual

  inductive F : Type u
  | F_N
  | F_D  (f1 : E)
  | F_S  (s1 : SS) (s2 : SM)
  deriving Repr

  inductive E : Type u
  | E_S  (e1 : String)
  | E_K  (e1 : C)
  deriving Repr

inductive G₁ : Type u
  | G_S1 (g1 : String)
  | G_S2 (g1 : String)
  | G_S3 (g1 : String)
  | G_S4 (g1 : String)
  deriving Repr

  inductive G₂ : Type u
  | G_S5 (g1 : String)
  | G_S6 (g1 : String)
  | G_S7 (g1 : String)
  | G_S8 (g1 : String)
  | G_S9 (g1 : String)
  deriving Repr

  inductive G₃ : Type u
  | G_E1 (g1 : E)
  | G_F1 (g1 : F)
  deriving Repr

  inductive G₄ : Type u
  | G_C1 (g1 : C)
  deriving Repr

  inductive C : Type u
  | C_T  (c1 : Sum G₁ (Sum G₂ (Sum G₃ G₄)))
  | C_E  (c1 : String) (c2 : List E)
  | C_F  (c1 : String) (c2 : E × F)
  deriving Repr

end

-- namespace MutualDecEq

-- mutual
--   private def decEqListE : (xs ys : List E) → Decidable (xs = ys)
--     | [], [] => isTrue rfl
--     | [], _ :: _ =>
--         isFalse (by intro h; cases h)
--     | _ :: _, [] =>
--         isFalse (by intro h; cases h)
--     | x :: xs, y :: ys =>
--         match decEqE x y with
--         | isTrue hxy =>
--             match decEqListE xs ys with
--             | isTrue hrest =>
--                 isTrue (by cases hxy; cases hrest; rfl)
--             | isFalse hnrest =>
--                 isFalse (by
--                   intro h
--                   cases h
--                   exact hnrest rfl)
--         | isFalse hnxy =>
--             isFalse (by
--               intro h
--               cases h
--               exact hnxy rfl)


--   private def decEqFE : (p q : F × E) → Decidable (p = q)
--     | (f1, e1), (f2, e2) =>
--         match decEqF f1 f2 with
--         | isTrue hf =>
--             match decEqE e1 e2 with
--             | isTrue he =>
--                 isTrue (by cases hf; cases he; rfl)
--             | isFalse hne =>
--                 isFalse (by
--                   intro h
--                   cases h
--                   exact hne rfl)
--         | isFalse hnf =>
--             isFalse (by
--               intro h
--               cases h
--               exact hnf rfl)

--   private def decEqF : (a b : F) → Decidable (a = b)
--     | .F_N, .F_N => isTrue rfl
--     | .F_N, .F_D _ => isFalse (by intro h; cases h)
--     | .F_N, .F_S _ _ => isFalse (by intro h; cases h)

--     | .F_D _, .F_N => isFalse (by intro h; cases h)
--     | .F_D xs, .F_D ys =>
--         match decEqListE xs ys with
--         | isTrue h => isTrue (by cases h; rfl)
--         | isFalse hn =>
--             isFalse (by
--               intro h
--               cases h
--               exact hn rfl)
--     | .F_D _, .F_S _ _ => isFalse (by intro h; cases h)

--     | .F_S _ _, .F_N => isFalse (by intro h; cases h)
--     | .F_S _ _, .F_D _ => isFalse (by intro h; cases h)
--     | .F_S s1 m1, .F_S s2 m2 =>
--         match decEq s1 s2 with
--         | isTrue hs =>
--             match decEq m1 m2 with
--             | isTrue hm =>
--                 isTrue (by cases hs; cases hm; rfl)
--             | isFalse hnm =>
--                 isFalse (by
--                   intro h
--                   cases h
--                   exact hnm rfl)
--         | isFalse hns =>
--             isFalse (by
--               intro h
--               cases h
--               exact hns rfl)

--   private def decEqC : (a b : C) → Decidable (a = b)
--     | .C_T s1, .C_T s2 =>
--         match decEq s1 s2 with
--         | isTrue hs => isTrue (by cases hs; rfl)
--         | isFalse hns =>
--             isFalse (by
--               intro h
--               cases h
--               exact hns rfl)
--     | .C_T _, .B_P _ _ => isFalse (by intro h; cases h)
--     | .B_P _ _, .C_T _ => isFalse (by intro h; cases h)
--     | .B_P s1 p1, .B_P s2 p2 =>
--         match decEq s1 s2 with
--         | isTrue hs =>
--             match decEqFE p1 p2 with
--             | isTrue hp =>
--                 isTrue (by cases hs; cases hp; rfl)
--             | isFalse hnp =>
--                 isFalse (by
--                   intro h
--                   cases h
--                   exact hnp rfl)
--         | isFalse hns =>
--             isFalse (by
--               intro h
--               cases h
--               exact hns rfl)

--   private def decEqE : (a b : E) → Decidable (a = b)
--     | .E_S s1, .E_S s2 =>
--         match decEq s1 s2 with
--         | isTrue hs => isTrue (by cases hs; rfl)
--         | isFalse hns =>
--             isFalse (by
--               intro h
--               cases h
--               exact hns rfl)
--     | .E_S _, .E_K _ => isFalse (by intro h; cases h)
--     | .E_K _, .E_S _ => isFalse (by intro h; cases h)
--     | .E_K c1, .E_K c2 =>
--         match decEqC c1 c2 with
--         | isTrue hc => isTrue (by cases hc; rfl)
--         | isFalse hnc =>
--             isFalse (by
--               intro h
--               cases h
--               exact hnc rfl)
-- end

-- instance : DecidableEq F := decEqF
-- instance : DecidableEq C := decEqC
-- instance : DecidableEq E := decEqE

-- end MutualDecEq

-- private def decEqString (a b : String) : Decidable (a = b) := inferInstance
-- private def decEqNat (a b : Nat) : Decidable (a = b) := inferInstance
-- private def decEqChar (a b : Char) : Decidable (a = b) := inferInstance
-- private def decEqOption {α} (dec : (x y : α) → Decidable (x = y)) :
--     (o1 o2 : Option α) → Decidable (o1 = o2)
--   | none, none => isTrue rfl
--   | some a, some b =>
--       match dec a b with
--       | isTrue h  => isTrue (by cases h; rfl)
--       | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
--   | none, some _ => isFalse (by intro h; cases h)
--   | some _, none => isFalse (by intro h; cases h)
-- private def decEqProd {α β}
--     (deca : (x y : α) → Decidable (x = y))
--     (decb : (x y : β) → Decidable (x = y)) :
--     (p q : α × β) → Decidable (p = q)
--   | (a1, b1), (a2, b2) =>
--       match deca a1 a2, decb b1 b2 with
--       | isTrue ha, isTrue hb => isTrue (by cases ha; cases hb; rfl)
--       | isFalse ha, _ => isFalse (by intro h; cases h; exact ha rfl)
--       | _, isFalse hb => isFalse (by intro h; cases h; exact hb rfl)
-- private def decEqList {α} (dec : (x y : α) → Decidable (x = y)) :
  --   (xs ys : List α) → Decidable (xs = ys)
  -- | [], [] => isTrue rfl
  -- | x::xs, y::ys =>
  --     match dec x y, decEqList dec xs ys with
  --     | isTrue hx, isTrue hxs => isTrue (by cases hx; cases hxs; rfl)
  --     | isFalse hx, _ => isFalse (by intro h; cases h; exact hx rfl)
  --     | _, isFalse hxs => isFalse (by intro h; cases h; exact hxs rfl)
  -- | [], _::_ => isFalse (by intro h; cases h)
  -- | _::_, [] => isFalse (by intro h; cases h)
-- private def decEqCongrArg {α β} (f : α → β) {x y : α} :
--     Decidable (x = y) → Decidable (f x = f y)
--   | isTrue h  => isTrue (by cases h; rfl)
--   | isFalse h => isFalse (by intro hxy
--                              exact (not_iff_false_intro x).mp fun a => h rfl)
-- private def decEqSum
--     {α : Type u} {β : Type v}
--     (decEqA : (a b : α) → Decidable (a = b))
--     (decEqB : (a b : β) → Decidable (a = b))
--     : (x y : Sum α β) → Decidable (x = y)
--   | Sum.inl a1, Sum.inl a2 =>
--       match decEqA a1 a2 with
--       | isTrue h  => isTrue (by cases h; rfl)
--       | isFalse h => isFalse (by intro hxy; cases hxy; exact h rfl)

--   | Sum.inr b1, Sum.inr b2 =>
--       match decEqB b1 b2 with
--       | isTrue h  => isTrue (by cases h; rfl)
--       | isFalse h => isFalse (by intro hxy; cases hxy; exact h rfl)

--   | Sum.inl a1, Sum.inr b2 =>
--       isFalse (by intro hxy; cases hxy)

--   | Sum.inr b1, Sum.inl a2 =>
--       isFalse (by intro hxy; cases hxy)

-- mutual

--   private def decEqF : (a b : F) → Decidable (a = b)
--     | .F_N, .F_N => isTrue rfl
--     | .F_D x, .F_D y =>
--         match decEqE x y with
--         | isTrue h  => isTrue (by cases h; rfl)
--         | isFalse h => isFalse (by intro hxy; cases hxy; exact h rfl)
--     | .F_S s1 t1, .F_S s2 t2 =>
--         match (inferInstance : Decidable (s1 = s2)),
--               (inferInstance : Decidable (t1 = t2)) with
--         | isTrue hs, isTrue ht => isTrue (by cases hs; cases ht; rfl)
--         | isFalse hs, _        => isFalse (by intro h; cases h; exact hs rfl)
--         | _, isFalse ht        => isFalse (by intro h; cases h; exact ht rfl)
--     | .F_N, .F_D _ => isFalse (by intro h; cases h)
--     | .F_N, .F_S _ _ => isFalse (by intro h; cases h)
--     | .F_D _, .F_N => isFalse (by intro h; cases h)
--     | .F_D _, .F_S _ _ => isFalse (by intro h; cases h)
--     | .F_S _ _, .F_N => isFalse (by intro h; cases h)
--     | .F_S _ _, .F_D _ => isFalse (by intro h; cases h)
--   termination_by
--     a b      => sizeOf a + sizeOf b
--   decreasing_by
--     repeat' (simp_wf; omega)


--   private def decEqListE : (xs ys : List E) → Decidable (xs = ys)
--   | [], [] => isTrue rfl
--   | x::xs, y::ys =>
--       match decEqE x y, decEqListE xs ys with
--       | isTrue hx, isTrue hxs => isTrue (by cases hx; cases hxs; rfl)
--       | isFalse hx, _         => isFalse (by intro h; cases h; exact hx rfl)
--       | _, isFalse hxs        => isFalse (by intro h; cases h; exact hxs rfl)
--   | [], _::_ => isFalse (by intro h; cases h)
--   | _::_, [] => isFalse (by intro h; cases h)
--   termination_by
--     a b      => sizeOf a + sizeOf b
--   decreasing_by
--     repeat' (simp_wf; omega)


--   private def decEqProdEF : (p q : E × F) → Decidable (p = q)
--   | (e1, f1), (e2, f2) =>
--       match decEqE e1 e2, decEqF f1 f2 with
--       | isTrue he, isTrue hf => isTrue (by cases he; cases hf; rfl)
--       | isFalse he, _        => isFalse (by intro h; cases h; exact he rfl)
--       | _, isFalse hf        => isFalse (by intro h; cases h; exact hf rfl)
--   termination_by
--     a b      => sizeOf a + sizeOf b
--   decreasing_by
--     repeat' (simp_wf; omega)


--   private def decEqC : (a b : C) → Decidable (a = b)
--   | .C_T s1, .C_T s2 =>
--         match (inferInstance : Decidable (s1 = s2)) with
--         | isTrue h  => isTrue (by cases h; rfl)
--         | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
--   | .C_E s1 xs, .C_E s2 ys =>
--         match (inferInstance : Decidable (s1 = s2)), decEqListE xs ys with
--         | isTrue hs, isTrue hxy => isTrue (by cases hs; cases hxy; rfl)
--         | isFalse hs, _         => isFalse (by intro h; cases h; exact hs rfl)
--         | _, isFalse hxy        => isFalse (by intro h; cases h; exact hxy rfl)
--   | .C_F s1 p1, .C_F s2 p2 =>
--         match (inferInstance : Decidable (s1 = s2)), decEqProdEF p1 p2 with
--         | isTrue hs, isTrue hp => isTrue (by cases hs; cases hp; rfl)
--         | isFalse hs, _        => isFalse (by intro h; cases h; exact hs rfl)
--         | _, isFalse hp        => isFalse (by intro h; cases h; exact hp rfl)
--   | .C_T _, .C_E _ _ => isFalse (by intro h; cases h)
--   | .C_T _, .C_F _ _ => isFalse (by intro h; cases h)
--   | .C_E _ _, .C_T _ => isFalse (by intro h; cases h)
--   | .C_E _ _, .C_F _ _ => isFalse (by intro h; cases h)
--   | .C_F _ _, .C_T _ => isFalse (by intro h; cases h)
--   | .C_F _ _, .C_E _ _ => isFalse (by intro h; cases h)
--   termination_by
--     a b      => sizeOf a + sizeOf b
--   decreasing_by
--     repeat' (simp_wf; omega)


--   private def decEqE : (a b : E) → Decidable (a = b)
--   | .E_S s1, .E_S s2 =>
--       match (inferInstance : Decidable (s1 = s2)) with
--       | isTrue h  => isTrue (by cases h; rfl)
--       | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
--   | .E_K c1, .E_K c2 =>
--       match decEqC c1 c2 with
--       | isTrue h  => isTrue (by cases h; rfl)
--       | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
--   | .E_S _, .E_K _ => isFalse (by intro h; cases h)
--   | .E_K _, .E_S _ => isFalse (by intro h; cases h)
--   termination_by
--     a b      => sizeOf a + sizeOf b
--   decreasing_by
--     repeat' (simp_wf; omega)

-- end

mutual

  private def decEqListE : (xs ys : List E) → Decidable (xs = ys)
  | [], [] => isTrue rfl
  | x :: xs, y :: ys =>
      match decEqE x y, decEqListE xs ys with
      | isTrue hx, isTrue hxs => isTrue (by cases hx; cases hxs; rfl)
      | isFalse hx, _         => isFalse (by intro h; cases h; exact hx rfl)
      | _, isFalse hxs        => isFalse (by intro h; cases h; exact hxs rfl)
  | [], _ :: _ => isFalse (by intro h; cases h)
  | _ :: _, [] => isFalse (by intro h; cases h)
  termination_by
    xs ys => sizeOf xs + sizeOf ys
  decreasing_by
    repeat' (simp_wf; omega)

  private def decEqProdEF : (p q : E × F) → Decidable (p = q)
  | Prod.mk e1 f1, Prod.mk e2 f2 =>
      match decEqE e1 e2, decEqF f1 f2 with
      | isTrue he, isTrue hf => isTrue (by cases he; cases hf; rfl)
      | isFalse he, _        => isFalse (by intro h; cases h; exact he rfl)
      | _, isFalse hf        => isFalse (by intro h; cases h; exact hf rfl)
  termination_by
    p q => sizeOf p + sizeOf q
  decreasing_by
    repeat' (simp_wf; omega)

  private def decEqF : (a b : F) → Decidable (a = b)
    | .F_N, .F_N => isTrue rfl
    | .F_D x, .F_D y =>
        match decEqE x y with
        | isTrue h  => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro hxy; cases hxy; exact h rfl)
    | .F_S s1 t1, .F_S s2 t2 =>
        match (inferInstance : Decidable (s1 = s2)),
              (inferInstance : Decidable (t1 = t2)) with
        | isTrue hs, isTrue ht => isTrue (by cases hs; cases ht; rfl)
        | isFalse hs, _        => isFalse (by intro h; cases h; exact hs rfl)
        | _, isFalse ht        => isFalse (by intro h; cases h; exact ht rfl)
    | .F_N, .F_D _ => isFalse (by intro h; cases h)
    | .F_N, .F_S _ _ => isFalse (by intro h; cases h)
    | .F_D _, .F_N => isFalse (by intro h; cases h)
    | .F_D _, .F_S _ _ => isFalse (by intro h; cases h)
    | .F_S _ _, .F_N => isFalse (by intro h; cases h)
    | .F_S _ _, .F_D _ => isFalse (by intro h; cases h)
  termination_by
    a b => sizeOf a + sizeOf b
  decreasing_by
    repeat' (simp_wf; omega)
  -- private def decEqF : (a b : F) → Decidable (a = b) := by
  --   intro a b
  --   cases a <;> cases b <;>
  --     (try
  --        (refine isFalse ?_ <;> intro h <;> cases h <;> done))
  --   . exact isTrue rfl
  --   . expose_names
  --     cases (decEqE f1 f1_1) with
  --     | isTrue h  => exact isTrue (by cases h; rfl)
  --     | isFalse h =>
  --       exact isFalse (by
  --         intro hxy
  --         cases hxy
  --         exact h rfl)
  --   . expose_names
  --     cases (inferInstance : Decidable (s1 = s1_1)) with
  --     | isTrue hs =>
  --         cases (inferInstance : Decidable (s2 = s2_1)) with
  --         | isTrue ht =>
  --             exact isTrue (by cases hs; cases ht; rfl)
  --         | isFalse ht =>
  --             exact isFalse (by intro h; cases h; exact ht rfl)
  --     | isFalse hs =>
  --         exact isFalse (by intro h; cases h; exact hs rfl)
  -- termination_by
  --   a b => sizeOf a + sizeOf b
  -- decreasing_by
  --   repeat' (simp_wf; omega)

  private def decEqG₁ : (a b : G₁) → Decidable (a = b)
    | .G_S1 s1, .G_S1 s2 =>
        match (inferInstance : Decidable (s1 = s2)) with
        | isTrue h  => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .G_S2 s1, .G_S2 s2 =>
        match (inferInstance : Decidable (s1 = s2)) with
        | isTrue h  => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .G_S3 s1, .G_S3 s2 =>
        match (inferInstance : Decidable (s1 = s2)) with
        | isTrue h  => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .G_S4 s1, .G_S4 s2 =>
        match (inferInstance : Decidable (s1 = s2)) with
        | isTrue h  => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .G_S1 _, .G_S2 _ => isFalse (by intro h; cases h)
    | .G_S1 _, .G_S3 _ => isFalse (by intro h; cases h)
    | .G_S1 _, .G_S4 _ => isFalse (by intro h; cases h)
    | .G_S2 _, .G_S1 _ => isFalse (by intro h; cases h)
    | .G_S2 _, .G_S3 _ => isFalse (by intro h; cases h)
    | .G_S2 _, .G_S4 _ => isFalse (by intro h; cases h)
    | .G_S3 _, .G_S1 _ => isFalse (by intro h; cases h)
    | .G_S3 _, .G_S2 _ => isFalse (by intro h; cases h)
    | .G_S3 _, .G_S4 _ => isFalse (by intro h; cases h)
    | .G_S4 _, .G_S1 _ => isFalse (by intro h; cases h)
    | .G_S4 _, .G_S2 _ => isFalse (by intro h; cases h)
    | .G_S4 _, .G_S3 _ => isFalse (by intro h; cases h)

  private def decEqG₂ : (a b : G₂) → Decidable (a = b)
    | .G_S5 s1, .G_S5 s2 =>
        match (inferInstance : Decidable (s1 = s2)) with
        | isTrue h  => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .G_S6 s1, .G_S6 s2 =>
        match (inferInstance : Decidable (s1 = s2)) with
        | isTrue h  => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .G_S7 s1, .G_S7 s2 =>
        match (inferInstance : Decidable (s1 = s2)) with
        | isTrue h  => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .G_S8 s1, .G_S8 s2 =>
        match (inferInstance : Decidable (s1 = s2)) with
        | isTrue h  => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .G_S9 s1, .G_S9 s2 =>
        match (inferInstance : Decidable (s1 = s2)) with
        | isTrue h  => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .G_S5 _, .G_S6 _ => isFalse (by intro h; cases h)
    | .G_S5 _, .G_S7 _ => isFalse (by intro h; cases h)
    | .G_S5 _, .G_S8 _ => isFalse (by intro h; cases h)
    | .G_S5 _, .G_S9 _ => isFalse (by intro h; cases h)
    | .G_S6 _, .G_S5 _ => isFalse (by intro h; cases h)
    | .G_S6 _, .G_S7 _ => isFalse (by intro h; cases h)
    | .G_S6 _, .G_S8 _ => isFalse (by intro h; cases h)
    | .G_S6 _, .G_S9 _ => isFalse (by intro h; cases h)
    | .G_S7 _, .G_S5 _ => isFalse (by intro h; cases h)
    | .G_S7 _, .G_S6 _ => isFalse (by intro h; cases h)
    | .G_S7 _, .G_S8 _ => isFalse (by intro h; cases h)
    | .G_S7 _, .G_S9 _ => isFalse (by intro h; cases h)
    | .G_S8 _, .G_S5 _ => isFalse (by intro h; cases h)
    | .G_S8 _, .G_S6 _ => isFalse (by intro h; cases h)
    | .G_S8 _, .G_S7 _ => isFalse (by intro h; cases h)
    | .G_S8 _, .G_S9 _ => isFalse (by intro h; cases h)
    | .G_S9 _, .G_S5 _ => isFalse (by intro h; cases h)
    | .G_S9 _, .G_S6 _ => isFalse (by intro h; cases h)
    | .G_S9 _, .G_S7 _ => isFalse (by intro h; cases h)
    | .G_S9 _, .G_S8 _ => isFalse (by intro h; cases h)

  private def decEqG₃ : (a b : G₃) → Decidable (a = b)
    | .G_E1 x, .G_E1 y =>
        match decEqE x y with
        | isTrue h  => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro hxy; cases hxy; exact h rfl)
    | .G_F1 x, .G_F1 y =>
        match decEqF x y with
        | isTrue h  => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro hxy; cases hxy; exact h rfl)
    | .G_E1 _, .G_F1 _ => isFalse (by intro h; cases h)
    | .G_F1 _, .G_E1 _ => isFalse (by intro h; cases h)
  termination_by
    a b => sizeOf a + sizeOf b
  decreasing_by
    repeat' (simp_wf; omega)

  private def decEqG₄ : (a b : G₄) → Decidable (a = b)
    | .G_C1 x, .G_C1 y =>
        match decEqC x y with
        | isTrue h  => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro hxy; cases hxy; exact h rfl)
  termination_by
    a b => sizeOf a + sizeOf b
  decreasing_by
    repeat' (simp_wf; omega)




  private def decEqGSum : (x y : Sum G₁ (Sum G₂ (Sum G₃ G₄))) → Decidable (x = y)
    | Sum.inl a1, Sum.inl a2 =>
        match decEqG₁ a1 a2 with
        | isTrue h  => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro hxy; cases hxy; exact h rfl)
    | Sum.inr b1, Sum.inr b2 =>
        match decEqGSumInner b1 b2 with
        | isTrue h  => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro hxy; cases hxy; exact h rfl)
    | Sum.inl _, Sum.inr _ => isFalse (by intro hxy; cases hxy)
    | Sum.inr _, Sum.inl _ => isFalse (by intro hxy; cases hxy)
  termination_by
    x y => sizeOf x + sizeOf y
  decreasing_by
    repeat' (simp_wf; omega)

  private def decEqGSumInner : (x y : Sum G₂ (Sum G₃ G₄)) → Decidable (x = y)
    | Sum.inl a1, Sum.inl a2 =>
        match decEqG₂ a1 a2 with
        | isTrue h  => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro hxy; cases hxy; exact h rfl)

    | Sum.inr b1, Sum.inr b2 =>
        match decEqGSumInner2 b1 b2 with
        | isTrue h  => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro hxy; cases hxy; exact h rfl)

    | Sum.inl _, Sum.inr _ => isFalse (by intro hxy; cases hxy)
    | Sum.inr _, Sum.inl _ => isFalse (by intro hxy; cases hxy)
  termination_by
    x y => sizeOf x + sizeOf y
  decreasing_by
    repeat' (simp_wf; omega)

  private def decEqGSumInner2 : (x y : Sum G₃ G₄) → Decidable (x = y)
    | Sum.inl a1, Sum.inl a2 =>
        match decEqG₃ a1 a2 with
        | isTrue h  => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro hxy; cases hxy; exact h rfl)

    | Sum.inr b1, Sum.inr b2 =>
        match decEqG₄ b1 b2 with
        | isTrue h  => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro hxy; cases hxy; exact h rfl)

    | Sum.inl _, Sum.inr _ => isFalse (by intro hxy; cases hxy)
    | Sum.inr _, Sum.inl _ => isFalse (by intro hxy; cases hxy)
  termination_by
    x y => sizeOf x + sizeOf y
  decreasing_by
    repeat' (simp_wf; omega)



  private def decEqC : (a b : C) → Decidable (a = b)
    | .C_T g1, .C_T g2 =>
        match decEqGSum g1 g2 with
        | isTrue h  => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro hxy; cases hxy; exact h rfl)

    | .C_E s1 xs, .C_E s2 ys =>
        match (inferInstance : Decidable (s1 = s2)), decEqListE xs ys with
        | isTrue hs, isTrue hxy => isTrue (by cases hs; cases hxy; rfl)
        | isFalse hs, _         => isFalse (by intro h; cases h; exact hs rfl)
        | _, isFalse hxy        => isFalse (by intro h; cases h; exact hxy rfl)

    | .C_F s1 p1, .C_F s2 p2 =>
        match (inferInstance : Decidable (s1 = s2)), decEqProdEF p1 p2 with
        | isTrue hs, isTrue hp => isTrue (by cases hs; cases hp; rfl)
        | isFalse hs, _        => isFalse (by intro h; cases h; exact hs rfl)
        | _, isFalse hp        => isFalse (by intro h; cases h; exact hp rfl)
    | .C_T _, .C_E _ _ => isFalse (by intro h; cases h)
    | .C_T _, .C_F _ _ => isFalse (by intro h; cases h)
    | .C_E _ _, .C_T _ => isFalse (by intro h; cases h)
    | .C_E _ _, .C_F _ _ => isFalse (by intro h; cases h)
    | .C_F _ _, .C_T _ => isFalse (by intro h; cases h)
    | .C_F _ _, .C_E _ _ => isFalse (by intro h; cases h)
  termination_by
    a b => sizeOf a + sizeOf b
  decreasing_by
    repeat' (simp_wf; omega)




  private def decEqE : (a b : E) → Decidable (a = b)
    | .E_S s1, .E_S s2 =>
        match (inferInstance : Decidable (s1 = s2)) with
        | isTrue h  => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)

    | .E_K c1, .E_K c2 =>
        match decEqC c1 c2 with
        | isTrue h  => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)

    | .E_S _, .E_K _ => isFalse (by intro h; cases h)
    | .E_K _, .E_S _ => isFalse (by intro h; cases h)
  termination_by
    a b => sizeOf a + sizeOf b
  decreasing_by
    repeat' (simp_wf; omega)

end


instance : DecidableEq F := decEqF
instance : DecidableEq G₁ := decEqG₁
instance : DecidableEq G₂ := decEqG₂
instance : DecidableEq G₃ := decEqG₃
instance : DecidableEq G₄ := decEqG₄
instance : DecidableEq C := decEqC
instance : DecidableEq E := decEqE

inductive G : Type u
| G₁ (x : G₁) | G₂ (x : G₂) | G₃ (x : G₃) | G₄ (x : G₄)
deriving DecidableEq








mutual

  inductive F1 : Type u
  | F_N
  | F_D  (f1 : E1)
  | F_S  (s1 : SS) (s2 : SM)
  deriving Repr

  inductive E1 : Type u
  | E_S  (e1 : String)
  | E_K  (e1 : C1)
  deriving Repr

  inductive C1 : Type u
  | C_E  (c1 : String) (c2 : List E1)
  | C_F  (c1 : String) (c2 : E1 × F1)
  deriving Repr

end

mutual
  private def decEqF1 [DecidableEq SS] [DecidableEq SM]
      : (a b : F1) → Decidable (a = b) := by
    intro a b
    cases a <;> cases b <;>
      (try
        (refine isFalse ?_ <;> intro h <;> cases h <;> done))

    . exact isTrue rfl

    . expose_names
      cases decEqE1 f1 f1_1 with
      | isTrue h  => exact isTrue (by cases h; rfl)
      | isFalse h =>
          exact isFalse (by
            intro hxy
            cases hxy
            exact h rfl)

    . expose_names
      cases (inferInstance : Decidable (s1 = s1_1)) with
      | isTrue hs =>
          cases (inferInstance : Decidable (s2 = s2_1)) with
          | isTrue ht =>
              exact isTrue (by cases hs; cases ht; rfl)
          | isFalse ht =>
              exact isFalse (by intro h; cases h; exact ht rfl)
      | isFalse hs =>
          exact isFalse (by intro h; cases h; exact hs rfl)


  private def decEqE1 [DecidableEq SS] [DecidableEq SM]
      : (a b : E1) → Decidable (a = b) := by
    intro a b
    cases a <;> cases b <;>
      (try
        (refine isFalse ?_ <;> intro h <;> cases h <;> done))

    · -- E_S s1 vs E_S s2
      expose_names
      cases (inferInstance : Decidable (e1 = e1_1)) with
      | isTrue hs  => exact isTrue (by cases hs; rfl)
      | isFalse hs => exact isFalse (by intro h; cases h; exact hs rfl)

    · -- E_K c1 vs E_K c2
      expose_names
      cases (decEqC1 e1 e1_1) with
      | isTrue h  => exact isTrue (by cases h; rfl)
      | isFalse h => exact isFalse (by intro hxy; cases hxy; exact h rfl)

  private def decEqC1 [DecidableEq SS] [DecidableEq SM]
      : (a b : C1) → Decidable (a = b) := by
    intro a b
    cases a <;> cases b <;>
      (try
        (refine isFalse ?_ <;> intro h <;> cases h <;> done))

    · -- C_E s1 xs vs C_E s2 ys
      expose_names
      cases (inferInstance : Decidable (c1 = c1_1)) with
      | isFalse hs =>
          exact isFalse (by intro h; cases h; exact hs rfl)
      | isTrue hs =>
          let rec go : (xs ys : List E1) → Decidable (xs = ys)
            | [], [] => isTrue rfl
            | x :: xs, y :: ys =>
                match decEqE1 x y with
                | isFalse hxy =>
                    isFalse (by intro h; cases h; exact hxy rfl)
                | isTrue hxy =>
                    match go xs ys with
                    | isTrue htail =>
                        isTrue (by cases hxy; cases htail; rfl)
                    | isFalse htail =>
                        isFalse (by intro h; cases h; exact htail rfl)
            | [], _ :: _ => isFalse (by intro h; cases h)
            | _ :: _, [] => isFalse (by intro h; cases h)
          cases go c2 c2_1 with
          | isTrue hlist =>
              exact isTrue (by cases hs; cases hlist; rfl)
          | isFalse hlist =>
              exact isFalse (by
                intro h
                cases h
                exact hlist rfl)

    · -- C_F s1 (e1,f1) vs C_F s2 (e2,f2)
      expose_names
      cases c2 with
      | mk e1 f1 =>
      cases c2_1 with
      | mk e2 f2 =>
      cases (inferInstance : Decidable (c1 = c1_1)) with
      | isFalse hs =>
          exact isFalse (by intro h; cases h; exact hs rfl)
      | isTrue hs =>
          cases decEqE1 e1 e2 with
          | isFalse he =>
              exact isFalse (by intro h; cases h; exact he rfl)
          | isTrue he =>
              cases decEqF1 f1 f2 with
              | isTrue hf =>
                  exact isTrue (by cases hs; cases he; cases hf; rfl)
              | isFalse hf =>
                  exact isFalse (by intro h; cases h; exact hf rfl)

end


instance : DecidableEq F1 := decEqF1
instance : DecidableEq E1 := decEqE1
instance : DecidableEq C1 := decEqC1
