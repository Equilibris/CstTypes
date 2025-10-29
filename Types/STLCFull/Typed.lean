import Types.STLCFull.Stx
import Types.STLCFull.Red
import Types.STLCFull.Repl
import Mathlib.Data.Rel

namespace STLCFull

@[grind]
inductive TySpec : List Ty → Stx → Ty → Prop
  | bvar {idx ty Γ} : Γ[idx]? = some ty → TySpec Γ (.bvar idx) ty
  | app {Γ fn arg argTy retTy} : TySpec Γ fn (.arr argTy retTy) → TySpec Γ arg argTy
      → TySpec Γ (.app fn arg) retTy
  | abs {Γ body argTy retTy} : TySpec (argTy :: Γ) body retTy
      → TySpec Γ (.abs argTy body) (.arr argTy retTy)
  | prod {Γ a b tyA tyB} : TySpec Γ a tyA → TySpec Γ b tyB
      → TySpec Γ (.prod a b) (.prod tyA tyB)
  | fst {Γ expr tyA tyB} : TySpec Γ expr (.prod tyA tyB)
      → TySpec Γ (.fst expr) tyA
  | snd {Γ expr tyA tyB} : TySpec Γ expr (.prod tyA tyB)
      → TySpec Γ (.snd expr) tyB

@[simp, grind =]
theorem TySpec_bvar {Γ idx ty} : TySpec Γ (.bvar idx) ty ↔ Γ[idx]? = some ty := by
  grind

@[simp, grind =]
theorem TySpec_app {Γ fn arg ty} : TySpec Γ (.app fn arg) ty ↔
    (∃ argTy, (TySpec Γ fn (.arr argTy ty) ∧ TySpec Γ arg argTy)) := by
  grind

@[simp, grind =]
theorem TySpec_abs {Γ argTy body retTy}
    : TySpec Γ (.abs argTy body) (.arr argTy retTy) ↔ (TySpec (argTy :: Γ) body retTy) := by
  grind

@[simp, grind =]
theorem TySpec_prod {Γ a b tyA tyB}
    : TySpec Γ (.prod a b) (.prod tyA tyB) ↔ (TySpec Γ a tyA ∧ TySpec Γ b tyB) := by
  grind

@[simp, grind =]
theorem TySpec_fst {Γ expr tyA}
    : TySpec Γ (.fst expr) tyA ↔ ∃ tyB, TySpec Γ expr (.prod tyA tyB) := by
  grind

@[simp, grind =]
theorem TySpec_snd {Γ expr tyB}
    : TySpec Γ (.snd expr) tyB ↔ ∃ tyA, TySpec Γ expr (.prod tyA tyB) := by
  grind

theorem TySpec_abs' {Γ argTy body z}
    : TySpec Γ (.abs argTy body) z
    ↔ ∃ retTy, (z = (.arr argTy retTy)) ∧ (TySpec (argTy :: Γ) body retTy) := by
  grind

theorem TySpec_prod' {Γ a b z}
    : TySpec Γ (.prod a b) z
    ↔ ∃ tyA tyB, (z = (.prod tyA tyB)) ∧ (TySpec Γ a tyA ∧ TySpec Γ b tyB) := by
  grind

theorem TySpec_unique {Γ i o₁ o₂} (a : TySpec Γ i o₁) (b : TySpec Γ i o₂) : o₁ = o₂ :=
  match i, a, b with
  | .bvar id, a, b => by
    grind
  | .app fn arg, .app ha₁ hb₁, .app ha₂ hb₂ => by
    obtain rfl := TySpec_unique hb₁ hb₂
    obtain ⟨_, rfl⟩ := (Ty.arr.injEq _ _ _ _).mp <| TySpec_unique ha₁ ha₂
    rfl
  | .abs ty body, .abs ha, .abs hb => by
    obtain rfl := TySpec_unique ha hb
    rfl
  | .prod exprA exprB, .prod ha₁ hb₁, .prod ha₂ hb₂ => 
    (Ty.prod.injEq _ _ _ _).mpr ⟨TySpec_unique ha₁ ha₂, TySpec_unique hb₁ hb₂⟩
  | .fst expr, .fst ha, .fst hb =>
    ((Ty.prod.injEq _ _ _ _).mp <| TySpec_unique ha hb).left
  | .snd expr, .snd ha, .snd hb =>
    ((Ty.prod.injEq _ _ _ _).mp <| TySpec_unique ha hb).right

theorem bvarShift_maintain_gen
    {Γ₂ Γ body ty₂ Γ₁}
    (h : TySpec (Γ₂ ++ Γ) body ty₂)
    : TySpec (Γ₂ ++ Γ₁ ++ Γ) (body.bvarShift Γ₁.length Γ₂.length) ty₂
    :=
  match body, h with
  | .bvar idx, .bvar h => by
    rw [List.append_assoc, Stx.bvarShift, TySpec_bvar]
    split
    next lt => grind
    next ge =>
      rw [not_lt] at ge
      rw [List.getElem?_append_right ge] at h
      rw [
        List.getElem?_append_right (ge.trans <| Nat.le_add_right _ _),
        Nat.sub_add_comm ge,
        List.getElem?_append_right (Nat.le_add_left Γ₁.length (idx - Γ₂.length)),
        Nat.add_sub_cancel
      ]
      exact h
  | .abs ty body, .abs h => by
    rw [List.append_assoc, Stx.bvarShift, Nat.succ_eq_add_one, ←List.append_assoc]
    rw [←List.cons_append] at h
    exact .abs <| bvarShift_maintain_gen h
  | .app a b, .app ha hb => by
    rw [Stx.bvarShift]
    exact .app (bvarShift_maintain_gen ha) (bvarShift_maintain_gen hb)
  | .prod a b, .prod ha hb => by
    rw [Stx.bvarShift]
    exact .prod (bvarShift_maintain_gen ha) (bvarShift_maintain_gen hb)
  | .fst expr, .fst h => by
    rw [Stx.bvarShift]
    exact .fst <| bvarShift_maintain_gen h
  | .snd expr, .snd h => by
    rw [Stx.bvarShift]
    exact .snd <| bvarShift_maintain_gen h

theorem bvarShift_maintain
    {Γ body ty₂ Γ₁}
    (h : TySpec Γ body ty₂)
    : (TySpec (Γ₁ ++ Γ) (body.bvarShift Γ₁.length 0) ty₂) := by
  change TySpec ([] ++ Γ₁ ++ Γ) (body.bvarShift Γ₁.length ([] : List Ty).length) ty₂
  exact bvarShift_maintain_gen h

theorem TySpec_replace_gen
    {Γ body arg x Γ' ty₁}
    (argTy : TySpec Γ arg x)
    (base : TySpec (Γ' ++ (x :: Γ)) body ty₁)
    : TySpec (Γ' ++ Γ) (body.replace (Γ'.length) arg) ty₁ :=
  match body, base with
  | .bvar idx, .bvar base => by
    rw [Stx.replace, Stx.replace.bvar, Nat.pred_eq_sub_one]
    split
    <;> rename_i heq
    <;> simp only [Nat.compare_eq_eq, Nat.compare_eq_gt, Nat.compare_eq_lt] at heq
    · rw [TySpec_bvar]
      simp only [List.getElem?_append, heq, ↓reduceIte, getElem?_pos, Option.some.injEq] at base ⊢
      exact base
    · subst heq
      rw [List.getElem?_append_right (Nat.le_refl Γ'.length), Nat.sub_self,
        List.getElem?_cons_zero, Option.some.injEq] at base
      subst base
      change TySpec Γ _ _ at argTy
      exact bvarShift_maintain (Γ₁ := Γ') argTy
    · cases idx
      · contradiction
      next n =>
      have heq : Γ'.length ≤ n := Nat.le_of_lt_succ heq
      rw [TySpec_bvar, Nat.add_sub_cancel, List.getElem?_append_right heq]
      rw [
        List.getElem?_append_right <| heq.trans <| Nat.le_add_right n 1,
        Nat.sub_add_comm heq,
        List.getElem?_cons_succ
      ] at base
      exact base
  | .abs ty body, .abs base => by
    rw [←List.cons_append] at base
    exact .abs <| TySpec_replace_gen argTy base
  | .app a b, .app hFn hArg => 
    .app (TySpec_replace_gen argTy hFn) (TySpec_replace_gen argTy hArg)
  | .prod a b, .prod hA hB => .prod (TySpec_replace_gen argTy hA) (TySpec_replace_gen argTy hB)
  | .fst expr, .fst h => .fst (TySpec_replace_gen argTy h)
  | .snd expr, .snd h => .snd (TySpec_replace_gen argTy h)

theorem TySpec_replace
    {Γ x body ty₁ v}
    (hty₁ : TySpec Γ (.app (.abs x body) v) ty₁)
    : TySpec Γ (body.β v) ty₁ := by
  rw [TySpec_app] at hty₁
  rcases hty₁ with ⟨argTy, a, argTy⟩
  cases a
  next a =>
  change TySpec ([] ++ x :: Γ) _ _ at a
  exact TySpec_replace_gen argTy a

theorem TypePreservation
    {e₁ e₂ ty Γ}
    (h : Red e₁ e₂) (hTy : TySpec Γ e₁ ty) : TySpec Γ e₂ ty :=
  match h, hTy with
  | .app_fn h, .app ha hb => .app (TypePreservation h ha) hb
  | .app_arg h, .app ha hb => .app ha (TypePreservation h hb)
  | .abs h, .abs hTy => .abs <| TypePreservation h hTy
  | .prod_fst h, .prod ha hb => .prod (TypePreservation h ha) hb
  | .prod_snd h, .prod ha hb => .prod ha (TypePreservation h hb)
  | .fst h, .fst hTy => .fst <| TypePreservation h hTy
  | .snd h, .snd hTy => .snd <| TypePreservation h hTy
  | .beta, hTy => TySpec_replace ‹_›
  | .fst_beta, .fst (.prod ha _) => ha
  | .snd_beta, .snd (.prod _ hb) => hb

end STLCFull

