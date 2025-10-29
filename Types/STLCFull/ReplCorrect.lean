import Types.STLCFull.Repl
import Types.STLCFull.RefSet

namespace STLCFull

namespace Stx

/-- Proof of correctness for bvarShift's shifting -/
@[simp]
theorem bvarUnShift_bvarShift {shift skip s} : bvarUnShift shift skip (bvarShift shift skip s) = s := by
  induction s generalizing shift skip
  <;> simp [bvarShift, bvarUnShift]
  case bvar n => split <;> split <;> omega
  case app fn_ih arg_ih => exact ⟨fn_ih, arg_ih⟩
  case abs ty body_ih => exact body_ih
  case prod a_ih b_ih => exact ⟨a_ih, b_ih⟩
  case fst expr_ih => exact expr_ih
  case snd expr_ih => exact expr_ih

variable {n k} in
section
example : bvarShift k 0 (.bvar n) = (.bvar (n + k))                           := by simp [bvarShift]
example : bvarShift k (.succ n) (.bvar 0) = (.bvar 0)                         := by simp [bvarShift]
example : bvarShift k 0 (.abs .unit (.bvar 0)) = (.abs .unit $ .bvar 0)       := by simp [bvarShift]
example : bvarShift k 0 (.abs .unit (.bvar 1)) = (.abs .unit $ .bvar (1 + k)) := by simp [bvarShift]
end

@[simp]
theorem bvarShift.inv {n z} : bvarShift 0 n z = z := by
  induction z generalizing n
  <;> dsimp only [bvarShift]
  case bvar => split <;> rfl
  case app fn_ih arg_ih =>
    simp only [Stx.app.injEq]
    exact ⟨fn_ih, arg_ih⟩
  case abs ty body_ih =>
    simp only [Stx.abs.injEq, true_and]
    exact body_ih
  case prod a_ih b_ih =>
    simp only [Stx.prod.injEq]
    exact ⟨a_ih, b_ih⟩
  case fst expr_ih =>
    simp only [Stx.fst.injEq]
    exact expr_ih
  case snd expr_ih =>
    simp only [Stx.snd.injEq]
    exact expr_ih

@[simp]
theorem bvarShift.comb {n k s}
    : {v : _} → (bvarShift n s (bvarShift k s v)) = bvarShift (n + k) s v
  | .bvar _ => by dsimp [bvarShift]; grind
  | .abs _ _ => (Stx.abs.injEq _ _ _ _).mpr ⟨rfl, bvarShift.comb⟩
  | .app _ _ => (Stx.app.injEq _ _ _ _).mpr ⟨bvarShift.comb, bvarShift.comb⟩
  | .prod _ _ => (Stx.prod.injEq _ _ _ _).mpr ⟨bvarShift.comb, bvarShift.comb⟩
  | .fst _ => (Stx.fst.injEq _ _).mpr bvarShift.comb
  | .snd _ => (Stx.snd.injEq _ _).mpr bvarShift.comb

@[simp]
theorem bvarShift.comb' {n k s}
    : (bvarShift n s ∘ bvarShift k s) = bvarShift (n + k) s :=
  funext fun _ => bvarShift.comb

theorem bvarShift_RefSet_general {body idx skip shift} (h : RefSet body (idx + skip)) : RefSet (body.bvarShift shift skip) (idx + shift + skip) :=
  match body with
  | .bvar n => by
    simp at h
    subst h
    simp [bvarShift]
    split <;> omega
  | .abs ty body => by
    simp_all [bvarShift]
    exact bvarShift_RefSet_general h
  | .app fn arg => by
    simp only [RefSet_app, bvarShift] at h ⊢
    cases h
    next h => exact .inl $ bvarShift_RefSet_general h
    next h => exact .inr $ bvarShift_RefSet_general h
  | .prod a b => by
    simp only [RefSet_prod, bvarShift] at h ⊢
    cases h
    next h => exact .inl $ bvarShift_RefSet_general h
    next h => exact .inr $ bvarShift_RefSet_general h
  | .fst expr => by
    simp only [RefSet_fst, bvarShift] at h ⊢
    exact bvarShift_RefSet_general h
  | .snd expr => by
    simp only [RefSet_snd, bvarShift] at h ⊢
    exact bvarShift_RefSet_general h

theorem bvarShift_RefSet {body idx shift} (h : RefSet body idx) : RefSet (body.bvarShift shift 0) (idx + shift) :=
  bvarShift_RefSet_general h

theorem bvarShift_RefSet_general_rev {body idx shift}
    skip (h : RefSet (body.bvarShift shift skip) (idx + shift + skip))
    : RefSet body (idx + skip) :=
  match body with
  | .bvar n => by
    simp_all [bvarShift]
    split at h <;> omega
  | .abs ty body => by
    simp only [bvarShift, Nat.succ_eq_add_one, RefSet_abs] at h ⊢
    rw [Nat.add_assoc] at h
    exact bvarShift_RefSet_general_rev (skip + 1) h
  | .app fn arg => by
    simp only [bvarShift, RefSet_app] at h ⊢
    cases h
    next h => exact .inl $ bvarShift_RefSet_general_rev skip h
    next h => exact .inr $ bvarShift_RefSet_general_rev skip h
  | .prod a b => by
    simp only [bvarShift, RefSet_prod] at h ⊢
    cases h
    next h => exact .inl $ bvarShift_RefSet_general_rev skip h
    next h => exact .inr $ bvarShift_RefSet_general_rev skip h
  | .fst expr => by
    simp only [bvarShift, RefSet_fst] at h ⊢
    exact bvarShift_RefSet_general_rev skip h
  | .snd expr => by
    simp only [bvarShift, RefSet_snd] at h ⊢
    exact bvarShift_RefSet_general_rev skip h

example {n} : RefSet (.abs .unit (.bvar (n + 1))) n := .abs .bvar

theorem bvarShift_RefSet_rev
    {body idx shift}
    (h : RefSet (body.bvarShift shift 0) (idx + shift))
    : RefSet body idx :=
  bvarShift_RefSet_general_rev 0 h

theorem bvarShift_RefSet_general_rev' {body idx shift}
    skip
    (hlt : skip + shift ≤ idx)
    (h : RefSet (body.bvarShift shift skip) idx)
    : RefSet body (idx - shift) := by
  obtain ⟨idx', rfl⟩ := Nat.exists_eq_add_of_le hlt
  rw [show skip + shift + idx' = idx' + shift + skip by omega] at h
  rw [show (skip + shift + idx' - shift) = idx' + skip by omega]
  exact bvarShift_RefSet_general_rev skip h

theorem bvarShift_RefSet_general_lt_rev {body idx shift}
    skip
    (hlt : idx < skip + shift)
    (h : RefSet (body.bvarShift shift skip) idx)
    : RefSet body idx :=
  match body with
  | .bvar n => by
    simp_all only [bvarShift, RefSet_bvar]
    split at h <;> omega
  | .abs ty body => by
    simp only [bvarShift, Nat.succ_eq_add_one, RefSet_abs] at h ⊢
    exact bvarShift_RefSet_general_lt_rev (skip + 1) (by omega) h
  | .app fn arg => by
    simp only [bvarShift, RefSet_app] at h ⊢
    cases h
    next h => exact .inl $ bvarShift_RefSet_general_lt_rev skip hlt h
    next h => exact .inr $ bvarShift_RefSet_general_lt_rev skip hlt h
  | .prod a b => by
    simp only [bvarShift, RefSet_prod] at h ⊢
    cases h
    next h => exact .inl $ bvarShift_RefSet_general_lt_rev skip hlt h
    next h => exact .inr $ bvarShift_RefSet_general_lt_rev skip hlt h
  | .fst expr => by
    simp only [bvarShift, RefSet_fst] at h ⊢
    exact bvarShift_RefSet_general_lt_rev skip hlt h
  | .snd expr => by
    simp only [bvarShift, RefSet_snd] at h ⊢
    exact bvarShift_RefSet_general_lt_rev skip hlt h

theorem bvarShift_range
    {shift skip n}
    : {x : _}
    → RefSet (bvarShift shift skip x) n
    → (n < skip ∨ shift + skip ≤ n)
  | .bvar x, .bvar => by grind
  | .abs ty body, .abs h => by
    cases bvarShift_range (skip := skip.succ) h
    <;> grind
  | .app fn arg, .app_fn h | .app fn arg, .app_arg h => by
    have := bvarShift_range h
    grind
  | .prod a b, .prod_fst h | .prod a b, .prod_snd h => by
    have := bvarShift_range h
    grind
  | .fst expr, .fst h => by
    have := bvarShift_range h
    grind
  | .snd expr, .snd h => by
    have := bvarShift_range h
    grind

theorem replace_RefSet_general_lt_rev
    {repl idx jdx}
    (hlt : idx < jdx)
    : {body : Stx} → RefSet (body.replace jdx repl) idx
    → RefSet body idx
  | .bvar x, h => by
    simp only [replace, replace.bvar, Nat.pred_eq_sub_one] at h
    split at h
    <;> simp_all only [Std.LawfulEqCmp.compare_eq_iff_eq, RefSet_bvar, Nat.compare_eq_gt]
    · have := bvarShift_range h
      omega
    · omega
  | .abs ty body, .abs h => RefSet_abs.mpr
    <| replace_RefSet_general_lt_rev (Nat.add_lt_add_right hlt 1) h
  | .app fn arg, .app_fn h => RefSet_app.mpr
    <| .inl <| replace_RefSet_general_lt_rev hlt h
  | .app fn arg, .app_arg h => RefSet_app.mpr
    <| .inr <| replace_RefSet_general_lt_rev hlt h
  | .prod a b, .prod_fst h => RefSet_prod.mpr
    <| .inl <| replace_RefSet_general_lt_rev hlt h
  | .prod a b, .prod_snd h => RefSet_prod.mpr
    <| .inr <| replace_RefSet_general_lt_rev hlt h
  | .fst expr, .fst h => RefSet_fst.mpr
    <| replace_RefSet_general_lt_rev hlt h
  | .snd expr, .snd h => RefSet_snd.mpr
    <| replace_RefSet_general_lt_rev hlt h

theorem replace_RefSet_general_ge_rev
    {repl idx jdx}
    (hlt : jdx ≤ idx)
    : {body : Stx} → RefSet (body.replace jdx repl) idx
    → (RefSet body idx.succ ∨ RefSet repl (idx - jdx))
  | .bvar x, h => by
    simp only [replace, replace.bvar, Nat.pred_eq_sub_one] at h
    split at h
    <;> simp_all only [Std.LawfulEqCmp.compare_eq_iff_eq, RefSet_bvar,
      Nat.compare_eq_gt, Nat.compare_eq_lt]
    any_goals grind
    exact .inr <| bvarShift_RefSet_general_rev' _ (by omega) h
  | .abs ty body, .abs h => by
    simp only [Nat.succ_eq_add_one, RefSet_abs] at *
    have := replace_RefSet_general_ge_rev (Nat.add_le_add_right hlt 1) h
    simp_all only [Nat.reduceSubDiff]
  | .app fn arg, .app_fn h
  | .app fn arg, .app_arg h => by
    simp only [Nat.succ_eq_add_one, RefSet_app]
    cases replace_RefSet_general_ge_rev hlt h
    <;> simp_all
  | .prod a b, .prod_fst h
  | .prod a b, .prod_snd h => by
    simp only [Nat.succ_eq_add_one, RefSet_prod]
    cases replace_RefSet_general_ge_rev hlt h
    <;> simp_all
  | .fst expr, .fst h => by
    simp only [Nat.succ_eq_add_one, RefSet_fst]
    cases replace_RefSet_general_ge_rev hlt h
    <;> simp_all
  | .snd expr, .snd h => by
    simp only [Nat.succ_eq_add_one, RefSet_snd]
    cases replace_RefSet_general_ge_rev hlt h
    <;> simp_all

end Stx

end STLCFull
