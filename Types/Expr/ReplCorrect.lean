import Types.Expr.Repl
import Types.Expr.TReplCorrect
import Types.Expr.RefSet

namespace Expr

/-- Proof of correctness for bvarShift's shifting -/
@[simp]
theorem bvarUnShift_bvarShift {shift skip s} : bvarUnShift shift skip (bvarShift shift skip s) = s := by
  induction s generalizing shift skip
  <;> simp [bvarShift, bvarUnShift]
  case id n => split <;> split <;> omega
  case app fn_ih arg_ih => exact ⟨fn_ih, arg_ih⟩
  case lam ty body_ih => exact body_ih
  case tapp expr_ih => exact expr_ih
  case tlam body_ih => exact body_ih

variable {n k} in
section
example : bvarShift k 0 (.id n) = (.id (n + k))                                := by simp [bvarShift]
example : bvarShift k (.succ n) (.id 0) = (.id 0)                              := by simp [bvarShift]
example : bvarShift k 0 (.lam [t|0] (.id 0)) = (.lam [t|0] $ .id 0)            := by simp [bvarShift]
example : bvarShift k 0 (.lam [t|0] (.id 1)) = (.lam [t|0] $ .id (1 + k))      := by simp [bvarShift]
example : bvarShift k 0 (.tlam (.id 0)) = (.tlam $ .id k)                      := by simp [bvarShift]
example : bvarShift k 0 (.tlam (.id 1)) = (.tlam $ .id (1 + k))                := by simp [bvarShift]
end

@[simp]
theorem bvarShift.inv {n z} : bvarShift 0 n z = z := by
  induction z generalizing n
  <;> dsimp only [bvarShift]
  case id => split <;> rfl
  case app fn_ih arg_ih =>
    simp only [Expr.app.injEq]
    exact ⟨fn_ih, arg_ih⟩
  case lam ty body_ih =>
    simp only [lam.injEq, true_and]
    exact body_ih
  case tapp expr_ih =>
    simp only [tapp.injEq, and_true]
    exact expr_ih
  case tlam body_ih =>
    simp only [Expr.tlam.injEq]
    exact body_ih

theorem bvarShift_RefSet_general {body idx skip shift} (h : RefSet body (idx + skip)) : RefSet (body.bvarShift shift skip) (idx + shift + skip) :=
  match body with
  | .id n => by
    simp at h
    subst h
    simp [bvarShift]
    split <;> omega
  | .lam ty body => by
    simp_all [bvarShift]
    exact bvarShift_RefSet_general h
  | .tlam body => by
    simp_all [bvarShift]
    exact bvarShift_RefSet_general h
  | .app a b => by
    simp only [RefSet_app, bvarShift] at h ⊢
    cases h
    next h => exact .inl $ bvarShift_RefSet_general h
    next h => exact .inr $ bvarShift_RefSet_general h
  | .tapp expr ty => by
    simp only [RefSet_tapp, bvarShift] at h ⊢
    exact bvarShift_RefSet_general h

theorem bvarShift_RefSet {body idx shift} (h : RefSet body idx) : RefSet (body.bvarShift shift 0) (idx + shift) :=
  bvarShift_RefSet_general h

theorem bvarShift_RefSet_general_rev {body idx shift}
    skip (h : RefSet (body.bvarShift shift skip) (idx + shift + skip))
    : RefSet body (idx + skip) :=
  match body with
  | .id n => by
    simp_all [bvarShift]
    split at h <;> omega
  | .lam ty body => by
    simp only [bvarShift, Nat.succ_eq_add_one, RefSet_lam] at h ⊢
    rw [Nat.add_assoc] at h
    exact bvarShift_RefSet_general_rev (skip + 1) h
  | .tlam body => by
    simp only [bvarShift, RefSet_tlam] at h ⊢
    exact bvarShift_RefSet_general_rev skip h
  | .app a b => by
    simp only [bvarShift, RefSet_app] at h ⊢
    cases h
    next h => exact .inl $ bvarShift_RefSet_general_rev skip h
    next h => exact .inr $ bvarShift_RefSet_general_rev skip h
  | .tapp expr ty => by
    simp only [bvarShift, RefSet_tapp] at h ⊢
    exact bvarShift_RefSet_general_rev skip h

example {n} : RefSet (.lam [t|0] (.id (n + 1))) n := .lam .id
example {n} : RefSet (.tlam (.id n)) n := .tlam .id

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
  | .id n => by
    simp_all only [bvarShift, RefSet_id]
    split at h <;> omega
  | .lam ty body => by
    simp only [bvarShift, Nat.succ_eq_add_one, RefSet_lam] at h ⊢
    exact bvarShift_RefSet_general_lt_rev (skip + 1) (by omega) h
  | .tlam body => by
    simp only [bvarShift, RefSet_tlam] at h ⊢
    exact bvarShift_RefSet_general_lt_rev skip (by omega) h
  | .app a b => by
    simp only [bvarShift, RefSet_app] at h ⊢
    cases h
    next h => exact .inl $ bvarShift_RefSet_general_lt_rev skip hlt h
    next h => exact .inr $ bvarShift_RefSet_general_lt_rev skip hlt h
  | .tapp expr ty => by
    simp only [bvarShift, RefSet_tapp] at h ⊢
    exact bvarShift_RefSet_general_lt_rev skip hlt h

theorem bvarShift_range
    {shift skip n}
    : {x : _}
    → RefSet (bvarShift shift skip x) n
    → (n < skip ∨ shift + skip ≤ n)
  | .id x, .id => by grind
  | .lam ty body, .lam h => by
    cases bvarShift_range (skip := skip.succ) h
    <;> grind
  | .tlam body, .tlam h => by
    cases bvarShift_range h
    <;> grind
  | .app a b, .appL h | .app a b, .appR h => by
    have := bvarShift_range h
    grind
  | .tapp expr ty, .tappL h => by
    have := bvarShift_range h
    grind

theorem replace_RefSet_general_lt_rev
    {repl : Expr}
    {idx jdx ts}
    (hlt : idx < jdx)
    : {body : Expr} → RefSet (body.replace jdx ts repl) idx
    → RefSet body idx
  | .id x, h => by
    simp only [replace, replace.bvar, Nat.pred_eq_sub_one] at h
    split at h
    <;> simp_all only [Std.LawfulEqCmp.compare_eq_iff_eq, RefSet_id, Nat.compare_eq_gt]
    · have := bvarShift_range h
      omega
    · omega
  | .lam ty body, .lam h => RefSet_lam.mpr
    <| replace_RefSet_general_lt_rev (Nat.add_lt_add_right hlt 1) h
  | .tlam body, .tlam h => RefSet_tlam.mpr
    <| replace_RefSet_general_lt_rev hlt h
  | .app a b, .appL h => RefSet_app.mpr
    <| .inl <| replace_RefSet_general_lt_rev hlt h
  | .app a b, .appR h => RefSet_app.mpr
    <| .inr <| replace_RefSet_general_lt_rev hlt h
  | .tapp expr ty, .tappL h => RefSet_tapp.mpr
    <| replace_RefSet_general_lt_rev hlt h

theorem replace_RefSet_general_ge_rev
    {repl : Expr}
    {idx jdx ts}
    (hlt : jdx ≤ idx)
    : {body : Expr} → RefSet (body.replace jdx ts repl) idx
    → (RefSet body idx.succ ∨ RefSet repl (idx - jdx))
  | .id x, h => by
    simp only [replace, replace.bvar, Nat.pred_eq_sub_one] at h
    split at h
    <;> simp_all only [Std.LawfulEqCmp.compare_eq_iff_eq, RefSet_id,
      Nat.compare_eq_gt, Nat.compare_eq_lt]
    any_goals grind only
    exact .inr $ tBvarShift_RefSet.mp $ bvarShift_RefSet_general_rev' 0 (by omega) h
  | .lam ty body, .lam h => by
    simp only [Nat.succ_eq_add_one, RefSet_lam] at *
    have := replace_RefSet_general_ge_rev (Nat.add_le_add_right hlt 1) h
    simp_all only [Nat.reduceSubDiff]
  | .tlam body, .tlam h => by
    simp only [Nat.succ_eq_add_one, RefSet_tlam] at *
    exact replace_RefSet_general_ge_rev hlt h
  | .app a b, .appL h
  | .app a b, .appR h => by
    simp only [Nat.succ_eq_add_one, RefSet_app]
    cases replace_RefSet_general_ge_rev hlt h
    <;> simp_all
  | .tapp expr ty, .tappL h => by
    simp only [Nat.succ_eq_add_one, RefSet_tapp]
    cases replace_RefSet_general_ge_rev hlt h
    <;> simp_all

end Expr
