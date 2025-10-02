import Types.Expr.TRepl
import Types.Expr.TRefSet
import Types.Ty.ReplCorrect

namespace Expr

/-- Proof of correctness for tBvarShift's shifting -/
@[simp]
theorem tBvarUnShift_tBvarShift {shift skip s} : tBvarUnShift shift skip (tBvarShift shift skip s) = s := by
  induction s generalizing shift skip
  <;> simp only [tBvarShift, tBvarUnShift, Ty.bvarUnShift_bvarShift]
  <;> grind

variable {n k} in
section
example : tBvarShift k 0 (.id n) = (.id n)                                          := by simp [tBvarShift]
example : tBvarShift k 0 (.lam [t|0] (.id 0)) = (.lam (.id k) $ .id 0)              := by simp [tBvarShift, Ty.bvarShift]
example : tBvarShift k 0 (.lam [t|1] (.id 0)) = (.lam (.id (1 + k)) $ .id 0)        := by simp [tBvarShift, Ty.bvarShift]
example : tBvarShift k 0 (.tlam (.tapp (.id 0) [t|0])) = (.tlam $ .tapp (.id 0) [t|0]) := by simp [tBvarShift, Ty.bvarShift]
example : tBvarShift k 0 (.tlam (.tapp (.id 0) [t|1])) = (.tlam $ .tapp (.id 0) (.id $ 1 + k)) := by simp [tBvarShift, Ty.bvarShift]
end

@[simp]
theorem tBvarShift.inv {n z} : tBvarShift 0 n z = z := by
  induction z generalizing n
  <;> dsimp only [tBvarShift]
  case app fn_ih arg_ih =>
    simp only [Expr.app.injEq]
    exact ⟨fn_ih, arg_ih⟩
  case lam ty body_ih =>
    simp only [lam.injEq, Ty.bvarShift.inv, true_and]
    exact body_ih
  case tapp expr_ih =>
    simp only [tapp.injEq, Ty.bvarShift.inv, and_true]
    exact expr_ih
  case tlam body_ih =>
    simp only [Expr.tlam.injEq]
    exact body_ih

theorem tBvarShift_TRefSet_general {body idx skip shift} (h : TRefSet body (idx + skip)) : TRefSet (body.tBvarShift shift skip) (idx + shift + skip) :=
  match body with
  | .id n => by
    simp at h
  | .lam ty body => by
    simp only [TRefSet_lam, tBvarShift] at h ⊢
    cases h
    next h => exact .inl $ Ty.bvarShift_RefSet_general h
    next h => exact .inr $ tBvarShift_TRefSet_general h
  | .tlam body => by
    simp_all [tBvarShift]
    exact tBvarShift_TRefSet_general h
  | .app a b => by
    simp only [TRefSet_app, tBvarShift] at h ⊢
    cases h
    next h => exact .inl $ tBvarShift_TRefSet_general h
    next h => exact .inr $ tBvarShift_TRefSet_general h
  | .tapp expr ty => by
    simp only [TRefSet_tapp, tBvarShift] at h ⊢
    cases h
    next h => exact .inl $ tBvarShift_TRefSet_general h
    next h => exact .inr $ Ty.bvarShift_RefSet_general h

theorem tBvarShift_TRefSet {body idx shift} (h : TRefSet body idx) : TRefSet (body.tBvarShift shift 0) (idx + shift) :=
  tBvarShift_TRefSet_general h

theorem tBvarShift_TRefSet_general_rev {body idx shift}
    skip (h : TRefSet (body.tBvarShift shift skip) (idx + shift + skip))
    : TRefSet body (idx + skip) :=
  match body with
  | .id n => by
    simp_all [tBvarShift]
  | .lam ty body => by
    simp only [tBvarShift, TRefSet_lam] at h ⊢
    cases h
    next h => exact .inl $ Ty.bvarShift_RefSet_general_rev skip h
    next h => exact .inr $ tBvarShift_TRefSet_general_rev skip h
  | .tlam body => by
    simp only [tBvarShift, Nat.succ_eq_add_one, TRefSet_tlam] at h ⊢
    rw [Nat.add_assoc] at h
    exact tBvarShift_TRefSet_general_rev (skip + 1) h
  | .app a b => by
    simp only [tBvarShift, TRefSet_app] at h ⊢
    cases h
    next h => exact .inl $ tBvarShift_TRefSet_general_rev skip h
    next h => exact .inr $ tBvarShift_TRefSet_general_rev skip h
  | .tapp expr ty => by
    simp only [tBvarShift, TRefSet_tapp] at h ⊢
    cases h
    next h => exact .inl $ tBvarShift_TRefSet_general_rev skip h
    next h => exact .inr $ Ty.bvarShift_RefSet_general_rev skip h

example {n} : TRefSet (.lam [t|0] (.id (n + 1))) 0          := .lamT .id
example {n} : TRefSet (.tlam (.tapp (.id 0) (.id $ n+1))) n := .tlam (.tappR .id)

theorem tBvarShift_TRefSet_rev
    {body idx shift}
    (h : TRefSet (body.tBvarShift shift 0) (idx + shift))
    : TRefSet body idx :=
  tBvarShift_TRefSet_general_rev 0 h

theorem tBvarShift_TRefSet_general_rev' {body idx shift}
    skip
    (hlt : skip + shift ≤ idx)
    (h : TRefSet (body.tBvarShift shift skip) idx)
    : TRefSet body (idx - shift) := by
  obtain ⟨idx', rfl⟩ := Nat.exists_eq_add_of_le hlt
  rw [show skip + shift + idx' = idx' + shift + skip by omega] at h
  rw [show (skip + shift + idx' - shift) = idx' + skip by omega]
  exact tBvarShift_TRefSet_general_rev skip h

theorem tBvarShift_TRefSet_general_lt_rev {body idx shift}
    skip
    (hlt : idx < skip + shift)
    (h : TRefSet (body.tBvarShift shift skip) idx)
    : TRefSet body idx :=
  match body with
  | .id n => by
    simp_all [tBvarShift]
  | .lam ty body => by
    simp only [tBvarShift, TRefSet_lam] at h ⊢
    cases h
    next h => exact .inl $ Ty.bvarShift_RefSet_general_lt_rev skip hlt h
    next h => exact .inr $ tBvarShift_TRefSet_general_lt_rev skip hlt h
  | .tlam body => by
    simp [tBvarShift, Nat.succ_eq_add_one, TRefSet_tlam] at h ⊢
    exact tBvarShift_TRefSet_general_lt_rev (skip + 1) (by omega) h
  | .app a b => by
    simp only [tBvarShift, TRefSet_app] at h ⊢
    cases h
    next h => exact .inl $ tBvarShift_TRefSet_general_lt_rev skip hlt h
    next h => exact .inr $ tBvarShift_TRefSet_general_lt_rev skip hlt h
  | .tapp expr ty => by
    simp only [tBvarShift, TRefSet_tapp] at h ⊢
    cases h
    next h => exact .inl $ tBvarShift_TRefSet_general_lt_rev skip hlt h
    next h => exact .inr $ Ty.bvarShift_RefSet_general_lt_rev skip hlt h

theorem tBvarShift_range
    {shift skip n}
    : {x : _}
    → TRefSet (tBvarShift shift skip x) n
    → (n < skip ∨ shift + skip ≤ n)
  | .id x, h => by cases h
  | .lam ty body, .lamT h => by
    have := Ty.bvarShift_range h
    grind
  | .lam ty body, .lamB h => by
    have := tBvarShift_range h
    grind
  | .tlam body, .tlam h => by
    cases tBvarShift_range (skip := skip.succ) h
    <;> grind
  | .app a b, .appL h | .app a b, .appR h => by
    have := tBvarShift_range h
    grind
  | .tapp expr ty, .tappL h => by
    have := tBvarShift_range h
    grind
  | .tapp expr ty, .tappR h => by
    have := Ty.bvarShift_range h
    grind

theorem tReplace_TRefSet_general_lt_rev
    {repl : Ty}
    {idx jdx}
    (hlt : idx < jdx)
    : {body : Expr} → TRefSet (body.tReplace jdx repl) idx
    → TRefSet body idx
  | .id x, h => by cases h
  | .lam ty body, .lamT h => TRefSet_lam.mpr
    <| .inl <| Ty.replace_RefSet_general_lt_rev hlt h
  | .lam ty body, .lamB h => TRefSet_lam.mpr
    <| .inr <| tReplace_TRefSet_general_lt_rev hlt h
  | .tlam body, .tlam h => TRefSet_tlam.mpr
    <| tReplace_TRefSet_general_lt_rev (Nat.add_lt_add_right hlt 1) h
  | .app a b, .appL h => TRefSet_app.mpr
    <| .inl <| tReplace_TRefSet_general_lt_rev hlt h
  | .app a b, .appR h => TRefSet_app.mpr
    <| .inr <| tReplace_TRefSet_general_lt_rev hlt h
  | .tapp expr ty, .tappL h => TRefSet_tapp.mpr
    <| .inl <| tReplace_TRefSet_general_lt_rev hlt h
  | .tapp expr ty, .tappR h => TRefSet_tapp.mpr
    <| .inr <| Ty.replace_RefSet_general_lt_rev hlt h

theorem tReplace_TRefSet_general_ge_rev
    {repl : Ty}
    {idx jdx}
    (hlt : jdx ≤ idx)
    : {body : Expr} → TRefSet (body.tReplace jdx repl) idx
    → (TRefSet body idx.succ ∨ Ty.RefSet repl (idx - jdx))
  | .id x, h => by cases h
  | .lam ty body, .lamT h => by
    simp only [Nat.succ_eq_add_one, TRefSet_lam]
    cases Ty.replace_RefSet_general_ge_rev hlt h
    <;> simp_all
  | .lam ty body, .lamB h => by
    simp only [Nat.succ_eq_add_one, TRefSet_lam] at *
    have := tReplace_TRefSet_general_ge_rev hlt h
    grind only
  | .tlam body, .tlam h => by
    simp only [Nat.succ_eq_add_one, TRefSet_tlam] at *
    have := tReplace_TRefSet_general_ge_rev (Nat.add_le_add_right hlt 1) h
    simp_all only [Nat.reduceSubDiff]
  | .app a b, .appL h
  | .app a b, .appR h => by
    simp only [Nat.succ_eq_add_one, TRefSet_app]
    cases tReplace_TRefSet_general_ge_rev hlt h
    <;> simp_all
  | .tapp expr ty, .tappL h => by
    simp only [Nat.succ_eq_add_one, TRefSet_tapp]
    cases tReplace_TRefSet_general_ge_rev hlt h
    <;> simp_all
  | .tapp expr ty, .tappR h => by
    simp only [Nat.succ_eq_add_one, TRefSet_tapp]
    cases Ty.replace_RefSet_general_ge_rev hlt h
    <;> simp_all

end Expr
