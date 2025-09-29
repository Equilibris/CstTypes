import Types.Expr.Repl
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
example : bvarShift k 0 (.tlam (.id 0)) = (.tlam $ .id 0)                      := by simp [bvarShift]
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
    rw [h]
    clear h
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
    simp only [bvarShift, Nat.succ_eq_add_one, RefSet_tlam] at h ⊢
    rw [Nat.add_assoc] at h
    exact bvarShift_RefSet_general_rev (skip + 1) h
  | .app a b => by
    simp only [bvarShift, RefSet_app] at h ⊢
    cases h
    next h => exact .inl $ bvarShift_RefSet_general_rev skip h
    next h => exact .inr $ bvarShift_RefSet_general_rev skip h
  | .tapp expr ty => by
    simp only [bvarShift, RefSet_tapp] at h ⊢
    exact bvarShift_RefSet_general_rev skip h

example {n} : RefSet (.lam [t|0] (.id (n + 1))) n := .lam .id
example {n} : RefSet (.tlam (.id (n + 1))) n := .tlam .id

theorem bvarShift_RefSet_rev
    {body idx shift}
    (h : RefSet (body.bvarShift shift 0) (idx + shift))
    : RefSet body idx :=
  bvarShift_RefSet_general_rev 0 h

end Expr
