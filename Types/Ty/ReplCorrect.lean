import Types.Ty.Repl
import Types.Ty.RefSet

namespace Ty

/-- Proof of correctness for bvarShift's shifting -/
@[simp]
theorem bvarUnShift_bvarShift {shift skip s} : bvarUnShift shift skip (bvarShift shift skip s) = s := by
  induction s generalizing shift skip
  <;> simp [bvarShift, bvarUnShift]
  case id n => split <;> split <;> omega
  case fn fn_ih arg_ih => exact ⟨fn_ih, arg_ih⟩
  case fa body_ih => exact body_ih

variable {n k} in
section
example : bvarShift k 0 (.id n) = (.id (n + k))                     := by simp [bvarShift]
example : bvarShift k (.succ n) (.id 0) = (.id 0)                   := by simp [bvarShift]
example : bvarShift k 0 (.fa (.id 0)) = (.fa $ .id 0)               := by simp [bvarShift]
example : bvarShift k 0 (.fa (.id 1)) = (.fa $ .id (1 + k))         := by simp [bvarShift]
end

@[simp]
theorem bvarShift.inv {n z} : bvarShift 0 n z = z := by
  induction z generalizing n
  <;> dsimp only [bvarShift]
  case id => split <;> rfl
  case fn fn_ih arg_ih =>
    simp only [Ty.fn.injEq]
    exact ⟨fn_ih, arg_ih⟩
  case fa body ih=>
    simp only [Ty.fa.injEq]
    exact ih

theorem bvarShift_RefSet_general {body idx skip shift} (h : RefSet body (idx + skip)) : RefSet (body.bvarShift shift skip) (idx + shift + skip) :=
  match body with
  | .id n => by
    simp at h
    rw [h]
    clear h
    simp [bvarShift]
    split <;> omega
  | .fa body => by
    simp_all [bvarShift]
    exact bvarShift_RefSet_general h
  | .fn a b => by
    simp only [RefSet_fn, bvarShift] at h ⊢
    cases h
    next h => exact .inl $ bvarShift_RefSet_general h
    next h => exact .inr $ bvarShift_RefSet_general h

theorem bvarShift_RefSet {body idx shift} (h : RefSet body idx) : RefSet (body.bvarShift shift 0) (idx + shift) :=
  bvarShift_RefSet_general h

theorem bvarShift_RefSet_general_rev {body idx shift}
    skip (h : RefSet (body.bvarShift shift skip) (idx + shift + skip))
    : RefSet body (idx + skip) :=
  match body with
  | .id n => by
    simp_all [bvarShift]
    split at h <;> omega
  | .fa body => by
    simp only [bvarShift, Nat.succ_eq_add_one, RefSet_fa] at h ⊢
    rw [Nat.add_assoc] at h
    exact bvarShift_RefSet_general_rev (skip + 1) h
  | .fn a b => by
    simp only [bvarShift, RefSet_fn] at h ⊢
    cases h
    next h => exact .inl $ bvarShift_RefSet_general_rev skip h
    next h => exact .inr $ bvarShift_RefSet_general_rev skip h

example {n} : RefSet (.fa (.id (n + 1))) n := .fa .id

theorem bvarShift_RefSet_rev
    {body idx shift}
    (h : RefSet (body.bvarShift shift 0) (idx + shift))
    : RefSet body idx :=
  bvarShift_RefSet_general_rev 0 h
