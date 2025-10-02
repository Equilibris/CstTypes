import Types.Ty.Repl
import Types.Ty.RefSet

namespace Ty

/-- Proof of correctness for bvarShift's shifting -/
@[simp]
theorem bvarUnShift_bvarShift {shift skip s} : bvarUnShift shift skip (bvarShift shift skip s) = s := by
  induction s generalizing shift skip
  <;> simp [bvarShift, bvarUnShift]
  case id n => grind
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
    simp only [RefSet_id] at h
    subst h
    simp only [bvarShift, RefSet_id]
    grind
  | .fa body => by
    simp_all only [RefSet_fa, bvarShift]
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

theorem bvarShift_RefSet_general_rev' {body idx shift}
    skip
    (hlt : skip + shift ≤ idx)
    (h : RefSet (body.bvarShift shift skip) idx)
    : RefSet body (idx - shift) := by
  obtain ⟨idx, rfl⟩ := Nat.exists_eq_add_of_le hlt
  rw [show skip + shift + idx = idx + shift + skip by omega] at h
  rw [show (skip + shift + idx - shift) = idx + skip by omega]
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
  | .fa body => by
    simp only [bvarShift, Nat.succ_eq_add_one, RefSet_fa] at h ⊢
    exact bvarShift_RefSet_general_lt_rev (skip + 1) (by omega) h
  | .fn a b => by
    simp only [bvarShift, RefSet_fn] at h ⊢
    cases h
    next h => exact .inl $ bvarShift_RefSet_general_lt_rev skip hlt h
    next h => exact .inr $ bvarShift_RefSet_general_lt_rev skip hlt h

theorem bvarShift_range
    {shift skip n}
    : {x : _}
    → RefSet (bvarShift shift skip x) n
    → (n < skip ∨ shift + skip ≤ n)
  | .id x, .id => by grind only []
  | .fa x, .fa h => by
    cases bvarShift_range (skip := skip.succ) h
    <;> grind only
  | .fn a b, .fnL h | .fn a b, .fnR h => by
    have := bvarShift_range h
    grind only

theorem replace_RefSet_general_lt_rev
    {repl idx jdx}
    (hlt : idx < jdx)
    : {body : Ty} → RefSet (body.replace jdx repl) idx
    → RefSet body idx
  | .id x, h => by
    simp only [replace, replace.bvar, Nat.pred_eq_sub_one] at h
    split at h
    <;> simp_all only [Std.LawfulEqCmp.compare_eq_iff_eq, RefSet_id, Nat.compare_eq_gt]
    · have := bvarShift_range h
      omega
    · omega
  | .fa b, .fa h => RefSet_fa.mpr
    <| replace_RefSet_general_lt_rev (Nat.add_lt_add_right hlt 1) h
  | .fn a b, .fnL h => RefSet_fn.mpr
    <| .inl <| replace_RefSet_general_lt_rev hlt h
  | .fn a b, .fnR h => RefSet_fn.mpr
    <| .inr <| replace_RefSet_general_lt_rev hlt h

theorem replace_RefSet_general_ge_rev
    {repl idx jdx}
    (hlt : jdx ≤ idx)
    : {body : Ty} → RefSet (body.replace jdx repl) idx
    → (RefSet body idx.succ ∨ RefSet repl (idx - jdx))
  | .id x, h => by
    simp only [replace, replace.bvar, Nat.pred_eq_sub_one] at h
    split at h
    <;> simp_all only [Std.LawfulEqCmp.compare_eq_iff_eq, RefSet_id,
      Nat.compare_eq_gt, Nat.compare_eq_lt]
    any_goals grind only
    exact .inr <| bvarShift_RefSet_general_rev' _ (by omega) h
  | .fa x, .fa h => by
    simp only [Nat.succ_eq_add_one, RefSet_fa] at *
    have := replace_RefSet_general_ge_rev (Nat.add_le_add_right hlt 1) h
    simp_all only [Nat.reduceSubDiff]
  | .fn a b, .fnL h
  | .fn a b, .fnR h => by
    simp only [Nat.succ_eq_add_one, RefSet_fn]
    cases replace_RefSet_general_ge_rev hlt h
    <;> simp_all

