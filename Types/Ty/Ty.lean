import Types.TStx

namespace Ty

-- Validity predicate for types with De Bruijn indices
inductive Valid : Ty → Nat → Prop
  | id {n idx} : idx < n → Valid (.id idx) n
  | fn {n a b} : Valid a n → Valid b n → Valid (Ty.fn a b) n
  | fa {n t} : Valid t (n + 1) → Valid (fa t) n

def ifree (cutoff : Nat) (inc : Nat) : Ty → Ty
  | Ty.id idx => .id (if idx >= cutoff then (idx + inc) else idx)
  | .fn a b => .fn (ifree cutoff inc a) (ifree cutoff inc b)
  | .fa t => .fa (ifree cutoff.succ inc t)

example : [t|0].ifree 0 2 = [t|2] := rfl
example : [t|0].ifree 1 3 = [t|0] := rfl
example : [t|1].ifree 1 2 = [t|3] := rfl
example : [t|0 → 1].ifree 0 1 = [t|1 → 2] := rfl
example : [t|0 → 2].ifree 1 2 = [t|0 → 4] := rfl
example : [t|Λ. 0 → 0].ifree 0 1 = [t|Λ. 0 → 0] := rfl
example : [t|Λ. 0 → 1].ifree 0 1 = [t|Λ. 0 → 2] := rfl

-- Proof that ifree maintains validity
theorem Valid_ifree_Valid {n cutoff inc : Nat}
    : {t : Ty} → Valid t n → Valid (ifree cutoff inc t) (n + inc)
  | .id i, .id h => .id (by split <;> omega)
  | .fn _ _, .fn ha hb => .fn (Valid_ifree_Valid ha) (Valid_ifree_Valid hb)
  | .fa _, .fa h => .fa <| by
    rw [show n + inc + 1 = n + 1 + inc by omega]
    exact (Valid_ifree_Valid h)

def subst (skip idx : Nat) (body replacement : Ty) : Ty :=
  match body with
  | Ty.id i =>
    if i = idx then
      ifree 0 skip replacement
    else if i > idx then
      Ty.id (i - 1)
    else
      Ty.id i
  | Ty.fn a b => .fn (subst skip idx a replacement) (subst skip idx b replacement)
  | Ty.fa t => .fa <| subst skip.succ idx.succ t replacement

example : [t|0].subst 0 0 [t|0 → 0] = [t|0 → 0] := rfl
example : [t|0].subst 0 1 [t|0 → 0] = [t|0] := rfl
example : [t|Λ. 0 → 1].subst 0 0 [t|0 → 0] = [t|Λ. 0 → (1 → 1)] := rfl

-- Proof that subst maintains validity
theorem Valid_subst_Valid {n m skip idx : Nat} {replacement : Ty}
    (h_repl : Valid replacement m)
    : {body : Ty} → Valid body (n + m + 1)
    → Valid (subst skip idx body replacement) (n + m)
  | .id i, .id h => by
    dsimp [subst]
    split
    case isTrue h_eq =>
      have h_ifree : Valid (ifree 0 skip replacement) (m + skip) := Valid_ifree_Valid h_repl
      rw [show m + skip = n + m by omega] at h_ifree
      exact h_ifree
    case isFalse h_ne =>
      split
      case h_gt => exact .id (by omega)
      case h_le => exact .id (by omega)
  | .fn _ _, .fn ha hb => .fn (Valid_subst_Valid h_repl ha) (Valid_subst_Valid h_repl hb)
  | .fa _, .fa h => .fa <| by
    rw [show n + m + 1 = n + m + 1 by rfl]
    exact Valid_subst_Valid h_repl h

-- RefSet predicate for types
inductive RefSet : Ty → ℕ → Prop
  | fnL : RefSet a idx → RefSet (.fn a b) idx
  | fnR : RefSet b idx → RefSet (.fn a b) idx
  | fa : RefSet body idx.succ → RefSet (.fa body) idx
  | id : RefSet (.id idx) idx

@[simp]
theorem RefSet_fa : RefSet (.fa body) idx ↔ RefSet body (idx + 1) := by
  constructor
  <;> intro h
  · cases h; assumption
  · exact .fa h

@[simp]
theorem RefSet_fn : RefSet (.fn a b) idx ↔ (RefSet a idx ∨ RefSet b idx) := by
  constructor
  <;> rintro (h|h)
  · exact .inl h
  · exact .inr h
  · exact .fnL h
  · exact .fnR h

@[simp]
theorem RefSet_id : RefSet (.id idx) jdx ↔ idx = jdx := by
  constructor
  <;> intro h
  · cases h; rfl
  · rw [h]
    exact .id

example : RefSet (.fa (.fn (.id 1) (.id 0))) 0 := .fa (.fnR .id)
example : ¬∃ n, RefSet (.fa (.id 0)) n := by
  rintro ⟨n, _|_|_⟩
example : ¬∃ n, RefSet (.fa (.id 0)) n := by
  intro ⟨n, x⟩ ; simp only [RefSet_fa, RefSet_id] at x

lemma RefSet_dist : RefSet (.fa (.fn a b)) idx ↔ RefSet (.fa a) idx ∨ RefSet (.fa b) idx := by
  constructor
  <;> intro h
  <;> simp only [RefSet_fa, RefSet_fn] at h ⊢
  <;> exact h

end Ty
