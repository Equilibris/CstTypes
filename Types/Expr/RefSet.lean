import Types.Expr.Stx

namespace Expr

-- RefSet predicate for expressions
inductive RefSet : Expr → Nat → Prop
  | appL {a b idx} : RefSet a idx → RefSet (.app a b) idx
  | appR {a b idx} : RefSet b idx → RefSet (.app a b) idx
  | lam {ty body idx} : RefSet body idx.succ → RefSet (.lam ty body) idx
  | tappL {expr ty idx} : RefSet expr idx → RefSet (.tapp expr ty) idx
  | tlam {body idx} : RefSet body idx.succ → RefSet (.tlam body) idx
  | id {idx} : RefSet (.id idx) idx

@[simp]
theorem RefSet_lam {ty body idx} : RefSet (.lam ty body) idx ↔ RefSet body (idx + 1) := by
  constructor
  <;> intro h
  · cases h; assumption
  · exact .lam h

@[simp]
theorem RefSet_tlam {body idx} : RefSet (.tlam body) idx ↔ RefSet body (idx + 1) := by
  constructor
  <;> intro h
  · cases h; assumption
  · exact .tlam h

@[simp]
theorem RefSet_app {a b idx} : RefSet (.app a b) idx ↔ (RefSet a idx ∨ RefSet b idx) := by
  constructor
  <;> rintro (h|h)
  · exact .inl h
  · exact .inr h
  · exact .appL h
  · exact .appR h

@[simp]
theorem RefSet_tapp {expr ty idx} : RefSet (.tapp expr ty) idx ↔ RefSet expr idx := by
  constructor
  <;> intro h
  · cases h; assumption
  · exact .tappL h

@[simp]
theorem RefSet_id {idx jdx} : RefSet (.id idx) jdx ↔ idx = jdx := by
  constructor
  <;> intro h
  · cases h; rfl
  · rw [h]
    exact .id

example : RefSet (.lam [t|0] (.app (.id 1) (.id 0))) 0 := .lam (.appL .id)
example : ¬∃ n, RefSet (.lam [t|0] (.id 0)) n := by simp
example : ¬∃ n, RefSet (.lam [t|0] (.id 0)) n := by simp

theorem RefSet_dist_app {ty a b idx} : RefSet (.lam ty (.app a b)) idx ↔ RefSet (.lam ty a) idx ∨ RefSet (.lam ty b) idx := by
  constructor
  <;> intro h
  <;> simp only [RefSet_lam, RefSet_app] at h ⊢
  <;> exact h

theorem RefSet_dist_tlam {a b idx} : RefSet (.tlam (.app a b)) idx ↔ RefSet (.tlam a) idx ∨ RefSet (.tlam b) idx := by
  constructor
  <;> intro h
  <;> simp only [RefSet_tlam, RefSet_app] at h ⊢
  <;> exact h

end Expr
