import Types.Ty.Stx

-- RefSet predicate for types
inductive RefSet : Ty → Nat → Prop
  | fnL {a b idx} : RefSet a idx → RefSet (.fn a b) idx
  | fnR {a b idx} : RefSet b idx → RefSet (.fn a b) idx
  | fa {body idx} : RefSet body idx.succ → RefSet (.fa body) idx
  | id {idx} : RefSet (.id idx) idx

@[simp]
theorem RefSet_fa {body idx} : RefSet (.fa body) idx ↔ RefSet body (idx + 1) := by
  constructor
  <;> intro h
  · cases h; assumption
  · exact .fa h

@[simp]
theorem RefSet_fn {a b idx} : RefSet (.fn a b) idx ↔ (RefSet a idx ∨ RefSet b idx) := by
  constructor
  <;> rintro (h|h)
  · exact .inl h
  · exact .inr h
  · exact .fnL h
  · exact .fnR h

@[simp]
theorem RefSet_id {idx jdx} : RefSet (.id idx) jdx ↔ idx = jdx := by
  constructor
  <;> intro h
  · cases h; rfl
  · rw [h]
    exact .id

theorem RefSet_fa {a b idx} : RefSet (.fa (.fn a b)) idx ↔ RefSet (.fa a) idx ∨ RefSet (.fa b) idx := by
  constructor
  <;> intro h
  <;> simp only [RefSet_fa, RefSet_fn] at h ⊢
  <;> exact h
