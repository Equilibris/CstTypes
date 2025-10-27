import Types.SysF.Ty.Stx

namespace Ty

-- RefSet predicate for types
@[grind]
inductive RefSet : Ty → Nat → Prop
  | fnL {a b idx} : RefSet a idx → RefSet (.fn a b) idx
  | fnR {a b idx} : RefSet b idx → RefSet (.fn a b) idx
  | fa {body idx} : RefSet body idx.succ → RefSet (.fa body) idx
  | id {idx} : RefSet (.id idx) idx

@[simp]
theorem RefSet_fa {body idx} : RefSet (.fa body) idx ↔ RefSet body (idx + 1) := by
  grind

@[simp]
theorem RefSet_fn {a b idx} : RefSet (.fn a b) idx ↔ (RefSet a idx ∨ RefSet b idx) := by
  grind

@[simp]
theorem RefSet_id {idx jdx} : RefSet (.id idx) jdx ↔ idx = jdx := by
  grind

theorem RefSet_dist {a b idx} : RefSet (.fa (.fn a b)) idx ↔ RefSet (.fa a) idx ∨ RefSet (.fa b) idx := by
  grind

instance RefSet.dec : {t : Ty} → {n : Nat} → Decidable (RefSet t n)
  | .id x, v => if h : x = v then .isTrue <| h ▸ .id
    else .isFalse $ by simpa
  | .fa b, v => match @RefSet.dec b v.succ with
    | .isTrue h => .isTrue <| .fa h
    | .isFalse h => .isFalse <| by simpa
  | .fn a b, v =>
    match @RefSet.dec a v, @RefSet.dec b v with
    | .isTrue h, _ => .isTrue <| .fnL h
    | _, .isTrue h => .isTrue <| .fnR h
    | .isFalse h₁, .isFalse h₂ => .isFalse $ by simp_all

