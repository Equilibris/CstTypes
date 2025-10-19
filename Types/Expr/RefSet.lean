import Types.Expr.Stx

namespace Expr

-- RefSet predicate for expressions
@[grind]
inductive RefSet : Expr → Nat → Prop
  | appL {a b idx} : RefSet a idx → RefSet (.app a b) idx
  | appR {a b idx} : RefSet b idx → RefSet (.app a b) idx
  | lam {ty body idx} : RefSet body idx.succ → RefSet (.lam ty body) idx
  | tappL {expr ty idx} : RefSet expr idx → RefSet (.tapp expr ty) idx
  | tlam {body idx} : RefSet body idx → RefSet (.tlam body) idx
  | id {idx} : RefSet (.id idx) idx

@[simp, grind =]
theorem RefSet_lam {ty body idx} : RefSet (.lam ty body) idx ↔ RefSet body (idx + 1) := by
  grind

@[simp, grind =]
theorem RefSet_tlam {body idx} : RefSet (.tlam body) idx ↔ RefSet body idx := by
  grind

@[simp, grind =]
theorem RefSet_app {a b idx} : RefSet (.app a b) idx ↔ (RefSet a idx ∨ RefSet b idx) := by
  grind

@[simp, grind =]
theorem RefSet_tapp {expr ty idx} : RefSet (.tapp expr ty) idx ↔ RefSet expr idx := by
  grind

@[simp, grind =]
theorem RefSet_id {idx jdx} : RefSet (.id idx) jdx ↔ idx = jdx := by
  grind

example : RefSet (.lam [t|0] (.app (.id 1) (.id 0))) 0 := .lam (.appL .id)
example : ¬∃ n, RefSet (.lam [t|0] (.id 0)) n := by simp
example : ¬∃ n, RefSet (.lam [t|0] (.id 0)) n := by simp

theorem RefSet_dist_app {ty a b idx} : RefSet (.lam ty (.app a b)) idx ↔ RefSet (.lam ty a) idx ∨ RefSet (.lam ty b) idx := by
  grind

theorem RefSet_dist_tlam {a b idx} : RefSet (.tlam (.app a b)) idx ↔ RefSet (.tlam a) idx ∨ RefSet (.tlam b) idx := by
  grind

instance RefSet.dec : {e : Expr} → {n : Nat} → Decidable (RefSet e n)
  | .id x, v => if h : x = v then .isTrue <| h ▸ .id
    else .isFalse $ by simpa
  | .lam ty b, v => match @RefSet.dec b v.succ with
    | .isTrue h => .isTrue <| .lam h
    | .isFalse h => .isFalse <| by simpa
  | .tlam b, v => match @RefSet.dec b v with
    | .isTrue h => .isTrue <| .tlam h
    | .isFalse h => .isFalse <| by simpa
  | .app a b, v =>
    match @RefSet.dec a v, @RefSet.dec b v with
    | .isTrue h, _ => .isTrue <| .appL h
    | _, .isTrue h => .isTrue <| .appR h
    | .isFalse h₁, .isFalse h₂ => .isFalse $ by simp_all
  | .tapp expr ty, v => match @RefSet.dec expr v with
    | .isTrue h => .isTrue <| .tappL h
    | .isFalse h => .isFalse <| by simpa

end Expr
