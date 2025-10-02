import Types.Expr.Stx
import Types.Ty.RefSet

namespace Expr

-- TRefSet predicate for expressions - tracks type variable references
@[grind]
inductive TRefSet : Expr → Nat → Prop
  | appL {a b idx} : TRefSet a idx → TRefSet (.app a b) idx
  | appR {a b idx} : TRefSet b idx → TRefSet (.app a b) idx
  | lamT {ty body idx} : Ty.RefSet ty idx → TRefSet (.lam ty body) idx
  | lamB {ty body idx} : TRefSet body idx → TRefSet (.lam ty body) idx
  | tappL {expr ty idx} : TRefSet expr idx → TRefSet (.tapp expr ty) idx
  | tappR {expr ty idx} : Ty.RefSet ty idx → TRefSet (.tapp expr ty) idx
  | tlam {body idx} : TRefSet body idx.succ → TRefSet (.tlam body) idx

@[simp, grind =]
theorem TRefSet_lam {ty body idx} : TRefSet (.lam ty body) idx ↔ (Ty.RefSet ty idx ∨ TRefSet body idx) := by
  grind

@[simp, grind =]
theorem TRefSet_tlam {body idx} : TRefSet (.tlam body) idx ↔ TRefSet body (idx + 1) := by
  grind

@[simp, grind =]
theorem TRefSet_app {a b idx} : TRefSet (.app a b) idx ↔ (TRefSet a idx ∨ TRefSet b idx) := by
  grind

@[simp, grind =]
theorem TRefSet_tapp {expr ty idx} : TRefSet (.tapp expr ty) idx ↔ (TRefSet expr idx ∨ Ty.RefSet ty idx) := by
  grind

@[simp]
theorem TRefSet_id {idx jdx} : ¬TRefSet (.id idx) jdx := by
  grind

example : TRefSet (.lam [t|0] (.id 1)) 0 := .lamT .id
example : TRefSet (.tapp (.id 0) [t|1]) 1 := .tappR .id
example : TRefSet (.tlam (.tapp (.id 0) [t|1])) 0 := .tlam (.tappR .id)
example : ¬∃ n, TRefSet (.id 5) n := by simp

theorem TRefSet_dist_app {ty a b idx} : TRefSet (.lam ty (.app a b)) idx ↔ TRefSet (.lam ty a) idx ∨ TRefSet (.lam ty b) idx := by
  grind

theorem TRefSet_dist_tlam {a b idx} : TRefSet (.tlam (.app a b)) idx ↔ TRefSet (.tlam a) idx ∨ TRefSet (.tlam b) idx := by
  grind

instance TRefSet.dec : {e : Expr} → {n : Nat} → Decidable (TRefSet e n)
  | .id x, v => .isFalse $ by simp
  | .lam ty b, v =>
    match Ty.RefSet.dec (t := ty) (n := v), @TRefSet.dec b v with
    | .isTrue h, _ => .isTrue <| .lamT h
    | _, .isTrue h => .isTrue <| .lamB h
    | .isFalse h₁, .isFalse h₂ => .isFalse $ by simp_all
  | .tlam b, v => match @TRefSet.dec b v.succ with
    | .isTrue h => .isTrue <| .tlam h
    | .isFalse h => .isFalse <| by simpa
  | .app a b, v =>
    match @TRefSet.dec a v, @TRefSet.dec b v with
    | .isTrue h, _ => .isTrue <| .appL h
    | _, .isTrue h => .isTrue <| .appR h
    | .isFalse h₁, .isFalse h₂ => .isFalse $ by simp_all
  | .tapp expr ty, v =>
    match @TRefSet.dec expr v, Ty.RefSet.dec (t := ty) (n := v) with
    | .isTrue h, _ => .isTrue <| .tappL h
    | _, .isTrue h => .isTrue <| .tappR h
    | .isFalse h₁, .isFalse h₂ => .isFalse $ by simp_all

end Expr
