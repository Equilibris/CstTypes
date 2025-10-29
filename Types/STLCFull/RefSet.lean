import Types.STLCFull.Stx

namespace STLCFull

-- RefSet predicate for STLCFull expressions
@[grind]
inductive RefSet : Stx → Nat → Prop
  | app_fn {fn arg idx} : RefSet fn idx → RefSet (.app fn arg) idx
  | app_arg {fn arg idx} : RefSet arg idx → RefSet (.app fn arg) idx
  | abs {ty body idx} : RefSet body idx.succ → RefSet (.abs ty body) idx
  | prod_fst {a b idx} : RefSet a idx → RefSet (.prod a b) idx
  | prod_snd {a b idx} : RefSet b idx → RefSet (.prod a b) idx
  | fst {expr idx} : RefSet expr idx → RefSet (.fst expr) idx
  | snd {expr idx} : RefSet expr idx → RefSet (.snd expr) idx
  | bvar {idx} : RefSet (.bvar idx) idx

@[simp, grind =]
theorem RefSet_abs {ty body idx} : RefSet (.abs ty body) idx ↔ RefSet body (idx + 1) := by
  grind

@[simp, grind =]
theorem RefSet_app {fn arg idx} : RefSet (.app fn arg) idx ↔ (RefSet fn idx ∨ RefSet arg idx) := by
  grind

@[simp, grind =]
theorem RefSet_prod {a b idx} : RefSet (.prod a b) idx ↔ (RefSet a idx ∨ RefSet b idx) := by
  grind

@[simp, grind =]
theorem RefSet_fst {expr idx} : RefSet (.fst expr) idx ↔ RefSet expr idx := by
  grind

@[simp, grind =]
theorem RefSet_snd {expr idx} : RefSet (.snd expr) idx ↔ RefSet expr idx := by
  grind

@[simp, grind =]
theorem RefSet_bvar {idx jdx} : RefSet (.bvar idx) jdx ↔ idx = jdx := by
  grind

example : RefSet (.abs .unit (.app (.bvar 1) (.bvar 0))) 0 := .abs (.app_fn .bvar)
example : ¬∃ n, RefSet (.abs .unit (.bvar 0)) n := by simp

theorem RefSet_dist_app {ty fn arg idx} : RefSet (.abs ty (.app fn arg)) idx ↔ RefSet (.abs ty fn) idx ∨ RefSet (.abs ty arg) idx := by
  grind

theorem RefSet_dist_prod {ty a b idx} : RefSet (.abs ty (.prod a b)) idx ↔ RefSet (.abs ty a) idx ∨ RefSet (.abs ty b) idx := by
  grind

instance RefSet.dec : {e : Stx} → {n : Nat} → Decidable (RefSet e n)
  | .bvar x, v => if h : x = v then .isTrue <| h ▸ .bvar
    else .isFalse $ by simpa
  | .abs ty b, v => match @RefSet.dec b v.succ with
    | .isTrue h => .isTrue <| .abs h
    | .isFalse h => .isFalse <| by simpa
  | .app fn arg, v =>
    match @RefSet.dec fn v, @RefSet.dec arg v with
    | .isTrue h, _ => .isTrue <| .app_fn h
    | _, .isTrue h => .isTrue <| .app_arg h
    | .isFalse h₁, .isFalse h₂ => .isFalse $ by simp_all
  | .prod a b, v =>
    match @RefSet.dec a v, @RefSet.dec b v with
    | .isTrue h, _ => .isTrue <| .prod_fst h
    | _, .isTrue h => .isTrue <| .prod_snd h
    | .isFalse h₁, .isFalse h₂ => .isFalse $ by simp_all
  | .fst expr, v => match @RefSet.dec expr v with
    | .isTrue h => .isTrue <| .fst h
    | .isFalse h => .isFalse <| by simpa
  | .snd expr, v => match @RefSet.dec expr v with
    | .isTrue h => .isTrue <| .snd h
    | .isFalse h => .isFalse <| by simpa

end STLCFull
