import Types.STLCFull.Stx
import Types.STLCFull.Red

namespace STLCFull.Stx

mutual
@[grind]
inductive NonEval : Stx → Prop
  | bvar {idx} : NonEval (.bvar idx)
  | app {a b : Stx} (lhs : NonEval a) (rhs : Terminal b) : NonEval (.app a b)
  | fst {expr : Stx} (h : NonEval expr) : NonEval (.fst expr)
  | snd {expr : Stx} (h : NonEval expr) : NonEval (.snd expr)

@[grind]
inductive Terminal : Stx → Prop
  | abs {ty : Ty} {a : Stx} (h : Terminal a) : Terminal (.abs ty a)
  | prod {a b : Stx} (ha : Terminal a) (hb : Terminal b) : Terminal (.prod a b)
  | unit : Terminal .unit
  | nonEval {a : Stx} (h : NonEval a) : Terminal a
end

@[simp]
theorem Terminal_abs {ty : Ty} {a : Stx} : Terminal (.abs ty a) → Terminal a := by
  grind

@[simp]
theorem Terminal_prod {a b : Stx} : Terminal (.prod a b) → Terminal a → Terminal b := by
  grind

@[simp]
theorem Terminal_unit : Terminal .unit → True := by
  grind

@[simp]
theorem NonEval_bvar {idx} : NonEval (.bvar idx) → True := by
  grind

@[simp]
theorem Terminal_bvar {idx} : Terminal (.bvar idx) → True := by
  grind

@[simp]
theorem Terminal_app {a b : Stx} : Terminal (.app a b) → (NonEval a) ∨ (Terminal b) := by
  grind

@[simp]
theorem NonEval_app {a b : Stx} : NonEval (.app a b) → (NonEval a) ∨  (Terminal b) := by
  grind

@[simp]
theorem Terminal_fst {expr : Stx} : Terminal (.fst expr) → NonEval expr := by
  grind

@[simp]
theorem NonEval_fst {expr : Stx} : NonEval (.fst expr) → NonEval expr := by
  grind

@[simp]
theorem Terminal_snd {expr : Stx} : Terminal (.snd expr) → NonEval expr := by
  grind

@[simp]
theorem NonEval_snd {expr : Stx} : NonEval (.snd expr) → NonEval expr := by
  grind

mutual

theorem Terminal_not_Red {a b : Stx} (terminal : Terminal a) : ¬Red a b := fun h =>
  match h, terminal with
  | .app_fn h, .nonEval (.app lhs _) => NonEval_not_Red lhs h
  | .app_arg h, .nonEval (.app _ rhs) => Terminal_not_Red rhs h
  | .abs h, .abs term => Terminal_not_Red term h
  | .prod_fst h, .prod term _ => Terminal_not_Red term h
  | .prod_snd h, .prod _ term => Terminal_not_Red term h
  | .fst h, .nonEval (.fst h') => NonEval_not_Red h' h
  | .snd h, .nonEval (.snd h') => NonEval_not_Red h' h

theorem NonEval_not_Red {a b : Stx} (terminal : Stx.NonEval a) : ¬Red a b := fun h =>
  match h, terminal with
  | .app_fn h, .app h' _
  | .fst h, .fst h'
  | .snd h, .snd h' => NonEval_not_Red h' h
  | .app_arg h, .app _ h' => Terminal_not_Red h' h

end

end STLCFull.Stx

