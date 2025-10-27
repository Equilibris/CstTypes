import Types.STLC.Stx
import Types.STLC.Red

namespace STLC.Stx

mutual
inductive NonEval : Stx → Prop
  | bvar {idx : ℕ} : NonEval (.bvar idx)
  | app {a b : Stx} (lhs : NonEval a) (rhs : Terminal b) : NonEval (.app a b)

inductive Terminal : Stx → Prop
  | abs {ty : Ty} {a : Stx} (h : Terminal a) : Terminal (.abs ty a)
  | nonEval {a : Stx} (h : NonEval a) : Terminal a
end

@[simp]
theorem Terminal_abs {ty : Ty} {a : Stx} : Terminal (.abs ty a) ↔ Terminal a := by
  constructor
  <;> intro h
  · cases h
    next h => exact h
    next h => cases h
  · exact .abs h

@[simp]
theorem NonEval_bvar {idx : ℕ} : NonEval (.bvar idx) ↔ True := by
  constructor <;> intro _
  · trivial
  · exact .bvar

@[simp]
theorem Terminal_bvar {idx : ℕ} : Terminal (.bvar idx) ↔ True := by
  constructor <;> intro _
  · trivial
  · exact .nonEval .bvar

@[simp]
theorem Terminal_app {a b : Stx} : Terminal (.app a b) ↔ (NonEval a) ∧ (Terminal b) := by
  constructor
  <;> intro h
  · cases h; next h =>
    cases h; next a b =>
    exact ⟨a, b⟩
  · rcases h with ⟨a, b⟩
    exact .nonEval $ .app a b

@[simp]
theorem NonEval_app {a b : Stx} : NonEval (.app a b) ↔ (NonEval a) ∧ (Terminal b) := by
  constructor
  <;> intro h
  · cases h; next a b =>
    exact ⟨a, b⟩
  · rcases h with ⟨a, b⟩
    exact .app a b

mutual
/-- Proof of correctness for terminal -/
theorem Terminal_not_Red {a b : Stx} (terminal : Stx.Terminal a) : ¬Red a b := fun h =>
  match h with
  | .appl h => by
    rw [Stx.Terminal_app] at terminal
    rcases terminal with ⟨a, _⟩
    exact NonEval_not_Red a h
  | .appr h => by
    rw [Stx.Terminal_app] at terminal
    rcases terminal with ⟨_, a⟩
    exact Terminal_not_Red a h
  | .congr h => by
    rw [Stx.Terminal_abs] at terminal
    exact Terminal_not_Red terminal h
  | .beta => by rcases terminal with (_|_|_|_)
theorem NonEval_not_Red {a b : Stx} (terminal : Stx.NonEval a) : ¬Red a b := fun h =>
  match h with
  | .appl h => by
    rw [Stx.NonEval_app] at terminal
    rcases terminal with ⟨a, _⟩
    exact NonEval_not_Red a h
  | .appr h => by
    rw [Stx.NonEval_app] at terminal
    rcases terminal with ⟨_, a⟩
    exact Terminal_not_Red a h
  | .congr h => by
    cases terminal
  | .beta => by rcases terminal with (_|_|_)
end

end Stx

end STLC
