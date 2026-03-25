import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Lattice
import Types.DataFun.Stx

class Chg (X : Type u) [PartialOrder X] where
  (D : Type u)
  [i : PartialOrder D]
  (Val : X → D → Prop)
  (up (v : X) (d : D) : Val v d → X)
  (z : X → D)
  -- Proofs:
  (z_Val : ∀ x, Val x (z x))
  (z_up_noop : ∀ x, up x (z x) (z_Val x) = x)

instance {n} : Chg (Fin n) where
  D := Nat
  Val := fun ⟨k, h⟩ d => k + d < n
  up := fun ⟨k, h⟩ d h' => ⟨k + d, by omega⟩
  z := 0
  z_Val x := by dsimp; omega
  z_up_noop x := by rfl

instance {L : Type _} [Lattice L] : Chg L where
  D := L
  Val _ _ := True
  up a b _ := max a b
  z x := x
  z_Val _ := .intro
  z_up_noop x := by simp



