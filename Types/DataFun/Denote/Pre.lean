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

open CategoryTheory

instance {v : Sigma Preorder} : Preorder v.fst := v.snd

instance : Category.{u, u+1} (Sigma Preorder.{u}) where
  Hom a b := OrderHom a.fst b.fst
  id a := OrderHom.id
  comp f g := OrderHom.comp g f

instance : CartesianMonoidalCategory.{u,u+1} (Sigma Preorder.{u}) :=
  CartesianMonoidalCategory.ofChosenFiniteProducts 
    {
      cone := Limits.asEmptyCone (⟨PUnit, by infer_instance⟩)
      isLimit := Limits.IsTerminal.ofUniqueHom 
        (fun X => {
          toFun _ := .unit
          monotone' _ _ _ := refl _
        })
        fun X m => by
          apply OrderHom.ext
          ext _
    }
    fun X Y => {
      cone := Limits.BinaryFan.mk (P := ⟨X.fst × Y.fst, by infer_instance⟩)
        OrderHom.fst
        OrderHom.snd
      isLimit := Limits.BinaryFan.isLimitMk
        (fun s => {
          toFun p := ⟨s.fst.toFun p, s.snd.toFun p⟩
          monotone' x y h :=
            Prod.mk_le_mk.mpr ⟨s.fst.monotone h, s.snd.monotone h⟩
        })
        (fun v => by
          apply OrderHom.ext
          funext v
          rfl)
        (fun v => by
          apply OrderHom.ext
          funext v
          rfl)
        fun s m hf hs => by
          apply OrderHom.ext
          funext v
          change m.toFun v = Prod.mk (s.fst.toFun v) (s.snd.toFun v)
          rw [← hf, ← hs]
          ext <;> rfl
    }

instance : MonoidalClosed (Sigma Preorder.{u}) where
  closed X := {
    rightAdj := {
      obj := sorry
      map := sorry
    }
    adj := sorry
  }

structure Dize (T : Type _) where
  mk ::
  out' : T
deriving DecidableEq, Repr

instance : PartialOrder (Dize T) where
  le := (· = ·)
  le_refl := Eq.refl
  le_trans _ _ _ := Eq.trans
  le_antisymm a b h h' := h ▸ rfl

namespace Dize

instance [Fintype T] : Fintype (Dize T) where
  elems := (Fintype.elems : Finset T).map (⟨mk, fun _ _ => by simp⟩)
  complete := fun ⟨x⟩ => by simp [Fintype.complete]

def lift {A B} (f : A → B) : Dize A →o Dize B where
  toFun := mk ∘ f ∘ out'
  monotone' _ _ := by rintro rfl; rfl

def repr {A B} : (A → B) ≃ (Dize A →o Dize B) where
  toFun := lift
  invFun f := out' ∘ f.toFun ∘ mk
  left_inv _ := rfl
  right_inv _ := rfl

def out {A} [Preorder A] : Dize A →o A where
  toFun := out'
  monotone' _ _ := by rintro rfl; rfl

def dub {A} [Preorder A] : Dize A →o Dize (Dize A) where
  toFun := mk
  monotone' _ _ := by rintro rfl; rfl

abbrev F : Sigma Preorder ⥤ Sigma Preorder where
  obj X := ⟨Dize X.fst, by infer_instance⟩
  map f := Dize.lift f.toFun

def C : Comonad (Sigma Preorder) where
  toFunctor := F
  ε := { app X := Dize.out }
  δ := { app X := Dize.dub }

def oiso {A B} : Dize (A × B) ≃o (Dize A × Dize B) where
  toFun := fun ⟨⟨a, b⟩⟩ => ⟨⟨a⟩, ⟨b⟩⟩
  invFun := fun ⟨⟨a⟩, ⟨b⟩⟩ => ⟨⟨a, b⟩⟩
  map_rel_iff' {a b} := {
    mp h := by
      rcases a with ⟨⟨a, _⟩⟩
      rcases b with ⟨⟨b, _⟩⟩
      obtain ⟨h, h'⟩ := Prod.mk_le_mk.mp h
      change _ = _ at h h'
      simp only [mk.injEq] at h h'
      subst h h'
      rfl
    mpr := by
      rintro rfl
      refine Prod.mk_le_mk.mpr ⟨rfl, rfl⟩
  }

end Dize

