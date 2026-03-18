import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

open CategoryTheory

instance {v : Sigma Preorder} : Preorder v.fst := v.snd

instance : Category (Sigma Preorder) where
  Hom a b := OrderHom a.fst b.fst
  id a := OrderHom.id
  comp f g := OrderHom.comp g f

instance : CartesianMonoidalCategory (Sigma Preorder) :=
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

instance : MonoidalClosed (Sigma Preorder) where
  closed X := sorry
  

