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
import Types.DataFun.Denote.Pre

open CategoryTheory

class Chg (X : Type u) extends PartialOrder X where
  (D : Type u)
  [i : PartialOrder D]
  (Val : X → D → Prop)
  (up (v : X) (d : D) : Val v d → X)
  (z : X → D)
  -- Proofs:
  (z_Val : ∀ x, Val x (z x))
  (z_up_noop : ∀ x, up x (z x) (z_Val x) = x)

namespace Chg

instance [Chg X] : PartialOrder (Chg.D X) := Chg.i

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

variable (X Y Z)
    [Chg X]
    [Chg Y]
    [Chg Z]

structure PreHom where
  base : X →o Y
  deriv : Dize X × Chg.D X →o Chg.D Y

  deriv_is_valid x d : Val x d → Val (base x) (deriv (.mk x, d))
  deriv_is_deriv x d h : base (up x d h) = up (base x) (deriv ⟨.mk x, d⟩) (deriv_is_valid x d h)

namespace PreHom

instance {x : Sigma Chg} : Chg x.fst := x.snd

def id [Chg X] : PreHom X X where
  base := .id
  deriv := OrderHom.snd
  deriv_is_valid _ _ h := h
  deriv_is_deriv _ _ _ := rfl

def comp (f : PreHom X Y) (g : PreHom Y Z) : PreHom X Z where
  base := g.base.comp f.base
  deriv := {
    toFun := fun ⟨x, dx⟩ => g.deriv ⟨.mk <| f.base x.out, f.deriv ⟨x, dx⟩⟩
    monotone' := by
      intro ⟨⟨x⟩, dx⟩ ⟨⟨y⟩, dy⟩ ⟨hl, hr⟩
      obtain rfl := (Dize.mk.injEq _ _).mp hl
      refine g.deriv.monotone ⟨rfl, f.deriv.monotone ⟨rfl, hr⟩⟩
  }
  deriv_is_valid x dx h :=
    g.deriv_is_valid (f.base x) (f.deriv (.mk x, dx)) <| f.deriv_is_valid x dx h
  deriv_is_deriv x dx h := by
    dsimp
    rw [f.deriv_is_deriv, g.deriv_is_deriv]
    rfl

end PreHom

instance hSetoid : Setoid (PreHom X Y) where
  r := (·.base = ·.base)
  iseqv := {
    refl _ := rfl
    symm := Eq.symm
    trans := Eq.trans
  }

def Hom : Type _ := Quotient (hSetoid X Y)
def Hom.getF : Hom X Y → X →o Y := Quotient.lift PreHom.base fun _ _ h => h

@[ext]
theorem Hom.ext {a b : Hom X Y} (h : a.getF = b.getF) : a = b := by
  cases a using Quotient.ind
  cases b using Quotient.ind
  apply Quotient.sound h

instance : Coe (Hom X Y) (X →o Y) := ⟨Hom.getF _ _⟩
instance : CoeFun (Hom X Y) fun _ => X → Y := ⟨(·.getF _ _)⟩

instance : Category (Sigma Chg) where
  Hom X Y := Hom X.1 Y.1
  id X := Quotient.mk _ (PreHom.id _)
  comp {X Y Z} := Quotient.lift₂ (fun f g => .mk _ (.comp _ _ _ f g)) <| by
    intro a₁ b₁ a₂ b₂ (ha : _ = _) (hb : _ = _)
    apply Quotient.sound
    change b₁.base.comp a₁.base = b₂.base.comp a₂.base
    rw [ha, hb]
  id_comp {X Y} f := by
    rcases f with ⟨f⟩
    apply Quotient.sound
    rfl
  comp_id {X Y} f := by
    rcases f with ⟨f⟩
    apply Quotient.sound
    rfl
  assoc f g h := by
    rcases f with ⟨f⟩
    rcases g with ⟨g⟩
    rcases h with ⟨h⟩
    apply Quotient.sound
    rfl

instance : Chg PUnit where
  D := PUnit
  Val _ _ := True
  up _ _ _ := .unit
  z _ := .unit
  z_Val _ := .intro
  z_up_noop _ := rfl

instance : Chg (X × Y) where
  D := D X × D Y
  Val a b := Val a.1 b.1 ∧ Val a.2 b.2
  up x y h := ⟨up x.1 y.1 h.1, up x.2 y.2 h.2⟩
  z x := ⟨z x.1, z x.2⟩
  z_Val x := ⟨z_Val x.1, z_Val x.2⟩
  z_up_noop x := by simp [z_up_noop]

instance {X Y} [Preorder X] [Preorder Y] : Preorder (X ⊕ Y) where
  le
    | .inr a, .inr b
    | .inl a, .inl b => a ≤ b
    | .inr a, .inl b
    | .inl a, .inr b => False
  le_refl | .inl _ | .inr _ => le_refl _
  le_trans := by
    rintro (_|_) (_|_) (_|_) f g
    any_goals rcases f
    any_goals rcases g
    all_goals exact le_trans f g

instance {X Y} [PartialOrder X] [PartialOrder Y] : PartialOrder (X ⊕ Y) where
  le_antisymm := by
    rintro (_|_) (_|_) f g
    any_goals rcases f
    all_goals simp only [Sum.inr.injEq, Sum.inl.injEq]
    all_goals exact le_antisymm f g

instance : Chg (X ⊕ Y) where
  D := D X ⊕ D Y
  Val
    | .inl x, .inl dx
    | .inr x, .inr dx => Val x dx
    | .inl x, .inr dx
    | .inr x, .inl dx => False
  up 
    | .inl x, .inl dx => (.inl <| up x dx ·)
    | .inr x, .inr dx => (.inr <| up x dx ·)
    | .inl x, .inr dx
    | .inr x, .inl dx => False.elim
  z
    | .inl x => .inl (z x)
    | .inr x => .inr (z x)
  z_Val | .inr x | .inl x => z_Val x
  z_up_noop | .inr x | .inl x => by simp [z_up_noop]

instance : PartialOrder (Hom X Y) where
  le := (·.getF ≤ ·.getF)
  le_refl _ y := le_refl _
  le_trans a b c h g := h.trans g
  le_antisymm a b h g := Hom.ext X Y <| OrderHom.ext _ _ <| le_antisymm h g

def Hom.update (f : Hom X Y) (df : Dize X × D X →o D Y) : Hom X Y := f.liftOn (fun f => .mk _ {
  base := {
    toFun x := up (f.base x) (df ⟨.mk x, z x⟩) <| by 
      next f =>
      sorry
    monotone' := by 
      sorry
  }
  deriv := sorry
  deriv_is_valid := sorry
  deriv_is_deriv := sorry
}) sorry

instance : Chg (Hom X Y) where
  D := Dize X × D X →o D Y
  Val := sorry
  up := sorry
  z := sorry
  z_Val := sorry
  z_up_noop := sorry

end Chg

