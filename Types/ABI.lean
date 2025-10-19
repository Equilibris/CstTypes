import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.GeneralizeProofs

universe u v w

variable {A : Type u} {B : Type v} 

namespace V1

variable {eq : Nonempty (A ≃ B)}

structure ABI (A : Type u) (B : Type v) (eq : Nonempty (A ≃ B)) : Type u :=
  private hmk ::
  private inner : A

namespace ABI

noncomputable def mk (x : B) : ABI A B eq :=
  hmk (eq.some.invFun x)

noncomputable def dest (x : ABI A B eq) : B :=
  eq.some.toFun x.inner

theorem mk_dest {x : B} : dest (mk (eq := eq) x) = x := by
  simp [mk, dest]
theorem dest_mk {x : ABI A B eq} : mk (dest x) = x := by
  simp [mk, dest]

end V1.ABI

namespace V2

structure ABIRepr (A : Type u) (B : Type v) (eq : A ≃ B) where
  intro ::
  carry : Type u

  mkB : B → carry
  mkA : A → carry

  destB : carry → B
  destA : carry → A

  mkB_destB : destB ∘ mkB = id
  destB_mkB : mkB ∘ destB = id

  mkA_destA : destB ∘ mkB = id
  destA_mkA : mkB ∘ destB = id

  toFun_mkB_mkA : mkB ∘ eq.toFun = mkA
  toFun_mkA_mkB : mkA ∘ eq.invFun = mkB

  destA_toFun_destB : eq.toFun ∘ destA = destB
  destB_toFun_destA : eq.invFun ∘ destB = destA

  elim : {motive : (t : Type max u v) → t → Sort w}
       → (hLog : (z : A) → motive (ULift A) (.up z))
       → (hCheap : (z : B) → motive (ULift B) (.up z))
       → (∀ z, HEq (hLog z) (hCheap (eq.toFun z)))
       → (∀ z, HEq (hCheap z) (hLog (eq.invFun z)))
       → (v : carry) → motive (ULift carry) (.up v)

  elimLog : {motive : (t : Type max u v) → t → Sort w}
       → (hLog : (z : A) → motive (ULift A) (.up z))
       → (hCheap : (z : B) → motive (ULift B) (.up z))
       → (eqA : ∀ z, HEq (hLog z) (hCheap (eq.toFun z)))
       → (eqB : ∀ z, HEq (hCheap z) (hLog (eq.invFun z)))
       → ∀ z, HEq (elim hLog hCheap eqA eqB (mkA z)) (hLog z)
  elimCheap : {motive : (t : Type max u v) → t → Sort _}
       → (hLog : (z : A) → motive (ULift A) (.up z))
       → (hCheap : (z : B) → motive (ULift B) (.up z))
       → (eqA : ∀ z, HEq (hLog z) (hCheap (eq.toFun z)))
       → (eqB : ∀ z, HEq (hCheap z) (hLog (eq.invFun z)))
       → ∀ z : B, HEq (elim hLog hCheap eqA eqB (mkB z)) (hCheap z)

def ULift.down.inj : (ULift.down a = ULift.down b) → a = b := by
  cases a; cases b
  dsimp
  rintro rfl
  rfl

def ULift.down.inj' : a = b → (ULift.down a = ULift.down b) := by
  rintro rfl; rfl

@[simp]
unsafe def unsafeCastNoop {v : Type _} : unsafeCast (α := v) (β := v) = id := rfl
@[simp]
unsafe def unsafeCastComp {α β χ : Type _}
    : unsafeCast (α := β) (β := χ) ∘ unsafeCast = unsafeCast (α := α) (β := χ) := by
  funext a
  dsimp [unsafeCast]
  congr
  change ULift.down _ = ULift.down _
  sorry


unsafe def ABIImpl (A : Type u) (B : Type v) (eq : A ≃ B)
    : ABIRepr.{u, v, w} A B eq := {
  carry := unsafeCast B,
  mkA := unsafeCast ∘ eq.toFun,
  mkB := unsafeCast,
  destA := eq.invFun ∘ unsafeCast,
  destB := unsafeCast,
  mkB_destB := by simp
  destB_mkB := by simp
  mkA_destA := by simp
  destA_mkA := by simp
  toFun_mkB_mkA := rfl
  toFun_mkA_mkB := by
    change unsafeCast ∘ (_ ∘ _) = _
    simp
  destA_toFun_destB := by
    change (_ ∘ _) ∘ unsafeCast = _
    simp
  destB_toFun_destA := rfl
  elim := fun _ hCheap _ _ x => unsafeCast $ hCheap $ unsafeCast x
  elimLog := fun hLog hCheap eqA eqB z => lcProof
  elimCheap := fun hLog hCheap eqA eqB x => lcProof
}

@[implemented_by ABIImpl]
opaque ABI (A : Type u) (B : Type v) (eq : A ≃ B)
    : ABIRepr.{u, v, w} A B eq := {
  carry := A,
  mkA := id,
  mkB := eq.invFun,
  destA := id,
  destB := eq.toFun,
  mkB_destB := by simp
  destB_mkB := by simp
  mkA_destA := by simp
  destA_mkA := by simp
  toFun_mkB_mkA := by simp
  toFun_mkA_mkB := by simp
  destA_toFun_destB := by simp
  destB_toFun_destA := by simp
  elim := fun hLog _ _ _ x => hLog $ x
  elimLog := fun hLog hCheap eqA eqB z => HEq.rfl
  elimCheap := fun hLog hCheap eqA eqB x => HEq.symm (eqB x)
}

namespace ABIRepr

/- attribute [elab_as_elim] ABIRepr.elim -/

variable {eq : A ≃ B}

instance : CoeSort (ABIRepr A B eq) (Type u) := ⟨ABIRepr.carry⟩


end V2.ABIRepr

namespace V3

structure ABIRepr (A : Type u) (B : Type v) (eq : A ≃ B) where
  intro ::
  carry : Type u

  mkB : B → carry
  mkA : A → carry

  destB : carry → B
  destA : carry → A

  mkB_destB : destB ∘ mkB = id
  destB_mkB : mkB ∘ destB = id

  mkA_destA : destA ∘ mkA = id
  destA_mkA : mkA ∘ destA = id

  toFun_mkB_mkA  : mkB ∘ eq.toFun = mkA
  invFun_mkA_mkB : mkA ∘ eq.invFun = mkB

  destA_toFun_destB  : eq ∘ destA = destB
  destB_invFun_destA : eq.symm ∘ destB = destA

  elim : {motive : carry → Sort w}
       → (hLog : (z : A) → motive (mkA z))
       → (hCheap : (z : B) → motive (mkB z))
       → (eqA : ∀ z, HEq (hLog z) (hCheap (eq z)))
       → (eqB : ∀ z, HEq (hCheap z) (hLog (eq.symm z)))
       → (v : carry) → motive v

  elimLog : {motive : carry → Sort w}
       → {hLog : (z : A) → motive (mkA z)}
       → {hCheap : (z : B) → motive (mkB z)}
       → {eqA : ∀ z, HEq (hLog z) (hCheap (eq z))}
       → {eqB : ∀ z, HEq (hCheap z) (hLog (eq.symm z))}
       → ∀ z, HEq (elim hLog hCheap eqA eqB (mkA z)) (hLog z)
  elimCheap : {motive : carry → Sort w}
       → {hLog : (z : A) → motive (mkA z)}
       → {hCheap : (z : B) → motive (mkB z)}
       → {eqA : ∀ z, HEq (hLog z) (hCheap (eq z))}
       → {eqB : ∀ z, HEq (hCheap z) (hLog (eq.symm z))}
       → ∀ z : B, HEq (elim hLog hCheap eqA eqB (mkB z)) (hCheap z)

@[simp]
unsafe def unsafeCastNoop {v : Type _} : unsafeCast (α := v) (β := v) = id := rfl

section corruptionSurface

@[simp]
unsafe axiom unsafeCastComp {α β χ : Type _}
    : unsafeCast (α := β) (β := χ) ∘ unsafeCast = unsafeCast (α := α) (β := χ)
unsafe abbrev unsafeIn : B → unsafeCast B := unsafeCast
unsafe abbrev unsafeOut : unsafeCast B → B := unsafeCast

end corruptionSurface

private unsafe def ABIImpl (A : Type u) (B : Type v) (eq : A ≃ B)
    : ABIRepr.{u, v, w} A B eq := {
  carry := unsafeCast B,
  mkA := unsafeIn ∘ eq,
  mkB := unsafeIn,
  destA := eq.symm ∘ unsafeOut,
  destB := unsafeOut,
  mkB_destB := unsafeCastComp
  destB_mkB := unsafeCastComp
  mkA_destA := calc
    eq.symm ∘ (unsafeCast ∘ unsafeCast) ∘ eq
      = eq.symm ∘ id ∘ eq             := by rw [unsafeCastComp, unsafeCastNoop]
    _ = id                            := Equiv.symm_comp_self eq 
  destA_mkA := calc
    unsafeCast ∘ (eq ∘ eq.symm) ∘ unsafeCast
      = unsafeCast ∘ id ∘ unsafeCast  := by rw [Equiv.self_comp_symm eq]
    _ = id                            := unsafeCastComp.trans unsafeCastNoop
  toFun_mkB_mkA := rfl
  invFun_mkA_mkB := calc
    unsafeCast ∘ (eq ∘ eq.symm)
      = unsafeIn ∘ id                 := by rw [Equiv.self_comp_symm]
    _ = unsafeIn                      := rfl
  destA_toFun_destB := calc
    (eq ∘ eq.symm) ∘ unsafeOut
      = id ∘ unsafeOut                := by rw [Equiv.self_comp_symm]
    _ = unsafeOut                     := rfl
  destB_invFun_destA := rfl
  elim := fun {motive} _ hCheap _ _ x =>
    cast (by rw [unsafeCastComp]; rfl) <|
      show motive ((unsafeCast ∘ unsafeCast) x)
      from hCheap <| unsafeOut x
  elimLog := fun {_ hLog hCheap eqA _ z} => by
    change HEq (cast _ (hCheap ((unsafeCast ∘ unsafeCast) _))) (hLog z)
    apply HEq.trans (cast_heq _ _)
    rw [unsafeCastComp, unsafeCastNoop]
    exact (eqA z).symm
  elimCheap := fun {_ hLog hCheap _ _ x} => by
    change HEq (cast _ (hCheap ((unsafeCast ∘ unsafeCast) _))) (hCheap (id x))
    apply HEq.trans (cast_heq _ _)
    rw [unsafeCastComp, unsafeCastNoop]
}

@[implemented_by ABIImpl]
opaque ABI (A : Type u) (B : Type v) (eq : A ≃ B)
    : ABIRepr.{u, v, w} A B eq := {
  carry := A,
  mkA := id,
  mkB := eq.invFun,
  destA := id,
  destB := eq.toFun,
  mkB_destB := Equiv.self_comp_symm eq
  destB_mkB := Equiv.symm_comp_self eq
  mkA_destA := rfl
  destA_mkA := rfl
  toFun_mkB_mkA := Equiv.symm_comp_self eq
  invFun_mkA_mkB := rfl
  destA_toFun_destB := rfl
  destB_invFun_destA := Equiv.symm_comp_self eq
  elim := fun {_ hLog _ _ _ x} => hLog x
  elimLog := fun {_ hLog _ _ _ x} => HEq.refl (hLog x)
  elimCheap := fun {_ _ _ _ eqB x} => (eqB x).symm
}

namespace ABIRepr

attribute [elab_as_elim] ABIRepr.elim

variable {eq : A ≃ B} {r : ABIRepr A B eq}

def fn {motive : Sort _}
    (fa : A → motive)
    (fb : B → motive)
    (eqa : fa = fb ∘ eq)
    (eqb : fb = fa ∘ eq.symm)
    : r.carry → motive :=
  r.elim fa fb
    (heq_of_eq <| congrFun eqa ·)
    (heq_of_eq <| congrFun eqb ·)

def fnA {a} {motive : Sort _}
    {fa : A → motive}
    {fb : B → motive}
    {eqa : fa = fb ∘ eq}
    {eqb : fb = fa ∘ eq.symm}
    : fn fa fb eqa eqb (r.mkA a) = fa a :=
  eq_of_heq <| r.elimLog a
def fnB {b} {motive : Sort _}
    {fa : A → motive}
    {fb : B → motive}
    {eqa : fa = fb ∘ eq}
    {eqb : fb = fa ∘ eq.symm}
    : fn fa fb eqa eqb (r.mkB b) = fb b :=
  eq_of_heq <| r.elimCheap b

def equivA : A ≃ r.carry where
  toFun  := r.mkA
  invFun := r.destA
  left_inv  := fun a => by
    change (_ ∘ _) a = id _
    rw [mkA_destA]
  right_inv := fun a => by
    change (_ ∘ _) a = id _
    rw [destA_mkA]

def equivB : B ≃ r.carry where
  toFun  := r.mkB
  invFun := r.destB
  left_inv  := fun a => by
    change (_ ∘ _) a = id _
    rw [mkB_destB]
  right_inv := fun a => by
    change (_ ∘ _) a = id _
    rw [destB_mkB]

end V3.ABIRepr

