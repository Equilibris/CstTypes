import Types.BLang
import Types.STLC.Typed
import Types.STLCHOAS.Show
import Types.STLCHOAS.Denote
import Types.STLCFull.Red
import Types.STLCFull.Typed
import Types.STLCFull.RefSet

namespace BLang.BLang1.Stx

section Ex1
def Progress : {t : _} → (a : Stx t) → ((b : _) ×' Red a b) ⊕ Val a
  | _, .false => .inr .false
  | _, .true => .inr .true
  | _, .neg v =>
    (match Progress v with
    | .inl ⟨_, h⟩ => .inl ⟨_, .negCongr h⟩
    | .inr .true => .inl ⟨_, .negTrue⟩
    | .inr .false => .inl ⟨_, .negFalse⟩)
  | _, .and a _ => (match Progress a with
    | .inl ⟨_, h⟩=> .inl ⟨_, .andCongr h⟩
    | .inr .true => .inl ⟨_, .andTrue⟩
    | .inr .false => .inl ⟨_, .andFalse⟩)
  | _, .add a b => (match Progress a, Progress b with 
    | .inl ⟨_, h⟩, _ => .inl ⟨_, .addCongr h⟩
    | .inr .n, .inl ⟨_, h⟩ => .inl ⟨_, .addCongr' h⟩
    | .inr .n, .inr .n => .inl ⟨_, .add⟩)
  | _, .lt a b =>  (match Progress a, Progress b with 
    | .inl ⟨_, h⟩, _ => .inl ⟨_, .ltCongr h⟩
    | .inr .n, .inl ⟨_, h⟩ => .inl ⟨_, .ltCongr' h⟩
    | .inr (.n (n := a)), .inr (.n (n := b)) =>
      if h : a < b then .inl ⟨_, .ltLt h⟩
      else .inl ⟨_, .ltGe (Int.not_lt.mp h)⟩)
  | _, .n _ => .inr .n

end Ex1

end BLang.BLang1.Stx

namespace STLC

section Ex2

-- This proof is given in Types.STLC.Typed
-- https://github.com/Equilibris/CstTypes/tree/main/Types/STLC/Typed
-- Notably this is done over de Bruijn idx'd syntax

/--
info: STLC.TySpec_replace {Γ : List Ty} {x : Ty} {body : Stx} {ty₁ : Ty} {v : Stx}
  (hty₁ : TySpec Γ ((Stx.abs x body).app v) ty₁) : TySpec Γ (Stx.replace 0 body v) ty₁
-/
#guard_msgs in
#check TySpec_replace

/--
info: STLC.Progress {Γ : List Ty} {stx : Stx} {ty : Ty} (hTy : TySpec Γ stx ty) : stx.Terminal ∨ ∃ stx', Red stx stx'
-/
#guard_msgs in
#check Progress

/--
info: STLC.TypePreservation {Γ : List Ty} {e₁ e₂ : Stx} {ty : Ty} (h : Red e₁ e₂) (hTy : TySpec Γ e₁ ty) : TySpec Γ e₂ ty
-/
#guard_msgs in
#check TypePreservation

end Ex2

section Ex4

inductive DegTy : Type
  | arr : DegTy → DegTy → DegTy

def DegTy.deg : DegTy → False
  | .arr _ v => v.deg

inductive DegS : List DegTy → DegTy → Type
  | var {Γ} (x : Fin Γ.length) : DegS Γ Γ[x]
  | app {Γ A B} : DegS Γ (.arr A B) → DegS Γ A → DegS Γ B
  | lam {Γ A B}  : DegS (A :: Γ) B → DegS Γ (.arr A B)

def DegS.deg : {Γ : _} → {ty : _} → DegS Γ ty → False
  | Γ, _, .var v => Γ[v].deg
  | Γ, _, .lam x => x.deg
  | Γ, _, .app _ x => x.deg

/-
By having no base types, the syntax of types becomes an empty type.
This consequently means there cannot be any terms, nor instances of the type.
Otherwise p.o. explosion.
-/

end Ex4

end STLC

namespace STLCHOAS

section Ex5

/-

The Main property of negation is to be able to conclude Empty (absurd) when: A ∧ ¬A,
the notation (· → Empty) captures this notion perfectly as we can construct the term:

  (a : A) (b : A → Empty) ⊢ (b a : Empty)

This means this is a reasonable notion.
Notably, since Empty resides in a predicative univese,
DN does not hold without further axioms.
In an impredictive universe this axiom does hold though as we can assume LEM,
using LEM proving DN is quite easy.
The proof of LEM is very cool.

-/

/-- info: Classical.choice.{u} {α : Sort u} : Nonempty α → α -/
#guard_msgs in
#check Classical.choice

example {A : Prop /- Not Type! -/} : ¬¬A ↔ A := ⟨
  (match Classical.em A with | .inl h => h | .inr h' => · h' |>.elim),
  fun a h => h a
⟩

def ex5_1 {P Q : Ty} : Term [ty| ((P → 0) × (Q → 0)) → ((P + Q) → 0)] :=
  .lam fun h =>
    .lam fun v =>
      .case (.var v)
        (fun v => .app (.fst (.var h)) (.var v))
        (fun v => .app (.snd (.var h)) (.var v))


def ex5_2 {P Q : Ty} : Term [ty|((P + Q) → 0) → ((P → 0) × (Q → 0))] :=
  .lam fun h => .mkP
    (.lam fun v => .app (.var h) (.inl (.var v)))
    (.lam fun v => .app (.var h) (.inr (.var v)))

def ex5_3 {P Q : Ty} : Term [ty| ((P → 0) + (Q → 0)) → ((P × Q) → 0)] :=
  .lam fun h => .lam fun p =>
    .case (.var h)
      (fun h => .app (.var h) (.fst (.var p)))
      (fun h => .app (.var h) (.snd (.var p)))


/-
The final theorem does not hold in constructive mathematics,
I am unable to prove this in Lean.
Q for supo: is it independent?
-/

universe u
set_option linter.style.commandStart false

variable (hEM : (∀ P : Type u, (P → Empty) ⊕ P))

def DNofhEM (P : Type u) : ((P → Empty) → Empty) → P :=
  fun hDN => match hEM P with 
    | .inl x => (hDN x).elim
    | .inr x => x

def ex5_4 (P Q : Type u) : (P × Q → Empty) → ((P → Empty) ⊕ (Q → Empty)) :=
  fun h =>
    match hEM P, hEM Q with
    | .inl x, _ => .inl x
    | _, .inl x => .inr x
    | .inr a, .inr b => (h ⟨a, b⟩).elim

/-
EM is independent wrt to STLC.
If you force it to be true you lose canonisity but keep SN.
In standard STLC it is unprovable
-/

end Ex5


end STLCHOAS

namespace STLCFull

section Ex6

theorem Ex6.Gen {idx : Nat} : {Γ e t : _} → TySpec Γ e t → Γ.length ≤ idx → RefSet e idx → False
  | Γ, _, _, .bvar h, _, .bvar => by simp [*] at *
  | Γ, _, _, .snd h, hL, .snd hr
  | Γ, _, _, .fst h, hL, .fst hr
  | Γ, _, _, .prod h _, hL, .prod_fst hr
  | Γ, _, _, .prod _ h, hL, .prod_snd hr
  | Γ, _, _, .app h _, hL, .app_fn hr
  | Γ, _, _, .app _ h, hL, .app_arg hr
  | Γ, _, _, .abs h, hL, .abs hr => Gen h (by simpa) hr

theorem Ex6 {idx e t} (h : TySpec [] e t) : RefSet e idx → False := Ex6.Gen h (Nat.zero_le idx)

end Ex6

end STLCFull

section Ex8

-- A more nice constructive way of checking equivilent types is using bijection

/--
info: structure Equiv.{u_1, u_2} (α : Sort u_1) (β : Sort u_2) : Sort (max (max 1 u_1) u_2)
number of parameters: 2
fields:
  Equiv.toFun : α → β
  Equiv.invFun : β → α
  Equiv.left_inv : Function.LeftInverse self.invFun self.toFun := by
    intro;
      first
      | rfl
      | ext <;> rfl
  Equiv.right_inv : Function.RightInverse self.invFun self.toFun := by
    intro;
      first
      | rfl
      | ext <;> rfl
constructor:
  Equiv.mk.{u_1, u_2} {α : Sort u_1} {β : Sort u_2} (toFun : α → β) (invFun : β → α)
    (left_inv : Function.LeftInverse invFun toFun := by intro;
      first
      | rfl
      | ext <;> rfl)
    (right_inv : Function.RightInverse invFun toFun := by intro;
      first
      | rfl
      | ext <;> rfl) :
    α ≃ β
-/
#guard_msgs in
#print Equiv

-- Alternatively you could use the Nonempty equivilent

end Ex8

