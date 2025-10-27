import Types.BLang
import Types.STLC.Typed
import Types.STLCHOAS.Show

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



-/

end Ex5

end STLCHOAS

