import Types.STLC.StrongNorm.CTySpec
import Types.STLC.StrongNorm.ArgCount
import Mathlib.Tactic.DepRewrite

namespace STLC

inductive TyArr : List Ty → Type
  | nil : TyArr []
  | cons {hd tl} (h : ArgCount hd) (t : TyArr tl) : TyArr (hd :: tl)

namespace TyArr

def concat {a b} : TyArr a → TyArr b → TyArr (a ++ b)
  | .nil, a => a
  | .cons hd tl, v => .cons hd (concat tl v)

instance {a b} : HAppend (TyArr a) (TyArr b) (TyArr (a ++ b)) := ⟨TyArr.concat⟩
theorem cons_append {A B t} {a : TyArr A} {b : TyArr B} {z : ArgCount t}
    : .cons z (a ++ b) = (TyArr.cons z a) ++ b := rfl

@[simp]
theorem nil_concat {Γ} {Γ' : TyArr Γ} : (TyArr.nil ++ Γ') = Γ' := rfl

def get
    {Γ}
    (idx : Fin Γ.length)
    (v : TyArr Γ)
    : ArgCount Γ[idx] := match Γ, idx, v with
  | [], idx, _ => idx.elim0
  | _ :: _, ⟨0, _⟩, .cons hd _ => hd
  | _ :: _, ⟨n+1, h⟩, .cons _ tl' => get ⟨n, Nat.succ_lt_succ_iff.mp h⟩ tl'

theorem get_append_assoc
    {Γ₁ Γ₂ Γ₃}
    {Γ₁' : TyArr Γ₁} {Γ₂' : TyArr Γ₂} {Γ₃' : TyArr Γ₃}
    {idx : Fin (Γ₁ ++ Γ₂ ++ Γ₃).length}
    : get idx (Γ₁' ++  Γ₂' ++ Γ₃')
    ≍ get (idx.cast (by rw [List.append_assoc])) (Γ₁' ++ (Γ₂' ++ Γ₃')) :=
  match Γ₁, Γ₁', idx with
  | [], .nil, x => .refl _
  | hd :: tl, .cons hd' tl', ⟨0, _⟩ => by
    change get _ (cons hd' (tl' ++ Γ₂' ++ Γ₃')) ≍ get _ (cons hd' (tl' ++ (Γ₂' ++ Γ₃')))
    dsimp [get]
    rfl
  | hd :: tl, .cons hd' tl', ⟨n+1, h⟩ => by
    change get _ (cons hd' (tl' ++ Γ₂' ++ Γ₃')) ≍ get _ (cons hd' (tl' ++ (Γ₂' ++ Γ₃')))
    dsimp [get]
    exact get_append_assoc

theorem get_append
    {Γ₁ Γ₂ idx}
    {Γ₁' : TyArr Γ₁} {Γ₂' : TyArr Γ₂}
    (h : idx.toNat < Γ₁.length)
    : get idx (Γ₁' ++ Γ₂') ≍ get (idx.castLT h) Γ₁' :=
  match Γ₁, Γ₁', idx with
  | [], _, idx => (Nat.not_succ_le_zero idx (by grind)).elim
  | hd :: tl, .cons hd' tl', ⟨0, _⟩ => .refl _
  | hd :: tl, .cons hd' tl', ⟨n+1, _⟩ => by
    dsimp [get]
    exact get_append (Nat.succ_lt_succ_iff.mp ‹_›)

theorem get_append_right
    {Γ₁ Γ₂ idx}
    {Γ₁' : TyArr Γ₁} {Γ₂' : TyArr Γ₂}
    (hLe : Γ₁.length ≤ idx.toNat)
    : get idx (Γ₁' ++ Γ₂') ≍ get ((idx.cast (by rw [List.length_append, Nat.add_comm])).subNat Γ₁.length hLe) Γ₂' :=
  match Γ₁, Γ₁', idx with
  | [], .nil, idx => by
    change get _ Γ₂' ≍ _
    rfl
  | hd :: tl, .cons hd' tl', ⟨0, _⟩ => by simp at hLe
  | hd :: tl, .cons hd' tl', ⟨n+1, h⟩ => by
    change get ⟨n, _⟩ (tl' ++ Γ₂') ≍ get ⟨n + 1 - (tl.length + 1), _⟩ Γ₂'
    dsimp only [List.length_cons, List.cons_append, Fin.toNat_eq_val, add_le_add_iff_right] at hLe
    have : (n + 1 - (tl.length + 1)) = (n - tl.length) := Nat.add_sub_add_right n 1 tl.length
    rw [this] at h'
    rw [get_idx_eq_jdx h' this]
    exact get_append_right hLe _

inductive Every (p : ∀ {s}, ArgCount s → Prop) : {Γ : _} → TyArr Γ → Prop
  | nil : Every p .nil
  | cons {h t} (hd : p h) : Every p t → Every p (TyArr.cons h t)
  -- | cons (hd : p h) (tl : Every p t) : Every p (TyArr.cons h t) -- for unknown reasons the line below breaks things
  -- TODO: bug report

theorem Every_get
    {Γ idx val p}
    {Γ' : TyArr Γ} (h : Every p Γ')
    {hGet : Γ[idx]? = some val}
    : p (TyArr.get hGet Γ') :=
  match Γ, Γ', idx, h with
  | [], .nil, _, _ => Option.noConfusion (List.getElem?_nil.symm.trans hGet)
  | h :: t, .cons hd tl, 0, .cons hhd _ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hGet
    subst hGet
    simp only [get, cast_eq]
    exact hhd
  | h :: t, .cons _ tl, n+1, .cons _ htl => Every_get htl

theorem Every_concat
    {p A B} {a : TyArr A} {b : TyArr B}
    (h1 : Every p a) (h2 : Every p b) : Every p (a ++ b) :=
  match h1 with
  | .nil => h2
  | .cons h t => .cons h (Every_concat t h2)

end STLC.TyArr

