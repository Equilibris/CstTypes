import Types.Utils
import Types.DataFun.Ty

namespace DF

def dize : List ModalType → List ModalType :=
  List.filter ModalType.IsDisc

theorem dize_app {A B : List ModalType} : dize (A ++ B) = dize A ++ dize B := by
  simp [dize]

inductive Stx : List ModalType → Ty → Type
  | var : List.MemT v Γ → Stx Γ v.out

  | unit : Stx Γ .unit
  | prod : Stx Γ A → Stx Γ B → Stx Γ (.prod A B)
  | fst : Stx Γ (.prod A B) → Stx Γ A
  | snd : Stx Γ (.prod A B) → Stx Γ B

  | inl : Stx Γ A → Stx Γ (.cop A B)
  | inr : Stx Γ B → Stx Γ (.cop A B)
  | case
      : Stx Γ (.cop A B)
      → Stx (.mono A :: Γ) C
      → Stx (.mono B :: Γ) C
      → Stx Γ C

  | lam : Stx (.mono A :: Γ) B → Stx Γ (.fn A B)
  | app : Stx Γ (.fn A B) → Stx Γ A → Stx Γ B

  | sing : Stx (dize Γ) T.toTy → Stx Γ (.pow T)
  | bot : L.Lattice → Stx Γ L
  | join : L.Lattice → Stx Γ L → Stx Γ L → Stx Γ L
  | forE : L.Lattice → Stx Γ (.pow T) → Stx (.disc T.toTy :: Γ) L → Stx Γ L

  | discI : Stx (dize Γ) A → Stx Γ (.disc A)
  | discE : Stx Γ (.disc A) → Stx (.disc A :: Γ) C → Stx Γ C

  | fix : L.Lattice → Stx (.mono L :: dize Γ) L → Stx Γ L

namespace Stx

@[simp]
theorem sizeOf_cast' {A B As Bs} {a : Stx As A} (h : A = B) (h' : As = Bs)  : sizeOf (cast (by rw [h, h']) a) = sizeOf a := by
  subst h
  subst h'
  rfl

@[simp]
theorem sizeOf_cast {A B} {a : A} (h : A = B) : sizeOf (cast h a) = sizeOf a := by
  subst h
  rfl

def gshift Γ {Γ₁ Γ₂} : Stx (Γ ++ Γ₁) t → Stx (Γ ++ (Γ₂ ++ Γ₁)) t
  | .var h => .var h.sandwitch_shift

  | .unit => .unit
  | .prod a b => .prod (gshift _ a) (gshift _ b)
  | .fst a => .fst (gshift _ a)
  | .snd a => .snd (gshift _ a)

  | .inl a => .inl (gshift _ a)
  | .inr a => .inr (gshift _ a)
  | .case a b c => .case (gshift _ a) (gshift (_ :: _) b) (gshift (_ :: _) c)

  | .lam a => .lam (gshift (_ :: _) a)
  | .app a b => .app (gshift _ a) (gshift _ b)

  | .sing a =>
    have := gshift _ (Γ₂ := dize Γ₂) <| cast (by rw [dize_app]) a
    .sing <| cast (by simp [←dize_app]) this
  | .bot h => .bot h
  | .join h a b => .join h (gshift _ a) (gshift _ b)
  | .forE h a b => .forE h (gshift _ a) (gshift (_ :: _) b)

  | .discI a =>
    have := gshift _ (Γ₂ := dize Γ₂) <| cast (by rw [dize_app]) a
    .discI <| cast (by simp [←dize_app]) this
  | .discE a b => .discE (gshift _ a) (gshift (_ :: _) b)

  | .fix h a =>
    have := gshift (_ :: _) (Γ₂ := dize Γ₂) <| cast (by rw [dize_app]; rfl) a
    .fix h <| cast (by simp [←dize_app]) this
termination_by a => sizeOf a
decreasing_by
all_goals simp
any_goals omega
all_goals rw [sizeOf_cast']
any_goals rfl
any_goals omega
all_goals simp [dize_app]

/- def parSubst.noopL : {Γ : _} → HList (Stx Γ) (Γ.map ModalType.out) -/
/-   | [] => .nil -/
/-   | _ :: _ => .cons (.var .hd) <| noopL.map <| shift [_] -/

end Stx

end DF
