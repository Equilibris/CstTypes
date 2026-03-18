import Types.Utils
import Types.DataFun.Ty

namespace DF

inductive Stx : (Γm Γd : List Ty) → Ty → Type
  | mvar : List.MemT v Γm → Stx Γm Γd v
  | dvar : List.MemT v Γd → Stx Γm Γd v

  | unit : Stx Γm Γd .unit
  | prod : Stx Γm Γd A → Stx Γm Γd B → Stx Γm Γd (.prod A B)
  | fst : Stx Γm Γd (.prod A B) → Stx Γm Γd A
  | snd : Stx Γm Γd (.prod A B) → Stx Γm Γd B

  | inl : Stx Γm Γd A → Stx Γm Γd (.cop A B)
  | inr : Stx Γm Γd B → Stx Γm Γd (.cop A B)
  | case
      : Stx Γm Γd (.cop A B)
      → Stx (A :: Γm) Γd C
      → Stx (B :: Γm) Γd C
      → Stx Γm Γd C

  | lam : Stx (A :: Γm) Γd B → Stx Γm Γd (.fn A B)
  | app : Stx Γm Γd (.fn A B) → Stx Γm Γd A → Stx Γm Γd B

  | sing : Stx [] Γd T.toTy → Stx Γm Γd (.pow T)
  | bot : L.Lattice → Stx Γm Γd  L
  | join : L.Lattice → Stx Γm Γd L → Stx Γm Γd L → Stx Γm Γd L
  | forE : L.Lattice → Stx Γm Γd (.pow T) → Stx Γm (T.toTy :: Γd) L → Stx Γm Γd L

  | discI : Stx [] Γd A → Stx Γm Γd (.disc A)
  | discE : Stx Γm Γd (.disc A) → Stx Γm (A :: Γd) C → Stx Γm Γd C

  | fix : L.Lattice → Stx [L] Γd L → Stx Γm Γd L

namespace Stx

def gwkn Γm Γd {Γ₁m Γ₂m Γ₁d Γ₂d} 
    : Stx (Γm ++ Γ₁m) (Γd ++ Γ₁d) t
    → Stx (Γm ++ (Γ₂m ++ Γ₁m)) (Γd ++ (Γ₂d ++ Γ₁d)) t
  | .mvar h => .mvar h.sandwitch_shift
  | .dvar h => .dvar h.sandwitch_shift

  | .unit => .unit
  | .prod a b => .prod (gwkn _ _ a) (gwkn _ _ b)
  | .fst a => .fst (gwkn _ _ a)
  | .snd a => .snd (gwkn _ _ a)

  | .inl a => .inl (gwkn _ _ a)
  | .inr a => .inr (gwkn _ _ a)
  | .case a b c => .case (gwkn _ _ a) (gwkn (_ :: _) _ b) (gwkn (_ :: _) _ c)

  | .lam a => .lam (gwkn (_ :: _) _ a)
  | .app a b => .app (gwkn _ _ a) (gwkn _ _ b)

  | .sing a =>
    .sing <| gwkn [] _ (Γ₂m := []) (Γ₂d := Γ₂d) a
  | .bot h => .bot h
  | .join h a b => .join h (gwkn _ _ a) (gwkn _ _ b)
  | .forE h a b => .forE h (gwkn _ _ a) (gwkn _ (_ :: _) b)

  | .discI a =>
    .discI <| gwkn [] _ (Γ₂m := []) (Γ₂d := Γ₂d) a
  | .discE a b => .discE (gwkn _ _ a) (gwkn _ (_ :: _) b)
  | .fix h a =>
    .fix h <| gwkn [t] _ (Γ₂m := []) (Γ₂d := Γ₂d) a

def wkn {Γ₁m Γ₂m Γ₁d Γ₂d} 
    : Stx Γ₁m Γ₁d t → Stx (Γ₂m ++ Γ₁m) (Γ₂d ++ Γ₁d) t :=
  gwkn [] []

end Stx

end DF
