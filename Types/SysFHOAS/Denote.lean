import Types.SysFHOAS.Stx

namespace SysFPHOAS

universe u v w

@[simp]
def Type'.denote : Type' (Sort u) → Sort (u + 1)
  | .var T => PLift T
  | .arr t1 t2 => Type'.denote t1 → Type'.denote t2
  | .all f => (T : Sort u) → Type'.denote (f T)

def Term'.denote {n} {ty : Type'.higher n (Sort u)} : Term' (fun n => Type'.denote ∘ Type'.compress) n ty → (Type'.compress ty).denote
  | .var v => v
  | .app t1 t2 => by
    have a := (Term'.denote t1)
    have b := (Term'.denote t2)
    unfold Type'.compress at a
    dsimp at a
    sorry
  | .lam f => fun x => Term'.denote (f x)
  | @Term'.tapp _ _ _f term1 t =>
    (Term'.denote term1) t
  | @Term'.tlam _ _ f g => 
    sorry
    fun x => Term'.denote (g x)

def same {ty : Ty} (t1 t2 : Term ty) : Prop :=
  Term'.denote t1 = Term'.denote t2

