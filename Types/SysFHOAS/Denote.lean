import Types.SysFHOAS.Stx

namespace SysFPHOAS

universe u v w

@[simp]
def Type'.denote : Type' (Sort u) → Sort (u + 1)
  | .var T => PLift T
  | .arr t1 t2 => Type'.denote t1 → Type'.denote t2
  | .all f => (T : Sort u) → Type'.denote (f T)

def Term'.denote {ty : Type' (Type' (Sort (u+1)))} : Term' Type'.denote ty → ty.squash.denote
  | .var v => v
  | .app t1 t2 =>
    (Term'.denote t1) (Term'.denote t2)
  | .lam f => fun x => Term'.denote (f x)
  | @Term'.tapp _ _ _f term1 t => by
    have := (Term'.denote (term1))
    sorry
  | @Term'.tlam _ _ f g => fun x => Term'.denote (g x)

def same {ty : Ty} (t1 t2 : Term ty) : Prop :=
  Term'.denote t1 = Term'.denote t2

