import Types.STLCHOAS.Stx

namespace STLCHOAS

@[simp]
def Ty.denote : Ty → Type
  | .arr t1 t2 => t1.denote → t2.denote

  | .cpd t1 t2 => t1.denote ⊕ t2.denote
  | .prod t1 t2 => t1.denote × t2.denote
  | .empty => Empty
  | .unit => Unit

@[simp]
def Term'.denote {ty : Ty} : Term' Ty.denote ty → ty.denote
  | .var v => v
  | .app t1 t2 => (Term'.denote t1) (Term'.denote t2)
  | .lam f => fun x => Term'.denote (f x)
  | .inr x => .inr x.denote
  | .inl x => .inl x.denote
  | .case s a b =>
    match s.denote with
    | .inl x => (a x).denote
    | .inr x => (b x).denote
  | .snd a => a.denote.snd
  | .fst a => a.denote.fst
  | .mkP a b => ⟨a.denote, b.denote⟩
  | .empty x => x.denote.elim
  | .unit => .unit

def same {ty : Ty} (t1 t2 : Term ty) : Prop :=
  Term'.denote t1 = Term'.denote t2

