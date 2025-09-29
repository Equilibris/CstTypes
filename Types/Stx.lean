import Types.TStx

inductive Stx : {n : Nat} → List (Ty n) → Ty n → Type
  | id {l} (id : Fin l.length) : Stx l l[id]

  | lam {n l t arg} : Ty n → Stx (arg :: l) t → @Stx n l [t|arg → t]
  | app {l a b} : Stx l [t| a → b] → Stx l a → Stx l b

  /- | tlam {n l t} : Stx (l) t → @Stx n l [t|Λ. t] -/
