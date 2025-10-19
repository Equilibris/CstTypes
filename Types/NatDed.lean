namespace NatDed

inductive Stx
  | p : Prop → Stx
  | top : Stx
  | bot : Stx
  | and : Stx → Stx → Stx
  | or  : Stx → Stx → Stx
  | imp : Stx → Stx → Stx

def Stx.denote : Stx → Prop
  | .p a => a
  | .top => True
  | .bot => False
  | .imp a b => a.denote → b.denote
  | .or a b => a.denote ∨ b.denote
  | .and a b => a.denote ∧ b.denote

inductive Ty : List Stx → Stx → Type
  | itop {Γ} : Ty Γ .top
  | iand {Γ a b} : Ty Γ a → Ty Γ b → Ty Γ (.and a b)
  | iorl {Γ a b} : Ty Γ a → Ty Γ (.or a b)
  | iorr {Γ a b} : Ty Γ b → Ty Γ (.or a b)
  | iimp {Γ a b} : Ty (a :: Γ) b → Ty Γ (.imp a b)

  | var {Γ} (i : Fin Γ.length) : Ty Γ Γ[i]

  | ebot {Γ a} : Ty Γ .bot → Ty Γ a
  | eand {Γ a b R} : Ty Γ (.and a b) → Ty (a :: b :: Γ) R → Ty Γ R
  | eor  {Γ a b R} : Ty Γ (.or a b) → Ty (a :: Γ) R → Ty (b :: Γ) R → Ty Γ R
  | eimp {Γ a b}   : Ty Γ (.imp a b) → Ty Γ a → Ty Γ b

def Ctx.denote (Γ : List Stx) : Prop := (x : Fin Γ.length) → Γ[x].denote

def Ctx.denote.cons {Γ s} (hd : s.denote) (tl : Ctx.denote Γ) : Ctx.denote (s :: Γ)
  | ⟨0, _⟩ => hd
  | ⟨n+1, h⟩ => tl ⟨n, Nat.succ_lt_succ_iff.mp h⟩

def Ty.denote {Γ : List Stx} (h : Ctx.denote Γ)
    : {s : Stx} → Ty Γ s → s.denote
  | _, .eimp a b => a.denote h $ b.denote h
  | _, .eor a b c =>
    match a.denote h with
    | .inl h' => b.denote $ .cons h' h
    | .inr h' => c.denote $ .cons h' h
  | _, .eand a b =>
    have ⟨ad, bd⟩ := a.denote h
    b.denote (.cons ad $ .cons bd h)
  | _, .ebot x => (x.denote h).elim
  | _, .var i => h i
  | _, .itop => .intro
  | _, .iimp x => (x.denote $ Ctx.denote.cons · h)
  | _, .iorl x => .inl (x.denote h)
  | _, .iorr x => .inr (x.denote h)
  | _, .iand a b => .intro (a.denote h) (b.denote h)

