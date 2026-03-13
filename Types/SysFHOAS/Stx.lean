
namespace SysFPHOAS

universe u v

inductive Type' (rep : Type u) : Type u where
  | var : rep → Type' rep
  | arr : Type' rep → Type' rep → Type' rep
  | all : (rep → Type' rep) → Type' rep

def Type'.squash {rep : Type u} : Type' (Type' rep) → Type' rep
  | .var rep => rep
  | .arr a b => .arr a.squash b.squash
  | .all f => .all fun v => (f (.var v)).squash

def Ty : Type (u + 1) :=  {rep2 : Type u} → Type' rep2

declare_syntax_cat hstx_ty

syntax ident : hstx_ty
syntax "!(" term ")" : hstx_ty
syntax "(" hstx_ty ")" : hstx_ty
syntax hstx_ty "→" hstx_ty : hstx_ty
syntax "∀" ident+ "." hstx_ty : hstx_ty

syntax "[ht|" hstx_ty "]" : term

macro_rules
  | `([ht| $v:ident ]) => `(Type'.var $v)
  | `([ht| !($t) ]) => `($t)
  | `([ht| $a → $b ]) => `(Type'.arr [ht| $a] [ht| $b])
  | `([ht| ($v) ]) => `(([ht|$v]))
  | `([ht| ∀ $i. $v]) => `(Type'.all fun $i => ([ht|$v]))
  | `([ht| ∀ $i $is*. $v]) => `(Type'.all fun $i => ([ht| ∀ $is*. $v]))

inductive Term' {T: Type v} (rep : Type' T → Type u) : Type' (Type' T) → Type (max u v) where
  | var {t} : rep t.squash → Term' rep t
  | app {A B} : Term' rep (Type'.arr A B) → Term' rep A → Term' rep B
  | lam {A B}: (rep A.squash → Term' rep B) → Term' rep (Type'.arr A B)
  | tapp : {f : Type' T → Type' (Type' T)}
    → Term' rep (Type'.all f)
    → (t : Type' T)
    → Term' rep (f t)
  | tlam {f} : ((x : _) → Term' rep (f x)) → Term' rep (Type'.all f)

def Term (t : Ty) : Type (u + 1) :=
  {T : Type u} → {rep : Type' T → Type u} → Term' rep t

