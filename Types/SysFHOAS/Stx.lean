
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

def Type'.higher (n : Nat) (rep : Type u) := n.succ.repeat Type' rep

def Type'.pvar {n : Nat} {rep} (r : rep) : n.repeat Type' rep :=
  match n with
  | 0 => r
  | _+1 => .var (Type'.pvar r)

def Type'.compress : {n : Nat} → {rep : Type u} → Type'.higher n rep → Type' rep
  | 0, _, v => v
  | n+1, _, .var rep => Type'.compress rep
  | _, _, .arr a b => .arr (Type'.compress a) (Type'.compress b)
  | _, _, .all f => sorry

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

inductive Term' {T: Type v} (rep : ∀ n, Type'.higher n T → Type u) : (n : Nat) → Type'.higher n T → Type (max u v) where
  | var {n t} : rep n t → Term' rep n t
  | app {n A B} : Term' rep n (Type'.arr A B) → Term' rep n A → Term' rep n B
  | lam {n A B}: (rep n A → Term' rep n B) → Term' rep n (Type'.arr A B)
  | tapp {n} : {f : Type'.higher n T → Type'.higher n.succ T}
    → Term' rep n.succ (Type'.all f)
    → (t : Type'.higher n T)
    → Term' rep n (f t).squash
  | tlam {n f} : ((x : _) → Term' rep n (f x)) → Term' rep n (Type'.all f)

def Term (t : Ty) : Type (u + 1) :=
  {T : Type u} → {n : Nat} → {rep : ∀ n, Type'.higher n T → Type u} → Term' rep n t

