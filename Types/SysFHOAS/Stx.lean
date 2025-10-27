
namespace SysFPHOAS

universe u v

inductive Type' (rep : Type u) : Type u where
  | var : rep → Type' rep
  | arr : Type' rep → Type' rep → Type' rep
  | all : (rep → Type' rep) → Type' rep

def Ty : Type (u + 1) :=  {rep2 : Type u} → Type' rep2

inductive Term' {T: Type v} (rep : Type' T → Type u) : Type' T →  Type (max u v) where
  | var : ∀ {t : Type' T}, rep t → Term' rep t
  | app :  {A B : Type' T} →  Term' rep (Type'.arr A B) → Term' rep A → Term' rep B
  | lam : ∀ {A B : Type' T}, (rep A → Term' rep B) → Term' rep (Type'.arr A B)
  | tapp : {f : T → Type' T}  → Term' rep (Type'.all f) → (t : T) → Term' rep (f t)
  | tlam : {f : T → Type' T} → ((x : T) → Term' rep (f x)) → Term' rep (Type'.all f)

def Term (t : Ty) : Type (u + 1) :=
  {T : Type u} → {rep : Type' T → Type u} → Term' rep t

