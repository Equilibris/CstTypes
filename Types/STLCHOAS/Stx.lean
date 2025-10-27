namespace STLCHOAS

universe u v

inductive Ty : Type where
  | arr   : Ty → Ty → Ty
  | unit  : Ty
  | empty : Ty
  | prod  : Ty → Ty → Ty
  | cpd   : Ty → Ty → Ty

inductive Term' (rep : Ty → Type) : Ty → Type where
  | var {t} : rep t → Term' rep t

  | lam {A B} : (rep A → Term' rep B) → Term' rep (Ty.arr A B)
  | app {A B} : Term' rep (.arr A B) → Term' rep A → Term' rep B

  | unit : Term' rep .unit
  | empty {A} : Term' rep .empty → Term' rep A

  | mkP {A B} : Term' rep A → Term' rep B → Term' rep (.prod A B)
  | fst {A B} : Term' rep (.prod A B) → Term' rep A
  | snd {A B} : Term' rep (.prod A B) → Term' rep B

  | case {A B C} : Term' rep (.cpd A B) → (rep A → Term' rep C) → (rep B → Term' rep C) → Term' rep C
  | inl  {A B} : Term' rep A → Term' rep (.cpd A B)
  | inr  {A B} : Term' rep B → Term' rep (.cpd A B)

def Term (t : Ty) : Type 1 :=
  {rep : Ty → Type} → Term' rep t

