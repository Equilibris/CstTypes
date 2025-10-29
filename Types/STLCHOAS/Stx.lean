namespace STLCHOAS

universe u v

inductive Ty : Type where
  | arr   : Ty → Ty → Ty
  | unit  : Ty
  | empty : Ty
  | prod  : Ty → Ty → Ty
  | cpd   : Ty → Ty → Ty

declare_syntax_cat stlc_ty

syntax num : stlc_ty
syntax ident : stlc_ty
syntax "!(" term ")" : stlc_ty
syntax "(" stlc_ty ")" : stlc_ty
syntax stlc_ty "→" stlc_ty : stlc_ty
syntax stlc_ty "×" stlc_ty : stlc_ty
syntax stlc_ty "+" stlc_ty : stlc_ty

syntax "[ty|" stlc_ty "]" : term

macro_rules
  | `([ty| 1 ]) => `(Ty.unit)
  | `([ty| 0 ]) => `(Ty.empty)
  | `([ty| $id:ident ]) => `($id)
  | `([ty| !($t) ]) => `($t)
  | `([ty| ($v) ]) => `([ty| $v])
  | `([ty| $a → $b ]) => `(Ty.arr [ty| $a] [ty| $b])
  | `([ty| $a × $b ]) => `(Ty.prod [ty| $a] [ty| $b])
  | `([ty| $a + $b ]) => `(Ty.cpd [ty| $a] [ty| $b])

open Lean in
def Ty.uex_inner : Syntax.Term → PrettyPrinter.UnexpandM (TSyntax `stlc_ty)
  | `([ty|$b]) => `(stlc_ty|$b)
  | `($t) => `(stlc_ty|!($t))

@[app_unexpander Ty.unit]
def Ty.unit.uex : Lean.PrettyPrinter.Unexpander
  | `($_p) => `([ty| 1])

@[app_unexpander Ty.empty]
def Ty.empty.uex : Lean.PrettyPrinter.Unexpander
  | `($_p) => `([ty| 0])

@[app_unexpander Ty.arr]
def Ty.arr.uex : Lean.PrettyPrinter.Unexpander
  | `($_p $a $b) => do
    let a ← uex_inner a
    let b ← uex_inner b
    let perenify : Lean.TSyntax `stlc_ty → Lean.PrettyPrinter.UnexpandM (Lean.TSyntax `stlc_ty)
      | `(stlc_ty|$c → $d) => `(stlc_ty|($c → $d))
      | `(stlc_ty|$c + $d) => `(stlc_ty|($c + $d))
      | v => `(stlc_ty|$v)
    let a ← perenify a
    `([ty| $a → $b])
  | _ => throw ()

@[app_unexpander Ty.prod]
def Ty.prod.uex : Lean.PrettyPrinter.Unexpander
  | `($_p $a $b) => do
    let a ← uex_inner a
    let b ← uex_inner b
    let perenify : Lean.TSyntax `stlc_ty → Lean.PrettyPrinter.UnexpandM (Lean.TSyntax `stlc_ty)
      | `(stlc_ty|$c → $d) => `(stlc_ty|($c → $d))
      | `(stlc_ty|$c + $d) => `(stlc_ty|($c + $d))
      | v => `(stlc_ty|$v)
    let a ← perenify a
    let b ← perenify b
    `([ty| $a × $b])
  | _ => throw ()

@[app_unexpander Ty.cpd]
def Ty.cpd.uex : Lean.PrettyPrinter.Unexpander
  | `($_p $a $b) => do
    let a ← uex_inner a
    let b ← uex_inner b
    let perenify : Lean.TSyntax `stlc_ty → Lean.PrettyPrinter.UnexpandM (Lean.TSyntax `stlc_ty)
      | `(stlc_ty|$c → $d) => `(stlc_ty|($c → $d))
      | `(stlc_ty|$c × $d) => `(stlc_ty|($c × $d))
      | v => `(stlc_ty|$v)
    let a ← perenify a
    let b ← perenify b
    `([ty| $a + $b])
  | _ => throw ()


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

