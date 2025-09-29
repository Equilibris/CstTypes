inductive Ty : Nat → Type
  | fn {n} : Ty n → Ty n → Ty n
  | id {n} : Fin n → Ty n
  | fa {n} : Ty n.succ → Ty n

declare_syntax_cat stx_ty

syntax ident : stx_ty
syntax num : stx_ty
syntax "!(" term ")" : stx_ty
syntax "(" stx_ty ")" : stx_ty
syntax stx_ty "→" stx_ty : stx_ty
syntax "Λ" ident* "." stx_ty : stx_ty

syntax "[t" num ident* "|" stx_ty "]" : term
syntax "[t|" stx_ty "]" : term

open Lean in
instance : HAdd NumLit Nat NumLit where
  hAdd x n := Syntax.mkNumLit s!"{x.getNat + n}"

macro_rules
  | `([t $_t | $v:num ]) => `(Ty.id $v)
  | `([t $_t | $v:ident ]) => `($v)
  | `([t $_t | !($t) ]) => `($t)
  | `([t $_t | $a → $b ]) => `(Ty.fn [t $_t | $a] [t $_t | $b])
  | `([t $t $h $ids*| $v:ident ]) =>
    if h.getId = v.getId then `(Ty.id $t)
    else `([t $(t + 1) $ids* | $v:ident])
  | `([t $t $ids*| ($v) ]) => `(([t $t $ids* |$v]))
  | `([t $t $ids*| Λ. $v]) => `(Ty.fa ([t $(t + 1) $ids*|$v]))
  | `([t $t $ids*| Λ $i. $v]) => `(Ty.fa ([t $t $i $ids*|$v]))
  | `([t $t $ids*| Λ $i $is*. $v]) => `(Ty.fa ([t $t $i $ids*| Λ $is*. $v]))
  | `([t| $v]) => `([t 0 | $v])

open Lean in
def Ty.uex_inner : Syntax.Term → PrettyPrinter.UnexpandM (TSyntax `stx_ty)
  | `($i:ident) => `(stx_ty|$i:ident)
  | `([t|$b]) => `(stx_ty|$b)
  | `($t) =>`(stx_ty|!($t))

@[app_unexpander Ty.id]
def Ty.id.uex : Lean.PrettyPrinter.Unexpander
  | `($_p $num:num) => `([t| $num:num])
  | _ => throw ()

@[app_unexpander Ty.fa]
def Ty.fa.uex : Lean.PrettyPrinter.Unexpander
  | `($_p $v) => do `([t| Λ. $(← uex_inner v)])
  | _ => throw ()

@[app_unexpander Ty.fn]
def Ty.fn.uex : Lean.PrettyPrinter.Unexpander
  | `($_p $a $b) => do
    let a ← uex_inner a
    let b ← uex_inner b
    let perenify : Lean.TSyntax `stx_ty → Lean.PrettyPrinter.UnexpandM (Lean.TSyntax `stx_ty)
      | `(stx_ty|Λ. $b) => `(stx_ty|(Λ. $b))
      | v => `(stx_ty|$v)
    let a ← perenify a
    let b ← perenify b
    `([t| $a → $b])
  | _ => throw ()

-- Add the type for free variable addition here
