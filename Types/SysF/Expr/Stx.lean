import Types.SysF.Ty

inductive Expr : Type
  | id : Nat → Expr
  | app : Expr → Expr → Expr
  | lam : Ty → Expr → Expr
  | tapp : Expr → Ty → Expr
  | tlam : Expr → Expr

declare_syntax_cat stx_expr

syntax ident : stx_expr
syntax num : stx_expr
syntax "!(" term ")" : stx_expr
syntax "(" stx_expr ")" : stx_expr
syntax stx_expr stx_expr : stx_expr
syntax stx_expr "[" stx_ty "]" : stx_expr
syntax "λ" ident* ":" stx_ty "." stx_expr : stx_expr
syntax "Λ" ident* "." stx_expr : stx_expr

syntax "[e!" num ident* "|" stx_expr "]" : term
syntax "[e|" stx_expr "]" : term

macro_rules
  | `([e! $_t | $v:num ]) => `(Expr.id $v)
  | `([e! $_t | $v:ident ]) => `($v)
  | `([e! $_t | !($t) ]) => `($t)
  | `([e! $_t | $a $b ]) => `(Expr.app [e! $_t | $a] [e! $_t | $b])
  | `([e! $_t | $a [$ty] ]) => `(Expr.tapp [e! $_t | $a] [t| $ty])
  | `([e! $t $h $ids*| $v:ident ]) =>
    if h.getId = v.getId then `(Expr.id $t)
    else `([e! $(t + 1) $ids* | $v:ident])
  | `([e! $t $ids*| ($v) ]) => `(([e! $t $ids* |$v]))
  | `([e! $t $ids*| λ : $ty. $body]) => `(Expr.lam [t|$ty] [e! $(t + 1) $ids*|$body] )
  | `([e! $t $ids*| λ $i : $ty . $body]) => `(Expr.lam [t| $ty] ([e! $(t + 1) $i $ids*|$body]))
  | `([e! $t $ids*| λ $i $is* : $ty . $body]) => `(Expr.lam [t| $ty] ([e! $t $i $ids*| λ $is* : $ty . $body]))
  | `([e! $t $ids*| Λ. $body]) => `(Expr.tlam ([e! $(t + 1) $ids*|$body]))
  | `([e! $t $ids*| Λ $i. $body]) => `(Expr.tlam ([e! $t $i $ids*|$body]))
  | `([e! $t $ids*| Λ $i $is*. $body]) => `(Expr.tlam ([e! $t $i $ids*| Λ $is*. $body]))
  | `([e| $v]) => `([e! 0 | $v])

open Lean in
def Expr.uex_inner : Syntax.Term → PrettyPrinter.UnexpandM (TSyntax `stx_expr)
  | `($i:ident) => `(stx_expr|$i:ident)
  | `([e|$b]) => `(stx_expr|$b)
  | `($t) =>`(stx_expr|!($t))

@[app_unexpander Expr.id]
def Expr.id.uex : Lean.PrettyPrinter.Unexpander
  | `($_p $num:num) => `([e| $num:num])
  | _ => throw ()

@[app_unexpander Expr.app]
def Expr.app.uex : Lean.PrettyPrinter.Unexpander
  | `($_p $a $b) => do
    let a ← uex_inner a
    let b ← uex_inner b
    let perenify : Lean.TSyntax `stx_expr → Lean.PrettyPrinter.UnexpandM (Lean.TSyntax `stx_expr)
      | `(stx_expr|λ $args* : $ty . $body) => `(stx_expr|(λ $args* : $ty . $body))
      | `(stx_expr|Λ $args* . $body) => `(stx_expr|(Λ $args* . $body))
      | v => `(stx_expr|$v)
    let a ← perenify a
    let b ← perenify b
    `([e| $a $b])
  | _ => throw ()

@[app_unexpander Expr.lam]
def Expr.lam.uex : Lean.PrettyPrinter.Unexpander
  | `($_p $ty $body) => do
    let body ← uex_inner body
    let ty ← Ty.uex_inner ty
    `([e| λ : $ty . $body])
  | _ => throw ()

@[app_unexpander Expr.tlam]
def Expr.tlam.uex : Lean.PrettyPrinter.Unexpander
  | `($_p $body) => do `([e| Λ. $(← uex_inner body)])
  | _ => throw ()

@[app_unexpander Expr.tapp]
def Expr.tapp.uex : Lean.PrettyPrinter.Unexpander
  | `($_p $expr $ty) => do
    let expr ← uex_inner expr
    let ty ← Ty.uex_inner ty
    `([e| $expr [$ty]])
  | _ => throw ()

example : [e|Λ. λ : 0 . 0] = (.tlam <| .lam (.id 0) <| .id 0) := rfl

