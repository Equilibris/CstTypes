import Types.SysF.Expr.Stx
import Types.SysF.Ty.Repl

namespace Expr

def tBvarShift (shift skip : Nat) : Expr → Expr
  | .id n => .id n
  | .app a b => .app (a.tBvarShift shift skip) (b.tBvarShift shift skip)
  | .lam ty body => .lam (ty.bvarShift shift skip) (body.tBvarShift shift skip)
  | .tapp expr ty => .tapp (expr.tBvarShift shift skip) (ty.bvarShift shift skip)
  | .tlam body => .tlam (body.tBvarShift shift skip.succ)

def tBvarUnShift (shift skip : Nat) : Expr → Expr
  | .id n => .id n
  | .app a b => .app (a.tBvarUnShift shift skip) (b.tBvarUnShift shift skip)
  | .lam ty body => .lam (ty.bvarUnShift shift skip) (body.tBvarUnShift shift skip)
  | .tapp expr ty => .tapp (expr.tBvarUnShift shift skip) (ty.bvarUnShift shift skip)
  | .tlam body => .tlam (body.tBvarUnShift shift skip.succ)

def tReplace.bvar (bvarId idx_shift : Nat) (replace : Ty) : Ty :=
  match compare bvarId idx_shift with
  | .lt => .id bvarId
  | .eq => replace.bvarShift idx_shift 0
  | .gt => .id bvarId.pred

def tReplace (idx_shift : Nat) (body : Expr) (replace : Ty) : Expr := match body with
  | .id n => .id n
  | .app a b => .app (a.tReplace idx_shift replace) (b.tReplace idx_shift replace)
  | .lam ty body => .lam (ty.replace idx_shift replace) (body.tReplace idx_shift replace)
  | .tapp expr ty => .tapp (expr.tReplace idx_shift replace) (ty.replace idx_shift replace)
  | .tlam body => .tlam (body.tReplace idx_shift.succ replace)

def tβ (body : Expr) (repl : Ty) : Expr := (body.tReplace 0 repl)

end Expr
