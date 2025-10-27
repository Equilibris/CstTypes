import Types.SysF.Expr.Stx
import Types.SysF.Expr.TRepl

namespace Expr

def bvarShift (shift skip : Nat) : Expr → Expr
  | .id n => .id $ if n < skip then n else n + shift
  | .app a b => .app (a.bvarShift shift skip) (b.bvarShift shift skip)
  | .lam ty body => .lam ty (body.bvarShift shift skip.succ)
  | .tapp expr ty => .tapp (expr.bvarShift shift skip) ty
  | .tlam body => .tlam (body.bvarShift shift skip)

def bvarUnShift (shift skip : Nat) : Expr → Expr
  | .id n => .id $ if n - shift < skip then n else n - shift
  | .app a b => .app (a.bvarUnShift shift skip) (b.bvarUnShift shift skip)
  | .lam ty body => .lam ty (body.bvarUnShift shift skip.succ)
  | .tapp expr ty => .tapp (expr.bvarUnShift shift skip) ty
  | .tlam body => .tlam (body.bvarUnShift shift skip)

def replace.bvar (bvarId idx_shift : Nat) (replace : Expr) : Expr :=
  match compare bvarId idx_shift with
  | .lt => .id bvarId
  | .eq => replace.bvarShift idx_shift 0
  | .gt => .id bvarId.pred

-- Replace also needs to add idx to every value within replace to ensure that the binders still point towards the right points
def replace (idx_shift tshift : Nat) (body replace : Expr) : Expr := match body with
  | .id n => Expr.replace.bvar n idx_shift (replace.tBvarShift tshift 0)
  | .app a b => .app (a.replace idx_shift tshift replace) (b.replace idx_shift tshift replace)
  | .lam ty body => .lam ty (body.replace idx_shift.succ tshift replace)
  | .tapp expr ty => .tapp (expr.replace idx_shift tshift replace) ty
  | .tlam body => .tlam (body.replace idx_shift tshift.succ replace)

def β (body repl : Expr) : Expr := (body.replace 0 0 repl)

end Expr
