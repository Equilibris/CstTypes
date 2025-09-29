import Types.Ty.Stx

namespace Ty

def bvarShift (shift skip : Nat) : Ty → Ty
  | .id n => .id $ if n < skip then n else n + shift
  | .fn a b => .fn (a.bvarShift shift skip) (b.bvarShift shift skip)
  | .fa body => .fa (body.bvarShift shift skip.succ)

def bvarUnShift (shift skip : Nat) : Ty → Ty
  | .id n => .id $ if n - shift < skip then n else n - shift
  | .fn a b => .fn (a.bvarUnShift shift skip) (b.bvarUnShift shift skip)
  | .fa body => .fa (body.bvarUnShift shift skip.succ)

def replace.bvar (bvarId idx_shift : Nat) (replace : Ty) : Ty :=
  match compare bvarId idx_shift with
  | .lt => .id bvarId
  | .eq => replace.bvarShift idx_shift 0
  | .gt => .id bvarId.pred

-- Replace also needs to add idx to every value within replace to ensure that the binders still point towards the right points
def replace (idx_shift : Nat) (body replace : Ty) : Ty := match body with
  | .id n => Ty.replace.bvar n idx_shift replace
  | .fn a b => .fn (a.replace idx_shift replace) (b.replace idx_shift replace)
  | .fa t => .fa (t.replace idx_shift.succ replace)

def β (body repl : Ty) : Ty := (body.replace 0 repl)
