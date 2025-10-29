import Types.STLCFull.Stx

namespace STLCFull

namespace Stx

def bvarShift (shift skip : Nat) : Stx → Stx
  | .bvar n => .bvar $ if n < skip then n else n + shift
  | .app fn arg => .app (fn.bvarShift shift skip) (arg.bvarShift shift skip)
  | .abs ty body => .abs ty (body.bvarShift shift skip.succ)
  | .prod a b => .prod (a.bvarShift shift skip) (b.bvarShift shift skip)
  | .fst expr => .fst (expr.bvarShift shift skip)
  | .snd expr => .snd (expr.bvarShift shift skip)

def bvarUnShift (shift skip : Nat) : Stx → Stx
  | .bvar n => .bvar $ if n - shift < skip then n else n - shift
  | .app fn arg => .app (fn.bvarUnShift shift skip) (arg.bvarUnShift shift skip)
  | .abs ty body => .abs ty (body.bvarUnShift shift skip.succ)
  | .prod a b => .prod (a.bvarUnShift shift skip) (b.bvarUnShift shift skip)
  | .fst expr => .fst (expr.bvarUnShift shift skip)
  | .snd expr => .snd (expr.bvarUnShift shift skip)

def replace.bvar (bvarId idx_shift : Nat) (replace : Stx) : Stx :=
  match compare bvarId idx_shift with
  | .lt => .bvar bvarId
  | .eq => replace.bvarShift idx_shift 0
  | .gt => .bvar bvarId.pred

def replace (idx_shift : Nat) (body replace : Stx) : Stx := match body with
  | .bvar n => Stx.replace.bvar n idx_shift replace
  | .app fn arg => .app (fn.replace idx_shift replace) (arg.replace idx_shift replace)
  | .abs ty body => .abs ty (body.replace idx_shift.succ replace)
  | .prod a b => .prod (a.replace idx_shift replace) (b.replace idx_shift replace)
  | .fst expr => .fst (expr.replace idx_shift replace)
  | .snd expr => .snd (expr.replace idx_shift replace)

def β (body repl : Stx) : Stx := (body.replace 0 repl)

end Stx

end STLCFull
