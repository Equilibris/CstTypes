import Types.Ty.Valid

namespace Ty

/-- An extrinsically valid Ty -/
structure E (n : Nat) where
  mk ::
  ty : Ty
  val : Valid n ty

namespace E

variable {n : Nat}

@[match_pattern] abbrev fn : E n → E n → E n := (.mk _ $ .fn ·.val ·.val)
@[match_pattern] abbrev fa : E (n + 1) → E n := (.mk _ $ .fa ·.val)
@[match_pattern] abbrev id : Fin n     → E n := (.mk _ $ .id ·)

@[simp]
def fn.injEq {a b c d : E n} : E.fn a b = E.fn c d ↔ (a = c ∧ b = d) := by
  cases a; cases b; cases c; cases d; grind

@[simp]
def fa.injEq {a b : E n.succ} : E.fa a = E.fa b ↔ (a = b) := by
  cases a; cases b; grind

@[simp]
def id.injEq {a b : Fin n} : E.id a = E.id b ↔ (a = b) := by grind

def bvarShift (shift skip : Nat) (x : E n) : E (n + shift) :=
  .mk _ $ Valid.bvarShift (skip := skip) x.val

def replace (hbody : E n.succ) (hrepl : E n) : E n :=
  .mk _ $ Valid.replace hbody.val hrepl.val

