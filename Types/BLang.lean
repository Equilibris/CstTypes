
namespace BLang

inductive Ty
  | bool
  | int

def Ty.denote : Ty → Type
  | .bool => Prop
  | .int => Int

namespace BLang1

inductive Stx : Ty → Type
  | true : Stx .bool
  | false : Stx .bool
  | n (x : Int) : Stx .int
  | lt : Stx .int → Stx .int → Stx .bool
  | add : Stx .int → Stx .int → Stx .int
  | and : Stx .bool → Stx .bool → Stx .bool
  | neg : Stx .bool → Stx .bool

namespace Stx

inductive Val : {t : _} → Stx t → Type
  | true  : Val .true
  | false : Val .false
  | n {n} : Val (.n n)

instance {t} {s : Stx t} : Subsingleton (Val s) where
  allEq
    | .true, .true => rfl
    | .false, .false => rfl
    | .n, .n => rfl

def denote : {t : Ty} → Stx t → t.denote
  | .bool, .true => True
  | .bool, .false => False
  | .int, .n x => x
  | .bool, .lt a b => Int.lt (a.denote : Int) (b.denote : Int)
  | .int, .add a b => Int.add a.denote b.denote
  | .bool, .and a b => a.denote ∧ b.denote
  | .bool, .neg a => ¬a.denote

inductive Red : {t : _} → Stx t → Stx t → Prop
  | ltCongr   {e e' l} : Red e e' → Red (.lt e l) (.lt e' l)
  | ltCongr'  {e e' n} : Red e e' → Red (.lt (.n n) e) (.lt (.n n) e')
  | ltLt      {a b}    : a < b → Red (.lt (.n a) (.n b)) .true
  | ltGe      {a b}    : b ≤ a → Red (.lt (.n a) (.n b)) .false
  | addCongr  {e e' l} : Red e e' → Red (.add e l) (.add e' l)
  | addCongr' {e e' n} : Red e e' → Red (.add (.n n) e) (.add (.n n) e')
  | add       {a b}    : Red (.add (.n a) (.n b)) (.n <| a + b)
  | andCongr  {e e' l} : Red e e' → Red (.and e l) (.and e' l)
  | andTrue   {e}      : Red (.and .true e) e
  | andFalse  {e}      : Red (.and .false e) .false
  | negCongr  {e e'}   : Red e e' → Red (.neg e) (.neg e')
  | negTrue            : Red (.neg .true) .false
  | negFalse           : Red (.neg .false) .true


end Stx

end BLang1

def Ctx.denote (Γ : List Ty) : Type :=
  (v : Fin Γ.length) → (Γ[v]).denote

instance : Inhabited (Ctx.denote []) where
  default x := x.elim0

namespace BLang2

inductive Stx : List Ty → Ty → Type
  | true {Γ} : Stx Γ .bool
  | false {Γ} : Stx Γ .bool
  | n {Γ} (x : Nat) : Stx Γ .int
  | lt {Γ} : Stx Γ .int → Stx Γ .int → Stx Γ .bool
  | add {Γ} : Stx Γ .int → Stx Γ .int → Stx Γ .int
  | and {Γ} : Stx Γ .bool → Stx Γ .bool → Stx Γ .bool
  | neg {Γ} : Stx Γ .bool → Stx Γ .bool
  | lete {Γ t t'} : Stx Γ t → Stx (t :: Γ) t' → Stx Γ t'
  | var {Γ} (idx : Fin Γ.length) : Stx Γ Γ[idx]

def Stx.denote {Γ} (γ : Ctx.denote Γ): {t : Ty} → Stx Γ t → t.denote
  | _, .true => True
  | _, .false => False
  | _, .n x => Int.ofNat x
  | _, .lt a b => Int.lt (a.denote γ) (b.denote γ)
  | _, .add a b => Int.add (a.denote γ) (b.denote γ)
  | _, .and a b => (a.denote γ) ∧ (b.denote γ)
  | _, .neg a => ¬(a.denote γ)
  | _, .lete val body => body.denote fun
    | ⟨0, _⟩ => val.denote γ
    | ⟨v+1, p⟩ => γ ⟨v, by grind⟩
  | _, .var idx => γ idx

/- declare_syntax_cat stx_blang2 -/

/- syntax "true" : stx_blang2 -/
/- syntax "false" : stx_blang2 -/
/- syntax num : stx_blang2 -/
/- syntax ident : stx_blang2 -/
/- syntax "!(" term ")" : stx_blang2 -/
/- syntax "(" stx_blang2 ")" : stx_blang2 -/
/- syntax stx_blang2 "<" stx_blang2 : stx_blang2 -/
/- syntax stx_blang2 "+" stx_blang2 : stx_blang2 -/
/- syntax stx_blang2 "&&" stx_blang2 : stx_blang2 -/
/- syntax "!" stx_blang2 : stx_blang2 -/
/- syntax "let" ident "=" stx_blang2 "in" stx_blang2 : stx_blang2 -/

/- syntax "[bl2!" "(" term ")" ident* "|" stx_blang2 "]" : term -/
/- syntax "[bl2|" stx_blang2 "]" : term -/

/- macro_rules -/
/-   | `([bl2! ($_) | true ]) => `(Stx.true) -/
/-   | `([bl2! ($_) | false ]) => `(Stx.false) -/
/-   | `([bl2! ($_) | $v:num ]) => `(Stx.n $v) -/
/-   | `([bl2! ($_) | $v:ident ]) => `($v) -/
/-   | `([bl2! ($_) | !($t) ]) => `($t) -/
/-   | `([bl2! ($Γ) | ($v) ]) => `([bl2! ($Γ) |$v]) -/
/-   | `([bl2! ($Γ) | $a < $b ]) => `(Stx.lt [bl2! ($Γ) | $a] [bl2! ($Γ) | $b]) -/
/-   | `([bl2! ($Γ) | $a + $b ]) => `(Stx.add [bl2! ($Γ) | $a] [bl2! ($Γ) | $b]) -/
/-   | `([bl2! ($Γ) | $a && $b ]) => `(Stx.and [bl2! ($Γ) | $a] [bl2! ($Γ) | $b]) -/
/-   | `([bl2! ($Γ) | ! $a ]) => `(Stx.neg [bl2! ($Γ) | $a]) -/
/-   | `([bl2! ($Γ) | let $x = $val in $body ]) => `(Stx.lete [bl2! ($Γ) | $val] [bl2! ($Γ) $x | $body]) -/
/-   | `([bl2! ($Γ) $h $ids*| $v:ident ]) => -/
/-     if h.getId = v.getId then `(Stx.var ⟨0, by simp⟩) -/
/-     else `([bl2! ($Γ) $ids* | $v:ident]) -/
/-   | `([bl2| $v]) => `([bl2! ([]) | $v]) -/

/- end BLang2 -/

#eval (Stx.lete (Γ := []) (.n 00) (.add (.var ⟨0, by grind⟩) (.var ⟨0, by grind⟩))).denote default

