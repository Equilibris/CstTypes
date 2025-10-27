import Types.STLC.Stx
import Types.STLC.Red.Beta
import Mathlib.Data.Rel

namespace STLC

inductive Red : Stx → Stx → Prop
  | appl  {a a' b : Stx} : Red a a' → Red (.app a b ) (.app a' b)
  | appr  {a b b' : Stx} : Red b b' → Red (.app a b ) (.app a b')
  | congr {ty : Ty} {a a' : Stx} : Red a a' → Red (.abs ty a) (.abs ty a')
  | beta  {body v : Stx} : Red (.app (.abs _ body) v) (body.β v)

abbrev RedStar := Relation.ReflTransGen Red
abbrev RedPlus := Relation.TransGen Red

end STLC

