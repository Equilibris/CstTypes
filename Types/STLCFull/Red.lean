import Types.STLCFull.Stx
import Types.STLCFull.Repl
import Mathlib.Data.Rel

namespace STLCFull

inductive Red : Stx → Stx → Prop
  | app_fn  {fn fn' arg} : Red fn fn' → Red (.app fn arg) (.app fn' arg)
  | app_arg {fn arg arg'} : Red arg arg' → Red (.app fn arg) (.app fn arg')
  | abs     {ty body body'} : Red body body' → Red (.abs ty body) (.abs ty body')
  | prod_fst {a a' b} : Red a a' → Red (.prod a b) (.prod a' b)
  | prod_snd {a b b'} : Red b b' → Red (.prod a b) (.prod a b')
  | fst     {expr expr'} : Red expr expr' → Red (.fst expr) (.fst expr')
  | snd     {expr expr'} : Red expr expr' → Red (.snd expr) (.snd expr')
  | beta    {ty body v} : Red (.app (.abs ty body) v) (body.β v)
  | fst_beta {a b} : Red (.fst (.prod a b)) a
  | snd_beta {a b} : Red (.snd (.prod a b)) b

abbrev RedStar := Relation.ReflTransGen Red
abbrev RedPlus := Relation.TransGen Red
