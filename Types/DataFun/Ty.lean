
namespace DF

@[grind]
inductive FTy where
  | unit
  | prod : FTy → FTy → FTy
  | cop  : FTy → FTy → FTy
  | pow  : FTy → FTy
  | disc : FTy → FTy

@[grind]
inductive Ty where
  | unit
  | prod : Ty → Ty → Ty
  | cop  : Ty → Ty → Ty
  | fn   : Ty → Ty → Ty
  | pow  : FTy → Ty
  | disc : Ty → Ty

@[grind]
class inductive FTy.Lattice : FTy → Type
  | unit : Lattice .unit
  | prod : a.Lattice → b.Lattice → Lattice (.prod a b)
  | pow : a.Lattice → Lattice (.pow a)

@[grind]
class inductive Ty.Lattice : Ty → Type
  | unit : Lattice .unit
  | prod : a.Lattice → b.Lattice → Lattice (.prod a b)
  | pow : a.Lattice → Lattice (.pow a)

/- instance FTy.lDec : {a : FTy} → Decidable a.Lattice -/
/-   | .unit => .isTrue .unit -/
/-   | .prod a b => -/
/-     match a.lDec, b.lDec with -/
/-     | .isTrue a, .isTrue b => .isTrue <| .prod a b -/
/-     | .isFalse a, _ -/
/-     | _, .isFalse _ => .isFalse <| by grind -/
/-   | .pow a => -/
/-     match a.lDec with -/
/-     | .isTrue a => .isTrue <| .pow a -/
/-     | .isFalse a => .isFalse <| by grind -/
/-   | .cop _ _ -/
/-   | .disc _ => .isFalse (by grind) -/
/-  -/
/- instance Ty.lDec : {a : Ty} → Decidable a.Lattice -/
/-   | .unit => .isTrue .unit -/
/-   | .prod a b => -/
/-     match a.lDec, b.lDec with -/
/-     | .isTrue a, .isTrue b => .isTrue <| .prod a b -/
/-     | .isFalse a, _ -/
/-     | _, .isFalse _ => .isFalse <| by grind -/
/-   | .pow a => -/
/-     match a.lDec with -/
/-     | .isTrue a => .isTrue <| .pow a -/
/-     | .isFalse a => .isFalse <| by grind -/
/-   | .fn _ _ -/
/-   | .cop _ _ -/
/-   | .disc _ => .isFalse (by grind) -/

def FTy.toTy : FTy → Ty
  | .unit     => .unit
  | .cop a b  => .cop a.toTy b.toTy
  | .prod a b => .prod a.toTy b.toTy
  | .pow a    => .pow a
  | .disc a    => .disc a.toTy

end DF

