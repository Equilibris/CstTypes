
namespace STLCFull

inductive Ty : Type where
  | unit  : Ty
  | arr   : Ty → Ty → Ty
  | prod  : Ty → Ty → Ty
deriving DecidableEq

inductive Stx
  | bvar (id : Nat)
  | app  (fn arg : Stx)
  | abs  (ty : Ty) (body : Stx)
  | prod : Stx → Stx → Stx
  | fst  : Stx → Stx
  | snd  : Stx → Stx
deriving DecidableEq

end STLCFull
