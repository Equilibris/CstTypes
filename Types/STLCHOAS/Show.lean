import Types.STLCHOAS.Stx

namespace STLCHOAS

def letters : List String := ["a", "b", "c", "d", "e", "f", "g"]

def natToLetter (i : Nat) : String := letters.getD i "z"

def Ty.show (ty : Ty) : String :=
  match ty with
  | .arr t1 t2 => "(" ++ Ty.show t1 ++ " → " ++ Ty.show t2 ++ ")"
  | .unit => "1"
  | .empty => "0"
  | .prod t1 t2 => "(" ++ Ty.show t1 ++ " × " ++ Ty.show t2 ++ ")"
  | .cpd t1 t2 => "(" ++ Ty.show t1 ++ " ⊕ " ++ Ty.show t2 ++ ")"

def Term'.show {ty : Ty} (expr : Term' (fun _ => String) ty) (level : Nat := 0) : String :=
  match ty, expr with
  | _, .var s => s
  | _, .app t1 t2 => "(" ++ Term'.show t1 level ++ " " ++ Term'.show t2 level ++ ")"
  | .arr ty _, .lam f => "(λ" ++ natToLetter level ++ " : " ++ ty.show ++ ". " ++ Term'.show (f (natToLetter level)) (level + 1) ++ ")"
  | _, .unit => "()"
  | _, .empty t => "(absurd " ++ Term'.show t level ++ ")"
  | _, .mkP t1 t2 => "⟨" ++ Term'.show t1 level ++ ", " ++ Term'.show t2 level ++ "⟩"
  | _, .fst t => "(" ++ Term'.show t level ++ ".1)"
  | _, .snd t => "(" ++ Term'.show t level ++ ".2)"
  | _, .case t f g => "(case " ++ Term'.show t level ++ " of inl " ++ natToLetter level ++ " => " ++ Term'.show (f (natToLetter level)) (level + 1) ++ " | inr " ++ natToLetter (level + 1) ++ " => " ++ Term'.show (g (natToLetter (level + 1))) (level + 2) ++ ")"
  | _, .inl t => "(inl " ++ Term'.show t level ++ ")"
  | _, .inr t => "(inr " ++ Term'.show t level ++ ")"

end STLCHOAS
