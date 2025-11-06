import Types.SysFHOAS.Stx

namespace SysFPHOAS

def letters : List String := ["a", "b", "c", "d", "e", "f", "g"]
def greek : List String := ["α", "β ", "γ ", "δ", "ε"]

def natToLetter (i : Nat) : String := letters.getD i "z"
def natToGreek (i : Nat) : String := greek.getD i "ζ"

def Type'.show (expr : Type' String) (level : Nat := 0) : String :=
  match expr with
  | .var s => s
  | .arr t1 t2 => "(" ++ Type'.show t1 level ++ " → " ++ Type'.show t2 level ++ ")"
  | .all  f=> "∀" ++ natToGreek level ++". " ++ Type'.show (f  (natToGreek level)) (level + 1)

def Term'.show {n} {ty : Type'.higher n String}
    (expr : Term' (T := String) (fun _ _ => String) n ty) (level : Nat := 0) (typelevel : Nat := 0) : String :=
  match expr with
  | .var s => s
  | .app t1 t2 => "(" ++ Term'.show t1 level typelevel ++ " " ++ Term'.show t2 level typelevel ++ ")"
  | .lam f => "(λ" ++ natToLetter level ++ "." ++ Term'.show (f (natToLetter level)) (level + 1) typelevel ++ ")"
  | @Term'.tapp _ _ _ f term1 t => 
    s!"({Term'.show term1 level typelevel} [{Type'.show (Type'.compress <| f t) typelevel}])"
  | @Term'.tlam _ _ _ f g => 
    s!"(Λ {natToGreek typelevel} . {Term'.show (g <| Type'.pvar (natToGreek typelevel)) level (typelevel + 1)})"


