open Lean in
instance : HAdd NumLit Nat NumLit where
  hAdd x n := Syntax.mkNumLit s!"{x.getNat + n}"

def Nat.split : ∀ n, ∃ a b : Nat, n = a + b := fun n => ⟨n, 0, rfl⟩

