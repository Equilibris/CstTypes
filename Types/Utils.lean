open Lean in
instance : HAdd NumLit Nat NumLit where
  hAdd x n := Syntax.mkNumLit s!"{x.getNat + n}"

