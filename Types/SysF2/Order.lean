import Types.SysF2.Ty
import Types.SysF2.Stx

def space {n} : Nat → Ty n → Vec Type n → Type
  | 0, _, _ => Nat
  | n+1, .fn a b, v => space n a v → space n b v
  | n+1, .fa a, v => ∀ t, space n a (.cons (space n t v) v)
  | _+1, .id id, v => v.get id

def obj (t : Ty n) (v : Vec Type n) : Type := ∀ n, space n t v

