import Mathlib.Tactic.CongrExclamation
import Types.Utils

inductive Ty : Nat → Type
  | fn : Ty n → Ty n → Ty n
  | id : Fin n → Ty n
  | fa : Ty (n + 1) → Ty n

namespace Ty

def sandwitch (i : Fin (m + k)) : Fin (m + (n + k)) := ⟨i + n, by omega⟩

def gshift k (n : Nat) : Ty (m + k) → Ty (m + (n + k))
  | .id i => .id <| sandwitch i
  | .fa (h : Ty (m + (k + 1))) => .fa <| h.gshift _ _
  | .fn a b => .fn (a.gshift _ n) (b.gshift _ n)

@[simp]
theorem gshift_0 : {i : Ty (m + k)} → gshift k 0 i = cast (by simp) i
  | .id ⟨i, h⟩ => by
    unfold gshift
    refine eq_of_heq <| (heq_cast_iff_heq _ _ _).mpr ?_
    congr! <;> simp
  | .fa h => by
    unfold gshift
    refine eq_of_heq <| (heq_cast_iff_heq _ _ _).mpr ?_
    congr!
    · simp
    rw [gshift_0]
    simp
  | .fn a b => by
    unfold gshift
    refine eq_of_heq <| (heq_cast_iff_heq _ _ _).mpr ?_
    congr!
    · simp
    all_goals rw [gshift_0]
    all_goals simp

def shift (n : Nat) : Ty m → Ty (m + n) := gshift 0 n

@[simp]
theorem shift_fn : shift k (.fn a b) = .fn (shift k a) (shift k b) := by
  simp [shift, gshift]

theorem shift_shift : (v : Ty k)
    → shift n (shift m v)
    = cast (congr rfl (Nat.add_assoc _ _ _).symm) (shift _ v)
  | .id ⟨_,_⟩ => by
    simp [shift, gshift, sandwitch]
    sorry
  | _ => sorry

@[simp]
theorem shift_0 {i : Ty (m + k)} : shift 0 i = i := by simp [shift]

def subst (hList : Vec (Ty m) n) : Ty n → Ty m
  | .id i => hList.get i
  | .fn l r => .fn (l.subst hList) (r.subst hList)
  | .fa b => .fa
      <| b.subst
      <| .cons (.id ⟨0, Nat.zero_lt_succ m⟩)
      <| hList.map
      <| shift 1

namespace subst

def noopL : (n : Nat) → Vec (Ty n) n
  | 0 => .nil
  | n+1 => .cons (.id 0) <| (noopL n).map <| shift _

@[simp]
theorem noopL_get : {n : _} → {i : Fin n} → (noopL n).get i = .id i
  | n+1, ⟨0, _⟩ => by simp [noopL]
  | n+1, ⟨m+1, _⟩ => by
    simp only [noopL, Vec.get, Vec.get_map]
    rw [noopL_get]
    simp [shift, gshift, sandwitch]

@[simp]
theorem subst_noopL : {v : _} → subst (noopL n) v = v
  | .id _ => by simp [subst]
  | .fa h => by
    apply (fa.injEq _ _).mpr
    change subst (noopL _) h = h
    rw [subst_noopL]
  | .fn l r => by
    refine (fn.injEq _ _ _ _).mpr ⟨?_, ?_⟩
    <;> rw [subst_noopL]

@[simp]
theorem subst_nil : subst .nil v = v := subst_noopL

end subst

end Ty
