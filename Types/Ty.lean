import Types.TStx

def Ty.incr_free_vars (cutoff : Nat) (inc : Nat) : {n : Nat} → Ty n → Ty (n + inc)
  | n, .id i =>
    if i.val >= cutoff then
      .id ⟨i.val + inc, by
        have h : i.val < n := i.isLt
        omega⟩
    else
      Ty.id ⟨i.val, by omega⟩
  | n, .fn a b => .fn (incr_free_vars cutoff inc a) (incr_free_vars cutoff inc b)
  | n, .fa t => .fa <| cast (by congr; omega) (incr_free_vars cutoff.succ inc t)

-- Examples demonstrating incr_free_vars behavior

-- Example 1: Incrementing a free variable (index 0, cutoff 0)
example : ([t|0] : Ty 1).incr_free_vars 0 2 = ([t|2] : Ty 3) := rfl
example : ([t|0] : Ty 2).incr_free_vars 1 3 = ([t|0] : Ty 5) := rfl
example : ([t|1] : Ty 3).incr_free_vars 1 2 = ([t|3] : Ty 5) := rfl
example : ([t|0 → 1] : Ty 2).incr_free_vars 0 1 = ([t|1 → 2] : Ty 3) := rfl
example : ([t|0 → 2] : Ty 3).incr_free_vars 1 2 = ([t|0 → 4] : Ty 5) := rfl
example : ([t|Λ. 0 → 0] : Ty 1).incr_free_vars 0 1 = ([t|Λ. 0 → 0] : Ty 2) := rfl
example : ([t|Λ. 0 → 1] : Ty 2).incr_free_vars 0 1 = ([t|Λ. 0 → 2] : Ty 3) := rfl

def Ty.subst {n m} (idx : Fin (m + n)) (replacement : Ty n)  : Ty (m + n + 1) → Ty (m + n)
  | Ty.id i =>
    if h₁ : i.val = idx then
      cast (by congr 1; omega) (incr_free_vars 0 m replacement)
    else if h₂ : i.val > idx then
      .id ⟨i.val - 1, by omega⟩
    else
      .id ⟨i.val, by omega⟩
  | Ty.fn a b => Ty.fn (subst idx replacement a) (subst idx replacement b)
  | Ty.fa t => Ty.fa <| cast (by congr; omega) (subst idx.succ (replacement.incr_free_vars 0 1) cast (t))

