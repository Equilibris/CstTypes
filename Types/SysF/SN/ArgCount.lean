import Types.SysF.Ty.Stx

def ArgCount : Ty → Type
  | .fn a b  => ArgCount a → ArgCount b
  | .id _ => Nat
  | .fa x => Nat → ArgCount x

namespace ArgCount

mutual
def lt {z} (a b : ArgCount z) : Prop := match z with
  | .id _ => Nat.lt a b
  | .fa _ => ∀ n, lt (a n) (b n)
  | .fn x _ => ∀ x : ArgCount x, Monotonic x → lt (a x) (b x)

-- Not really a LE as it doest satisfy le ↔ lt ∧ neq
def le {z} (a b : ArgCount z) : Prop := match z with
  | .id _ => Nat.le a b
  | .fa _ => ∀ n, le (a n) (b n)
  | .fn _ _ => ∀ x, Monotonic x → le (a x) (b x)

def Monotonic {z} (v : ArgCount z) : Prop := match z with
  | .id _ => True
  | .fa _ => (∀ a b, a ≤ b → le (v a) (v b)) ∧ (∀ x, Monotonic (v x))
  | .fn argTy _ =>
    -- Might need to add the restrictions Monotonic a and Monotonic b
    (∀ a b : ArgCount argTy, Monotonic a → Monotonic b → le a b → le (v a) (v b)) ∧
      (∀ x : ArgCount argTy, Monotonic x → Monotonic (v x))
end

instance {z} : LT (ArgCount z) := ⟨lt⟩
instance {z} : LE (ArgCount z) := ⟨le⟩

def inc {v} (h : ArgCount v) : ArgCount v := match v with
  | .id _ => Nat.succ h
  | .fa _ => fun a => inc (h a)
  | .fn _ _ => fun a => inc (h a)

def addN {v} (h : ArgCount v) (n : Nat) : ArgCount v := match v with
  | .id _ => Nat.add h n
  | .fa _ => fun a => addN (h a) n
  | .fn _ _ => fun a => addN (h a) n

instance {v} : HAdd (ArgCount v) Nat (ArgCount v) := ⟨addN⟩
theorem add_def {v} {a : ArgCount v} {n : Nat} : a + n = addN a n := rfl

theorem addN_succ_inc {t n} {v : ArgCount t} : addN v (n + 1) = inc (addN v n) :=
  match t with
  | .id _ => rfl
  | .fn a b 
  | .fa x => by
    dsimp [addN, inc]
    apply funext
    intro v
    rw [addN_succ_inc]

theorem addN_zero {t} {v : ArgCount t} : addN v 0 = v :=
  match t with
  | .id _ => rfl
  | .fa _
  | .fn _ _ => by
    dsimp [addN, inc]
    apply funext
    intro x
    rw [addN_zero]

def zero {v} : ArgCount v := match v with
  | .id _ => Nat.zero
  | .fa _ | .fn _ _ => fun _ => ArgCount.zero
def naturalize {v} (h : ArgCount v) : Nat := match v with
  | .id _ => h
  | .fa _ => naturalize (h 0)
  | .fn _ _ => naturalize (h ArgCount.zero)

@[simp]
theorem naturalize_zero {v} : naturalize (@zero v) = 0 := match v with
  | .id _ => rfl
  | .fa _ | .fn _ _ => by dsimp [naturalize]; exact naturalize_zero

@[simp]
theorem naturalize_inc
    {z}
    (x : ArgCount z)
    : naturalize (inc x) = (naturalize x) + 1 :=
  match z with
  | .id _ => rfl
  | .fn _ _ | .fa _ => by dsimp [naturalize, inc]; rw [naturalize_inc]

@[simp]
theorem naturalize_addN {ty n} {a : ArgCount ty} : (addN a n).naturalize = a.naturalize + n :=
  match ty with
  | .id _ => rfl
  | .fa _ | .fn a b => by
    dsimp [addN, naturalize]
    exact naturalize_addN

theorem lt_trans {t} {a b c : ArgCount t} (hab : a < b) (hbc : b < c) : a < c :=
  match t with
  | .id _ => by
    change lt _ _ at hab hbc ⊢
    simp only [lt] at hab hbc ⊢
    exact Nat.lt_trans hab hbc
  | .fa _ => by
    change lt _ _ at hab hbc ⊢
    simp only [lt] at hab hbc ⊢
    intro x
    exact lt_trans (hab x) (hbc x)
  | .fn _ _ => by
    change lt _ _ at hab hbc ⊢
    simp only [lt] at hab hbc ⊢
    intro x xm
    exact lt_trans (hab x xm) (hbc x xm)

theorem le_trans {t} {a b c : ArgCount t} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  match t with
  | .id _ => by
    change le _ _ at hab hbc ⊢
    dsimp only [le] at hab hbc ⊢
    exact Nat.le_trans hab hbc
  | .fa _ => by
    change le _ _ at hab hbc ⊢
    dsimp only [le] at hab hbc ⊢
    intro x
    exact le_trans (hab x) (hbc x)
  | .fn _ _ => by
    change le _ _ at hab hbc ⊢
    dsimp only [le] at hab hbc ⊢
    intro x xm
    exact le_trans (hab x xm) (hbc x xm)

theorem le_of_lt {z} {a b : ArgCount z} : a < b → a ≤ b :=
  match z with
  | .id _ => fun h => by
    change lt _ _ at h
    change le _ _
    simp only [lt, Nat.lt_eq, le, Nat.le_eq] at h ⊢
    exact Nat.le_of_succ_le h
  | .fa _ => by
    change lt _ _ → le _ _
    simp only [lt, le]
    exact fun h x => le_of_lt (h x)
  | .fn _ _ => by
    change lt _ _ → le _ _
    simp only [lt, le]
    exact fun h x xm => le_of_lt (h x xm)

theorem self_le_self {z} {a : ArgCount z} : a ≤ a :=
  match z with
  | .id _ => by
    change le _ _
    simp only [le, Nat.le_eq, Nat.le_refl]
  | .fa _ => by
    change le _ _
    simp only [le]
    intro x
    exact self_le_self
  | .fn _ _ => by
    change le _ _
    simp only [le]
    intro x _
    exact self_le_self

theorem zero_Monotonic {s} : Monotonic (@zero s) := match s with
  | .id _ => by simp only [Monotonic]
  | .fa _ => by
    simp only [Monotonic, zero]
    exact ⟨fun _ _ _ => self_le_self, fun _ => zero_Monotonic⟩
  | .fn _ _ => by
    simp only [Monotonic, zero]
    exact ⟨fun _ _ _ _ _ => self_le_self, fun _ _ => zero_Monotonic⟩

theorem le_congr
    {f r}
    {aF bF : ArgCount (.fn f r)}
    {aR bR : ArgCount f}
    (hAFMono : Monotonic aF)
    (hARMono : Monotonic aR)
    (hBRMono : Monotonic bR)
    (hFLe : aF ≤ bF)
    (hRLe : aR ≤ bR)
    : aF aR ≤ bF bR := by
  change le _ _ at hFLe hRLe ⊢
  simp only [le] at hFLe hRLe
  simp only [Monotonic] at hAFMono hARMono
  exact le_trans (hAFMono.1 aR bR hARMono hBRMono hRLe) (hFLe bR hBRMono)

theorem lt_naturalize {v} {a b : ArgCount v} (h : a < b) : naturalize a < naturalize b :=
  match v with
  | .id _ => by
    change lt _ _ at h
    simp only [lt, naturalize] at h ⊢
    exact h
    /- h -/
  | .fa _ => by
    change lt _ _ at h
    simp only [ArgCount, lt, naturalize] at a b h ⊢
    exact lt_naturalize $ h 0
  | .fn _ _ => by
    change lt _ _ at h
    simp only [ArgCount, lt, naturalize] at a b h ⊢
    exact lt_naturalize $ h zero zero_Monotonic

theorem le_naturalize {v} {a b : ArgCount v} (h : a ≤ b) : naturalize a ≤ naturalize b :=
  match v with
  | .id _ => by
    change le _ _ at h
    simp only [le, naturalize] at h ⊢
    exact h
    /- h -/
  | .fa _ => by
    change le _ _ at h
    simp only [ArgCount, le, naturalize] at a b h ⊢
    exact le_naturalize $ h 0
  | .fn _ _ => by
    change le _ _ at h
    simp only [ArgCount, le, naturalize] at a b h ⊢
    exact le_naturalize $ h zero zero_Monotonic

@[simp]
theorem self_lt_addN {t n} {a : ArgCount t} (h : 0 < n) : a < addN a n :=
  match t with
  | .id _ => Nat.lt_add_of_pos_right h
  | .fa _ => fun _ => self_lt_addN h
  | .fn _ _ => fun _ _ => self_lt_addN h

@[simp]
theorem addN_lt_addN_right {t n} {a b : ArgCount t} (h : a < b) : addN a n < addN b n := match t with
  | .id _ => Nat.add_lt_add_right h _
  | .fa _ => fun z => addN_lt_addN_right (h z)
  | .fn _ _ => fun z zMono => addN_lt_addN_right (h z zMono)

@[simp]
theorem addN_lt_addN_left {t a b} {n : ArgCount t} (h : a < b) : addN n a < addN n b := match t with
  | .id _ => Nat.add_lt_add_left h n
  | .fa _ => fun _ => addN_lt_addN_left h
  | .fn _ _ => fun _ _ => addN_lt_addN_left h

@[simp]
theorem addN_le_addN_right {t n} {a b : ArgCount t} (h : (a ≤ b)) : (addN a n ≤ addN b n) := 
  match t with
  | .id _ => Nat.add_le_add_right h n
  | .fa _ => fun x => addN_le_addN_right (h x)
  | .fn _ _ => fun x xm => addN_le_addN_right (h x xm)

@[simp]
theorem addN_le_addN_left {t a b} {n : ArgCount t} (h : (a ≤ b)) : addN n a ≤ addN n b :=
  match t with
  | .id _ => Nat.add_le_add_left h n
  | .fa _ => fun _ => addN_le_addN_left h
  | .fn _ _ => fun _ _ => addN_le_addN_left h

-- I wish this could be an inductive but its too complex
theorem addN_Monotonic {s n} {v : ArgCount s} (h : Monotonic v)
    : Monotonic (addN v n) := match s with
  | .id _ => by simp only [Monotonic] at h v ⊢
  | .fa _ => 
    ⟨fun a b hLt => addN_le_addN_right (h.1 a b hLt), (addN_Monotonic $ h.2 ·)⟩
  | .fn _ _ =>
    ⟨fun a b aMono bMono hLt => addN_le_addN_right (h.1 a b aMono bMono hLt), (addN_Monotonic $ h.right · ·)⟩

theorem le_addN_lt_lt {t n m} {a b : ArgCount t} (hLe : a ≤ b) (hLt : n < m) : a.addN n < b.addN m :=
  match t with
  | .id _ => calc
      _ ≤ _ := (Nat.add_le_add_right hLe n)
      _ < _ := (Nat.add_lt_add_left hLt b)
  | .fa _ => fun x => le_addN_lt_lt (hLe x) hLt
  | .fn _ _ => fun x xm => le_addN_lt_lt (hLe x xm) hLt

theorem lt_sufficency
    {f t}
    {a b : ArgCount (.fn f t)} {c : ArgCount f}
    (cMono : Monotonic c)
    (h : a < b) : a c < b c := by
  change lt _ _ at h ⊢
  simp only [lt] at *
  exact h c cMono

theorem le_trans_lt
    {t}
    {a b c : ArgCount t}
    (h1 : a ≤ b)
    (h2 : b < c)
    : a < c :=
  match t with
  | .id _ => Nat.lt_of_le_of_lt h1 h2
  | .fa _ => fun x => le_trans_lt (h1 x) (h2 x)
  | .fn _ _ => fun x xm => le_trans_lt (h1 x xm) (h2 x xm)

end ArgCount

