import Types.SysF.Ty.ReplCorrect

namespace Ty

def Valid (n : Nat) (t : Ty) : Prop :=
  ∀ k, RefSet t k → k < n

def maxV : Ty → Nat
  | .id b => b.succ
  | .fa x => x.maxV.pred
  | .fn a b => Nat.max a.maxV b.maxV

theorem Valid_maxV : {t : Ty} → Valid t.maxV t
  | .id x => by simp [Valid, maxV]
  | .fa x => by
    intro i
    have := @Valid_maxV x i.succ
    simp_all only [RefSet_fa, maxV, Nat.pred_eq_sub_one]
    grind only
  | .fn a b => by
    intro x
    have a := @Valid_maxV a x
    have b := @Valid_maxV b x
    simp_all only [RefSet_fn, maxV]
    grind only [= Nat.max_def, cases Or]

theorem lt_Valid {a b t} (h : a ≤ b) (hold : Valid a t) : Valid b t := by
  dsimp [Valid] at *
  grind only

theorem RefSet_Valid {n t} (hrs : ¬RefSet t n) (hv : Valid (n+1) t) : Valid n t := by
  dsimp [Valid] at *
  grind only

theorem not_Valid_lift {n t} (hv : ¬Valid (n+1) t) : ¬Valid n t := by
  dsimp [Valid] at *
  grind only

namespace Valid

def dec_lt {t} a b (hlt : a < b) (hVb : Valid b t) : Decidable (Valid a t) :=
  let x : Decidable (Valid (a.succ) t) :=
    if h : a.succ < b then
      dec_lt a.succ b h hVb
    else .isTrue (by grind only)
  if h : RefSet t a then
    .isFalse (fun h' => have := h' a h; by omega)
  else
    match x with
    | .isTrue h' => .isTrue $ RefSet_Valid h h'
    | .isFalse h' => .isFalse $ not_Valid_lift h'

instance dec {n t} : Decidable (Valid n t) :=
  if h : n < t.maxV then
    dec_lt _ _ h Valid_maxV
  else
    .isTrue (lt_Valid (by simp_all only [Nat.not_lt]) Valid_maxV)

variable {n}

def fn {A B} (a : Valid n A) (b : Valid n B) : Valid n [t|A → B] := by
  simp only [Valid, RefSet_fn] at *
  grind only

def fa {A} (a : Valid n.succ A) : Valid n [t|Λ. A] := by
  simp only [Valid, RefSet_fa] at *
  grind only

def id {n} (id : Fin n) : Valid n (.id id.val) := by
  simp [Valid]

theorem bvarShift {t : Ty} {n shift skip : Nat} (hv : Valid n t) : Valid (n + shift) (t.bvarShift shift skip) := by
  simp only [Valid] at *
  intro idx hk
  by_cases h : skip + shift ≤ idx
  · have := bvarShift_RefSet_general_rev' _ h hk
    grind only
  · have := bvarShift_RefSet_general_lt_rev _ (Nat.not_le.mp h) hk
    grind only

theorem replace' {body repl : Ty} {n idx : Nat}
    (hbody : Valid n body) (hrepl : Valid (n - idx) repl) :
    Valid n (body.replace idx repl) := fun k hk =>
  if h : idx ≤ k then
   match replace_RefSet_general_ge_rev h hk with
    | .inl h1 => Nat.lt_of_succ_lt <| hbody _ h1
    | .inr h2 => (Nat.sub_lt_sub_iff_right h).mp <| hrepl _ h2
  else hbody _ <| replace_RefSet_general_lt_rev (Nat.lt_of_not_le h) hk

theorem replace {body repl : Ty} {n : Nat}
    (hbody : Valid n.succ body) (hrepl : Valid n repl) :
    Valid n (body.replace 0 repl) := fun k hk =>
 match replace_RefSet_general_ge_rev (Nat.zero_le k) hk with
  | .inl h1 => Nat.succ_lt_succ_iff.mp (hbody k.succ h1)
  | .inr h2 => hrepl k h2

