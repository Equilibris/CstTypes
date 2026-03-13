open Lean in
instance : HAdd NumLit Nat NumLit where
  hAdd x n := Syntax.mkNumLit s!"{x.getNat + n}"

def Nat.split : ∀ n, ∃ a b : Nat, n = a + b := fun n => ⟨n, 0, rfl⟩

namespace List

inductive MemT : A → List A → Type
  | hd {a as} : MemT a (a :: as)
  | tl {bs a b} : MemT a bs → MemT a (b :: bs)

namespace MemT

def shift {A a} {l₁}
    : {l₂ : List A}
    → l₁.MemT a
    → (l₂ ++ l₁).MemT a
  | [], h => h
  | _ :: _, h => .tl (shift h)

def sandwitch_shift {A a l₁}
    : {l l₂ : List A}
    → (l ++ l₁).MemT a
    → (l ++ (l₂ ++ l₁)).MemT a
  | [], _, h => h.shift
  | _ :: _, _, .hd => .hd
  | _ :: _, _, .tl v => .tl v.sandwitch_shift

def remove
    {A v}
    : {l : List A}
    → l.MemT v
    → List A 
  | _ :: t, .hd => t
  | h :: _, .tl h' => h :: remove h'

def map {f : A → B}
    : {l : List A}
    → l.MemT v
    → (l.map f).MemT (f v)
  | _ :: _, .hd => .hd
  | _ :: _, .tl h => .tl h.map

/- def mapo {f : A → B} -/
/-     : {l : List A} -/
/-     → l.MemT v -/
/-     → (l.map f).MemT (f v) -/

end List.MemT

inductive HList {A} (f : A → Type _) : List A → Type _
  | nil : HList f []
  | cons {hd tl} : f hd → HList f tl → HList f (hd :: tl)

namespace HList

def get : {Γ : _} → List.MemT (A := A) t Γ → HList f Γ → f t
  | _ :: _, .hd, .cons h _ => h
  | _ :: _, .tl v, .cons _ tl => tl.get v

def map {f g} (h : ∀ {v}, f v → g v) : HList f Γ → HList g Γ
  | .nil => .nil
  | .cons hd tl => .cons (h hd) <| tl.map h

@[simp]
theorem get_map {f g : A → Type _}
    {h : ∀ {v}, f v → g v}
    : {ls : HList f Γ} → (i : List.MemT a Γ) → (ls.map h).get i = h (ls.get i)
  | .cons _ _, .hd => rfl
  | .cons hd tl, .tl h' => by
    change get h' (map h tl) = h (tl.get h')
    exact get_map _

def map' {Γm : A → B} {f g} (h : ∀ {v}, f v → g (Γm v)) : HList f Γ → HList g (Γ.map Γm)
  | .nil => .nil
  | .cons hd tl => .cons (h hd) <| tl.map' h

/- @[simp] -/
/- theorem get_map' -/
/-     {Γm : A → B} {f : A → Type _} {g : B → _} (h : ∀ {v}, f v → g (Γm v)) -/
/-     : {ls : HList f Γ} → (i : List.MemT a _) → (ls.map' h).get i = _ -/
/-   | .cons _ _, .hd => rfl -/
/-   | .cons hd tl, .tl h' => by  -/
/-     change get h' (map h tl) = h (tl.get h') -/
/-     exact get_map _ -/

end HList

inductive Vec (T : Type u) : Nat → Type u
  | nil : Vec T 0
  | cons : T → Vec T n → Vec T (n + 1)

namespace Vec

def get : Vec T n → Fin n → T
  | .cons h _, ⟨0, _⟩ => h
  | .cons _ tl, ⟨n+1, h'⟩ => tl.get ⟨n, Nat.succ_lt_succ_iff.mp h'⟩

@[simp]
theorem get_zero {h} {t : Vec T n} : (Vec.cons h t).get (0 : Fin (n+1)) = h := rfl
@[simp]
theorem get_succ {h} {t : Vec T n} {i : Fin n} : (Vec.cons h t).get (Fin.succ i) = t.get i := rfl

def map (f : A → B) : Vec A n → Vec B n
  | .nil => .nil
  | .cons hd tl => .cons (f hd) <| tl.map f

@[simp]
theorem get_map (f : A → B)
    : {ls : Vec A n} → (i : Fin n) → (ls.map f).get i = f (ls.get i)
  | .cons _ _, ⟨0, _⟩ => rfl
  | .cons _ _, ⟨n+1, h'⟩ => get_map f ⟨n, Nat.succ_lt_succ_iff.mp h'⟩

end Vec

