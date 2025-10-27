import Types.SysF.Expr.Valid
import Types.SysF.Expr.TReplCorrect
import Mathlib.Tactic.DepRewrite

namespace Expr

inductive SOp : Expr → Expr → Type
  | appLCongr {a b c} : SOp a b → SOp [e|a c] [e|b c]
  | appRCongr {a b c} : SOp a b → SOp [e|c a] [e|c b]
  | lamCongr  {a b t} : SOp a b → SOp [e|λ : t. a] [e|λ : t. b]

  | tappCongr {a b t} : SOp a b → SOp [e|a [t]] [e|b [t]]
  | tlamCongr {a b}   : SOp a b → SOp [e|Λ. a] [e|Λ. b]

  | tRed {a b}   : SOp [e|(Λ. a) [b]] (a.tReplace 0 b)
  | red  {a b t} : SOp [e|(λ : t. a) b] (a.replace 0 0 b)

theorem bvarShift_maintain_gen
    {n : Nat} {Γ₂ Γ₁ Γ : List (Ty.E n)} {body : Expr} {ty₂ : Ty.E n}
    (h : Typed n (Γ₂ ++ Γ) body ty₂)
    : Typed n (Γ₂ ++ Γ₁ ++ Γ) (bvarShift Γ₁.length Γ₂.length body) ty₂ :=
  match body with
  | .id idx => by
    rw [List.append_assoc, bvarShift, Typed_id]
    cases h; next i =>
    split
    case isTrue lt =>
      grind
    case isFalse ge =>
      simp only [Nat.not_lt] at ge
      have : Γ₂.length ≤ i := ge
      exists (by grind)
      simp only [Fin.getElem_fin]
      repeat rw [List.getElem_append_right (by omega)]
      congr 1
      omega
  | .lam ty body => by
    cases h; next hv h =>
    rw [←List.cons_append] at h
    exact .lam hv $ bvarShift_maintain_gen h
  | .app a b => by
    rw [bvarShift]
    cases h; next ha hb =>
    exact .app (bvarShift_maintain_gen hb) (bvarShift_maintain_gen ha)
  | .tapp expr ty => by
    rw [bvarShift]
    cases h; next hv h =>
    exact .tapp h $ bvarShift_maintain_gen hv
  | .tlam body => by
    cases h; next h =>
    apply Typed.tlam
    rw [List.map_append] at h
    let t := bvarShift_maintain_gen (Γ₁ := List.map (Ty.E.bvarShift 1 0) Γ₁) h
    repeat rw [←List.map_append] at t
    repeat rw [List.length_map] at t
    exact t

theorem bvarShift_maintain
    {n : Nat} {Γ₁ Γ : List (Ty.E n)} {body : Expr} {ty₂ : Ty.E n}
    (h : Typed n Γ body ty₂)
    : Typed n (Γ₁ ++ Γ) (bvarShift Γ₁.length 0 body) ty₂ := by
  change Typed n ([] ++ Γ₁ ++ Γ) (bvarShift Γ₁.length ([] : List (Ty.E n)).length body) ty₂
  exact bvarShift_maintain_gen h


theorem Typed_tBvarShift
    {n Γ arg x k sk}
    : Typed n Γ arg x
    → Typed (n + k)
        (List.map (Ty.E.bvarShift k sk) Γ)
        (tBvarShift k sk arg)
        (Ty.E.bvarShift k sk x)
  | .id _ => by simp [tBvarShift]
  | .tlam _ => sorry
  | .tapp hv h => by
    simp [tBvarShift]
    /- apply Typed.tapp (Ty.Valid.bvarShift hv) -/
    sorry
  | .lam hv h => by 
    sorry
  | .app hb ha => .app (Typed_tBvarShift hb) (Typed_tBvarShift ha)

theorem Typed_replace_gen
    {n k : Nat} {Γ' : List (Ty.E (n + k))} {Γ : List (Ty.E n)} {arg body : Expr}
    {ty₁ : Ty.E (n + k)} {x : Ty.E n}
    (argTy : Typed n Γ arg x)
    (base : Typed (n + k) (Γ' ++ List.map (Ty.E.bvarShift k 0) (x :: Γ)) body ty₁)
    : Typed (n + k) (Γ' ++ List.map (Ty.E.bvarShift k 0) Γ) (body.replace Γ'.length k arg) ty₁ :=
  match body with
  | .id idx => by
    rw [replace, replace.bvar, Nat.pred_eq_sub_one]
    split
    <;> rename_i heq
    <;> simp only [Nat.compare_eq_eq, Nat.compare_eq_gt, Nat.compare_eq_lt] at heq
    · cases base; next i =>
      rw [Typed_id]
      exists (by grind)
      grind
    · cases base; next i =>
      cases i
      dsimp at heq
      subst heq
      apply bvarShift_maintain 
      simp only [List.map_cons, Fin.getElem_fin, Nat.le_refl, List.getElem_append_right,
        Nat.sub_self, List.getElem_cons_zero]
      exact Typed_tBvarShift argTy
    · cases base; next i =>
      cases i; next n =>
      simp only [Fin.getElem_fin, Typed_id, List.length_append]
      exists (by grind)
      simp only [List.map_cons, List.length_append, List.length_cons, List.length_map] at heq n
      change (_ ++ ([_] ++ _))[_] = _
      repeat rw [List.getElem_append_right (by grind)]
      congr 1
      rw [List.length_singleton]
      omega
  | .lam ty body => by
    rw [replace, Nat.succ_eq_add_one]
    cases base; next hv base =>
    rw [←List.cons_append] at base
    exact .lam hv $ Typed_replace_gen argTy base
  | .app a b => by
    rw [replace]
    cases base; next ha hb =>
    exact .app (Typed_replace_gen argTy hb) (Typed_replace_gen argTy ha)
  | .tapp expr ty => by
    rw [replace]
    cases base; next hv h =>
    exact .tapp h $ Typed_replace_gen argTy hv
  | .tlam body => by
    rw [replace]
    cases base; next h =>
    apply Typed.tlam
    rw [List.map_append, List.map_cons, List.map_cons, List.map_map] at h
    simp only [Nat.succ_eq_add_one, Ty.E.bvarShift.comb, Ty.E.bvarShift.comb'] at h
    rw! (castMode := .all) [Nat.add_assoc] at h
    have := Typed_replace_gen argTy h
    rw! (castMode := .all) [←Nat.add_assoc] at this
    simp only [List.length_map, Nat.succ_eq_add_one, List.map_append, List.map_map,
        Ty.E.bvarShift.comb'] at this ⊢
    exact this

theorem Typed_tReplace_gen
    {n : Nat} {Γ : List (Ty.E n)} {body : Expr} {retT : Ty.E n.succ} {replT : Ty.E n}
    (h : Typed n.succ (Γ.map (Ty.E.bvarShift 1 0)) body retT)
    : Typed n Γ (body.tReplace 0 replT.ty) (retT.replace replT) :=
  match body with
  | .id idx => by
    cases h; next i =>
    simp [tReplace]
    have : Γ[idx]? = some (Γ.map (Ty.E.bvarShift 1 0))[idx] := by
      rw [List.getElem?_map]
      simp
    simp [Ty.E.replace]
    exact .id ⟨idx, i.isLt⟩
  | .lam ty body => by
    cases h; next hv h =>
    simp [tReplace]
    -- Type validity preservation needed
    sorry
  | .app a b => by
    cases h; next ha hb =>
    simp [tReplace]
    exact .app (Typed_tReplace_gen ha) (Typed_tReplace_gen hb)
  | .tapp expr ty => by
    cases h; next hv h =>
    simp [tReplace]
    -- Need to handle type application carefully
    sorry
  | .tlam body => by
    cases h; next h =>
    simp [tReplace]
    -- Need to handle type lambda carefully
    sorry

def valx
    {a b : Expr} {n Γ retT argT}
    (ha : Typed n (argT :: Γ) a retT)
    (hb : Typed n Γ b argT)
    : Typed n Γ (a.replace 0 b) retT :=
  Typed_replace_gen hb ha

def val {n Γ a b t} : Typed n Γ a t → SOp a b → Typed n Γ b t
  | .app ha hb, .red => by
    cases t
    cases ha
    exact valx ‹_› hb
  | .tapp hv h, .tRed => sorry
  | .app ha hb, .appLCongr hSOp => .app (val ha hSOp) hb
  | .app ha hb, .appRCongr hSOp => .app ha (val hb hSOp)
  | .tapp hv h, .tappCongr hSOp => .tapp hv (val h hSOp)
  | .lam hv h, .lamCongr hSOp => .lam hv (val h hSOp)
  | .tlam h, .tlamCongr hSOp => .tlam (val h hSOp)

