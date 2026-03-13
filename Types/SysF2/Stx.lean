import Types.SysF2.Ty

inductive ITerm : (n : Nat) → List (Ty n) → Ty n → Type
  | var : ctx.MemT ty → ITerm n ctx ty
  | lam : ITerm n (dom :: ctx) ran → ITerm n ctx (.fn dom ran)
  | app : ITerm n ctx (.fn dom ran) → ITerm n ctx dom → ITerm n ctx ran
  | fa : ITerm (n + 1) (ctx.map <| Ty.shift _) v → ITerm n ctx (.fa v)
  | tapp t : ITerm n ctx (.fa ta) →  ITerm n ctx (ta.subst <| .cons t <| Ty.subst.noopL _)

namespace ITerm

def gshift {Γ Γ₁} Γ₂ : ITerm n (Γ ++ Γ₁) t → ITerm n (Γ ++ (Γ₂ ++ Γ₁)) t
  | .var h => .var h.sandwitch_shift
  | .lam (h : ITerm n (_ :: _ ++ _) _) => .lam (h.gshift Γ₂)
  | .app l r => .app (gshift _ l) (gshift _ r)
  | .tapp t h => .tapp t (gshift Γ₂ h)
  | .fa h =>
    .fa
      <| cast (by simp)
      <| gshift (List.map (Ty.shift 1) Γ₂)
      <| cast (congr (congr rfl List.map_append) rfl) h
termination_by v => sizeOf v
decreasing_by
all_goals dsimp
any_goals omega
· calc
    _ = sizeOf h := by congr <;> simp
    _ < _ := by omega

def shift {Γ₁} Γ₂ (v : ITerm n Γ₁ t) : ITerm n (Γ₂ ++ Γ₁) t :=
  gshift (Γ := []) Γ₂ v

def shift'
    : ITerm n Γ t
    → ITerm (n + k) (List.map (Ty.shift k) Γ) (Ty.shift k t)
  | .var v => .var v.map
  | .lam h => cast (congr rfl Ty.shift_fn.symm)
    <| .lam
    <| cast (congr (congr rfl List.map_cons) rfl)
    <| shift' h
  | .app l r => .app (cast (congr rfl Ty.shift_fn) l.shift') r.shift'
  | .tapp t h => by
    have := (t.shift k)
    sorry
  | .fa h => sorry

def subst (hList : HList (ITerm n Γ') Γ) : ITerm n Γ t → ITerm n Γ' t
  | .var h => hList.get h
  | .lam h => .lam <| h.subst <| .cons (.var .hd) <| hList.map <| .shift [_]
  | .app l r => .app (l.subst hList) (r.subst hList)
  | .tapp t h => .tapp _ (h.subst hList)
  | .fa h => .fa <| h.subst <| hList.map' shift'

end ITerm

