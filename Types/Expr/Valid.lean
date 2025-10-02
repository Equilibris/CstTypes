import Types.Expr.ReplCorrect
import Types.Ty.E

namespace Expr

@[grind]
inductive Typed : (n : Nat) → List (Ty.E n) → Expr → Ty.E n → Type
  | id {n Γ} (i : Fin Γ.length) : Typed n Γ (.id i.val) Γ[i]
  | app {n Γ a b arg ret}
    : Typed n Γ a (.fn arg ret)
    → Typed n Γ b arg
    → Typed n Γ (.app a b) ret
  | lam {n Γ b arg ret} (h : Ty.Valid n arg)
    : Typed n (.mk arg h :: Γ) b ret
    → Typed n Γ (.lam arg b) (.fn (.mk arg h) ret)
  | tapp {n Γ b body arg} (h : Ty.Valid n arg)
    : Typed n Γ b (.fa body)
    → Typed n Γ (.tapp b arg) (body.replace (.mk arg h))
  | tlam {n Γ o arg}
    : Typed n.succ (Γ.map (Ty.E.bvarShift 1 0)) arg o
    → Typed n Γ (.tlam arg) (.fa o)

@[simp]
def Typed_id {n Γ idx t} : Typed n Γ (.id idx) t → (p : _) ×' t = Γ[Fin.mk idx p]
  | .id i => ⟨i.isLt, rfl⟩

theorem Typed.allEq {n Γ}
    : {t₁ t₂ e : _}
    → ∀ (a : Typed n Γ e t₁)
        (b : Typed n Γ e t₂),
        t₁ = t₂ ∧ a ≍ b
  | x, y, .id idx, a, b => by
    have ⟨fa, ha, eqa⟩ : ∃ f, ∃ h : x = Γ[Fin.mk idx f], a = (h ▸ .id (Fin.mk idx f)) := by
      cases a; simp
    have ⟨fb, hb, eqb⟩ : ∃ f, ∃ h : y = Γ[Fin.mk idx f], b = (h ▸ .id (Fin.mk idx f)) := by
      cases b; simp
    subst ha hb eqa eqb
    exact ⟨rfl, heq_of_eq rfl⟩
  | _, _, .tlam b, .tlam (o := ret₁) ha, .tlam (o := ret₂) hb => by
    obtain ⟨rfl, rfl⟩ := Typed.allEq (t₂ := ret₂) ha hb
    exact ⟨rfl, heq_of_eq rfl⟩
  | _, _, .tapp _ _, .tapp hv hb, .tapp hv' hb' => by
    have ⟨x, y⟩ := Typed.allEq hb hb'
    rw [Ty.E.fa.injEq] at x
    subst x y
    exact ⟨rfl, heq_of_eq rfl⟩
  | _, _, .lam ty b, ha, hb => by
    rcases ha with _|_|⟨hva, ha⟩
    rcases hb with _|_|⟨hvb, hb⟩
    obtain ⟨rfl, rfl⟩ := Typed.allEq ha hb
    exact ⟨rfl, heq_of_eq rfl⟩
  | _, _, .app _ _, .app (ret := ret₁) (arg := arg₁) ha hb,
                    .app (ret := ret₂) (arg := arg₂) ha' hb' => by
    obtain ⟨rfl, rfl⟩ := Typed.allEq hb hb'
    have ⟨x, y⟩ := Typed.allEq ha ha'
    simp only [Ty.E.fn.injEq, true_and] at x
    subst x y
    exact ⟨rfl, heq_of_eq rfl⟩

instance {n Γ e t} : Subsingleton (Typed n Γ e t) :=
  ⟨(Typed.allEq · · |>.right |> eq_of_heq)⟩



