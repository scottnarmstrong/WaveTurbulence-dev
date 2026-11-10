/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Anc
/-! **FINALCOUNT-G3: the dart range of a state only shrinks.**  `Set.range s.down` is the set of darts of `M_sub` that are
still present.  Used for the model fact that darts removed in Step 1 are never final darts. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}

/-- `s'` has fewer darts than `s`. -/
def St.Sub (s' s : St.{u} V D₀) : Prop := Set.range s'.down ⊆ Set.range s.down

theorem St.Sub.refl (s : St.{u} V D₀) : St.Sub s s := fun _ h => h
theorem St.Sub.trans {a b c : St.{u} V D₀} (h1 : St.Sub a b) (h2 : St.Sub b c) : St.Sub a c := fun _ h => h2 (h1 h)

theorem St.Sub.cutSt (s : St.{u} V D₀) (v v₂ : V) (x₁ x₂ : s.D) (c₁ c₂ : Cls) :
    St.Sub (s.cutSt v v₂ x₁ x₂ c₁ c₂) s := fun _ h => h

theorem St.Sub.delSt (s : St.{u} V D₀) (P : V → Prop) [DecidablePred P] (h : PClosed s.M P) :
    St.Sub (s.delSt P h) s := by
  rintro _ ⟨x, rfl⟩
  exact ⟨x.1, rfl⟩

theorem St.Sub.withCls (s : St.{u} V D₀) (c : V → Cls) : St.Sub (s.withCls c) s := fun _ h => h

theorem HStep2.sub {h h' : HSt V D₀} (hs : HStep2 L γ η w κ h h') : St.Sub h'.s h.s := by
  cases hs with
  | tri T Q kp hQ hkp hsg hsim hcl hnz hι₀ hι₁ h3 =>
    refine (St.Sub.delSt _ _ _).trans ((St.Sub.withCls _ _).trans ((St.Sub.delSt _ _ _).trans ?_))
    exact (St.Sub.cutSt _ _ _ _ _ _ _).trans ((St.Sub.cutSt _ _ _ _ _ _ _).trans (St.Sub.cutSt _ _ _ _ _ _ _))

theorem HStep3.sub {h h' : HSt V D₀} (hs : HStep3 L γ η w κ h h') : St.Sub h'.s h.s := by
  cases hs with
  | cut v v₂ x₁ x₂ hc R kp hR hkp hε hsg hsim hι h3 => exact St.Sub.cutSt _ _ _ _ _ _ _

theorem HStep4.sub {h h' : HSt V D₀} (hs : HStep4 L w κ h h') : St.Sub h'.s h.s := by
  cases hs with
  | cut v v₂ x₁ x₂ hc hε hβ hnz h3 => exact St.Sub.cutSt _ _ _ _ _ _ _

theorem rtg_sub {step : HSt V D₀ → HSt V D₀ → Prop} (hstep : ∀ h h', step h h' → St.Sub h'.s h.s)
    {x y : HSt V D₀} (h : Relation.ReflTransGen step x y) : St.Sub y.s x.s := by
  induction h with
  | refl => exact St.Sub.refl _
  | tail _ hs ih => exact (hstep _ _ hs).trans ih

end WaveTurbulence.FinalCountG3
