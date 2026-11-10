/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3DPInv3
/-! **FINALCOUNT-G3: `HRun.dp`**, the dart-set invariant along a run. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {M₀ : Molecule V D₀}

theorem rtg_dp {step : HSt V D₀ → HSt V D₀ → Prop}
    (hstep : ∀ h h', step h h' → DPInv h → AncRel M₀ h.s h.anc → DPInv h' ∧ AncRel M₀ h'.s h'.anc)
    {x y : HSt V D₀} (h : Relation.ReflTransGen step x y) :
    DPInv x → AncRel M₀ x.s x.anc → DPInv y ∧ AncRel M₀ y.s y.anc := by
  induction h with
  | refl => exact fun a b => ⟨a, b⟩
  | tail _ hs ih => exact fun a b => (fun ⟨i, r⟩ => hstep _ _ hs i r) (ih a b)

end WaveTurbulence.FinalCountG3
