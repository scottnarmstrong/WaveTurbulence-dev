/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.ClockTransport
public import WaveTurbulence.Foundations.WaveB.FrozenB1

/-! # Removing the vacuous flower-parent subtype from actual couple/tree time integrals -/

public section
noncomputable section
open MeasureTheory
namespace WaveTurbulence.IncohInst

/-- A source garden without flowers integrates over all of its branching clocks. -/
@[expose] def noFlowerBranchEquiv {w : ℕ} (G : Garden w) (hf : ∀ ℓ, ¬ G.IsFlower ℓ) :
    G.FreeBranch ≃ GBranch G.tree where
  toFun b := b.1
  invFun b := ⟨b, fun ⟨ℓ, hℓ, _⟩ => hf ℓ hℓ⟩
  left_inv _b := Subtype.ext rfl
  right_inv _ := rfl

/-- The vacuous subtype clock transport, as an actual measurable equivalence. -/
@[expose] def noFlowerClockEquiv {w : ℕ} (G : Garden w) (hf : ∀ ℓ, ¬ G.IsFlower ℓ) :
    (G.FreeBranch → ℝ) ≃ᵐ (GBranch G.tree → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : GBranch G.tree => ℝ) (noFlowerBranchEquiv G hf)

/-- Removing the vacuous flower-parent condition costs no Jacobian. -/
theorem measurePreserving_noFlowerClockEquiv {w : ℕ} (G : Garden w) (hf : ∀ ℓ, ¬ G.IsFlower ℓ) :
    MeasurePreserving (noFlowerClockEquiv G hf) :=
  volume_measurePreserving_piCongrLeft (fun _ : GBranch G.tree => ℝ) (noFlowerBranchEquiv G hf)

/-- The source's extended time function is exactly the ordinary clock assignment. -/
theorem extendTime_eq_noFlowerClockEquiv {w : ℕ} (G : Garden w) (hf : ∀ ℓ, ¬ G.IsFlower ℓ)
    (s : ℝ) (τ : G.FreeBranch → ℝ) : G.extendTime s τ = noFlowerClockEquiv G hf τ := by
  funext b
  have hb : ¬ G.IsFlowerParent b := fun ⟨ℓ, hℓ, _⟩ => hf ℓ hℓ
  rw [Garden.extendTime, dite_eq_right hb]
  rfl

/-- B1's literal phase integral is the ordinary integral over the branching time domain. -/
theorem phaseIntegral_eq_of_noFlowers {w d : ℕ} (G : Garden w) (hf : ∀ ℓ, ¬ G.IsFlower ℓ)
    (L γ δ : ℝ) (D : Set (GBranch G.tree → ℝ)) (hD : MeasurableSet D) (s : ℝ) (κ : GNode G.tree → Mom d) :
    phaseIntegral L γ δ G D s κ = ∫ τ in D, phaseProd L γ δ G κ τ := by
  unfold phaseIntegral
  simp_rw [extendTime_eq_noFlowerClockEquiv G hf s]
  rw [(measurePreserving_noFlowerClockEquiv G hf).integral_comp
    (noFlowerClockEquiv G hf).measurableEmbedding]
  exact integral_indicator hD

end WaveTurbulence.IncohInst
