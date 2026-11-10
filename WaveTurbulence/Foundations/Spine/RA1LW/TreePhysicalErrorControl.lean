/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.TreePhysicalScalarSplit
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeCoefficientWeights
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LocalRemainderJoint
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickCorrectionEnvelope

/-! # Actual measurability and scalar envelope transport for the physical tree errors -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory ClassJR ApproxNT

/-- Both actual source remainder densities give a measurable complete physical error. -/
theorem stronglyMeasurable_treePhysicalErrorScalar_joint {d n : ℕ} (hd : 3 ≤ d) (hn : 0 < n)
    {L : ℝ} (hL : 0 < L) (δ γ : ℝ) (J : Finset (Fin n))
    {C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ}
    (hC : StronglyMeasurable (Function.uncurry C)) (z : (Fin n × Fin 2) → Fin d → ℤ) :
    StronglyMeasurable (fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      treePhysicalErrorScalar L δ γ J C p.1 p.2.1 p.2.2 z) := by
  exact ((stronglyMeasurable_localRemainder_joint hd hn L (2*δ) γ J hC z).add
    (stronglyMeasurable_normalizedWickCorrection_joint hL (2*δ) γ z J hC)).const_mul _

/-- No growth from the original4^-n conversion is needed in the combined source envelope. -/
theorem treePhysicalErrorScalar_norm_le {d n : ℕ} (L δ γ : ℝ) (J : Finset (Fin n))
    (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (lam : ℝ × ℝ)
    (β γ' : Fin n → Mom d) (z : (Fin n × Fin 2) → Fin d → ℤ)
    {P E₁ E₂ : ℝ}
    (hNT : ‖localRemainder L (2*δ) γ J C β γ' lam z‖ ≤
      P*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))*E₁)
    (hW : ‖normalizedWickCorrection L (2*δ) γ z β γ' J C lam‖ ≤
      P*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))*E₂) :
    ‖treePhysicalErrorScalar L δ γ J C lam β γ' z‖ ≤
      P*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))*(E₁+E₂) := by
  rw [treePhysicalErrorScalar,norm_mul]
  apply (mul_le_mul_of_nonneg_right (tree_inverse_four_pow_norm_le n) (norm_nonneg _)).trans
  rw [one_mul]
  apply (norm_add_le _ _).trans
  exact (add_le_add hNT hW).trans_eq (by ring)

end WaveTurbulence.RA1Leafwise
