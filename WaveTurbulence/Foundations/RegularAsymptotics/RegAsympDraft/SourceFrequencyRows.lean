/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.NodeRowBound
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceMomentumBridge

/-! # Actual pulled-back leaf frequencies and their order-uniform bound -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links

/-- Pull back independent leaf frequencies through the actual integer rows. -/
@[expose] def sourceFrequencyPullback {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ}
    (α : Fin (2*Q.links.length+1) → Mom d) (j : LinkCoord Q) : Mom d :=
  ∑ a, (sourceNodeRow hQ (plusLeafEquiv hQ hG a).val.toNode j : ℝ) • α a

/-- The root phase uses precisely the sum of the actual leaf frequencies. -/
theorem sourceFrequencyPullback_root {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ}
    (α : Fin (2*Q.links.length+1) → Mom d) :
    sourceFrequencyPullback hQ hG α none = ∑ a, α a := by
  simp only [sourceFrequencyPullback,sourceNodeRow_root_column,Int.cast_one,one_smul]

/-- Only a linear order loss occurs in pulling back one frequency moment. -/
theorem norm_sourceFrequencyPullback_le {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ}
    (α : Fin (2*Q.links.length+1) → Mom d) (j : LinkCoord Q) :
    ‖sourceFrequencyPullback hQ hG α j‖ ≤ (1+(Q.size:ℝ)) * ∑ a, ‖α a‖ := by
  unfold sourceFrequencyPullback
  calc
    _ ≤ ∑ a, ‖(sourceNodeRow hQ (plusLeafEquiv hQ hG a).val.toNode j : ℝ) • α a‖ := norm_sum_le _ _
    _ ≤ ∑ a, (1+(Q.size:ℝ)) * ‖α a‖ := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_smul,Int.norm_cast_real]
      exact mul_le_mul_of_nonneg_right (norm_sourceNodeRow_le hQ _ j) (norm_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

end WaveTurbulence.RegAsymp
