/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SignedNormSquare
public import WaveTurbulence.Foundations.XChain.RemainderCumulantL2Bound
/-! Signed coefficient remainders preserve the fixedpoint norm and measurability bounds. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory
open scoped ENNReal

theorem zpowSign_sub (ζ : ℤˣ) (z w : ℂ) :
    zpowSign ζ (z - w) = zpowSign ζ z - zpowSign ζ w := by
  unfold zpowSign
  split_ifs
  · rfl
  · exact map_sub (starRingEnd ℂ) z w

theorem norm_zpowSign (ζ : ℤˣ) (z : ℂ) : ‖zpowSign ζ z‖ = ‖z‖ := by
  unfold zpowSign
  split_ifs
  · rfl
  · exact norm_star z

theorem memLp_signed_bounded_remainder {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {a b : Ω → ℂ}
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (ζ : ℤˣ) {K : ℝ} (hK : ∀ᵐ ω ∂μ, ‖a ω - b ω‖ ≤ K) (q : ℝ≥0∞) :
    MemLp (fun ω => zpowSign ζ (a ω - b ω)) q μ := by
  have hm : AEStronglyMeasurable (fun ω => zpowSign ζ (a ω - b ω)) μ := by
    unfold zpowSign
    split_ifs
    · exact ha.sub hb
    · exact (ha.sub hb).star
  exact MemLp.of_bound hm K (hK.mono fun ω hω => (norm_zpowSign ζ _).trans_le hω)

end WaveTurbulence.Induct
