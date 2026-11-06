/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SplicedFilteredBound
public import WaveTurbulence.Foundations.Spine.SplicedKernelFormula
public import WaveTurbulence.Foundations.Spine.FiniteSupportPartition
public import WaveTurbulence.Foundations.Spine.SplicedBoundaryLabels
/-! Exact reassembly from disjoint source-choice refinements, retaining the original phases. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Finset

/-- The actual kernel is the sum of disjoint refined pieces. The partition obligation is
combinatorial; each piece can be bounded using its containing admissible counting bin. -/
theorem splicedKernel_eq_sum_filtered {w d : ℕ} {J : Type*} [Fintype J]
    (G : Garden w) (hp : G.IsPlain) (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D)
    {L : ℝ} (hL : 0 < L) (γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (s : J → Set (GenDecoration G d roots 0))
    (hpart : ∀ z : GenDecoration G d roots 0, splicedMomentumAmplitude G D L γ η base z.1 ≠ 0 →
      ∃! j, z ∈ s j) :
    splicedKernel G D L γ η δ base roots =
      ∑ j : J, splicedFilteredKernel G D L γ η δ base roots (s j) := by
  classical
  let f : GenDecoration G d roots 0 → ℂ := fun z => splicedMomentumAmplitude G D L γ η base z.1 *
    splicedFourierB G D.layer D.rootTime (splicedFrequency G D L γ δ base z.1)
  have hs : Summable f := summable_spliced_amplitude_fourier G hp D hD hL γ η δ base roots
  have hu : ∀ z, f z ≠ 0 → ∃! j, z ∈ s j := by
    intro z hz
    apply hpart z
    intro he
    exact hz (by dsimp only [f]; rw [he, zero_mul])
  rw [splicedKernel_eq_amplitude_fourier]
  change (coupling d L γ δ : ℂ) ^ G.order * ∑' z, f z = _
  rw [tsum_eq_sum_partition f hs (fun j z => z ∈ s j) hu, mul_sum]
  rfl

end WaveTurbulence.LGSpine
