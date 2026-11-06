/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SplicedFiniteSupport
public import WaveTurbulence.Foundations.Spine.SplicedTimeIntegrability
/-! Interchange the actual compactly supported decoration sum and spliced time integral. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Finset MeasureTheory

 theorem splicedSelectedKernel_eq_integral_sum {w d : ℕ} (G : Garden w) (hp : G.IsPlain)
    (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D) (C : SourceVine.CountingChoices G d)
    {L : ℝ} (hL : 0 < L) (γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) :
    splicedSelectedKernel G D C L γ η δ base roots =
      (coupling d L γ δ : ℂ) ^ G.order *
        ∫ t : GBranch G.tree → ℝ,
          ∑' z : splicedSelectedCarrier G D C L γ η base roots,
            splicedMomentumAmplitude G D L γ η base z.1.1 *
              (splicedTimeDomain G D.layer D.rootTime).indicator
                (fun t => ∏ v : GBranch G.tree,
                  Complex.exp ((Real.pi * splicedFrequency G D L γ δ base z.1.1 v * t v : ℝ) * Complex.I)) t := by
  classical
  letI : Fintype (splicedSelectedCarrier G D C L γ η base roots) :=
    (finite_splicedSelectedCarrier G hp D hD C hL γ η base roots).fintype
  unfold splicedSelectedKernel splicedFourierB
  congr 1
  simp only [tsum_fintype]
  rw [integral_finset_sum]
  · apply sum_congr rfl
    intro z _
    exact (integral_const_mul _ _).symm
  · intro z _
    exact (integrable_splicedFourierIntegrand G D.layer D.rootTime
      (splicedFrequency G D L γ δ base z.1.1)).const_mul _

end WaveTurbulence.LGSpine
