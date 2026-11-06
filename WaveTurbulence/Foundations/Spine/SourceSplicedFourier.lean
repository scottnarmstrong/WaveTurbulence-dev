/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceSplicedKernel
/-! The literal function B(alpha) in TARGET ladderl1old, L1994–L2001. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open MeasureTheory Set Finset

noncomputable def splicedFrequency {w d : ℕ} (G : Garden w) (D : SplicedKernelData G d)
    (L γ δ : ℝ) (base : Mom d) (z : GNode G.tree → (Fin d → ℤ)) : GBranch G.tree → ℝ :=
  fun v => (((G.sign v.toNode : ℤˣ) : ℤ) : ℝ) * δ * L ^ (2 * γ) *
    omegaNode G (cosetDecoration G L base z) v + D.frequency v

noncomputable def splicedFourierB {w : ℕ} (G : Garden w) (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ)
    (α : GBranch G.tree → ℝ) : ℂ :=
  ∫ t : GBranch G.tree → ℝ, (splicedTimeDomain G layer rootTime).indicator
    (fun t => ∏ v : GBranch G.tree, Complex.exp ((Real.pi * α v * t v : ℝ) * Complex.I)) t

theorem splicedTimeIntegral_eq_fourierB {w d : ℕ} (G : Garden w) (D : SplicedKernelData G d)
    (L γ δ : ℝ) (base : Mom d) (z : GNode G.tree → (Fin d → ℤ)) :
    splicedTimeIntegral G D L γ δ base z =
      splicedFourierB G D.layer D.rootTime (splicedFrequency G D L γ δ base z) := by
  unfold splicedTimeIntegral splicedFourierB
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  by_cases ht : t ∈ splicedTimeDomain G D.layer D.rootTime
  · simp only [Set.indicator_of_mem ht, phaseProd]
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro v _
    rw [← Complex.exp_add]
    congr 1
    unfold splicedFrequency
    push_cast
    ring
  · simp only [Set.indicator_of_notMem ht]

end WaveTurbulence.LGSpine
