/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceLocalLadder
public import WaveTurbulence.Foundations.Spine.SplicedFiniteSupport
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
/-! Exact boundary-label fibers used when extracting a local ladder sum. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Finset
open scoped Classical

 theorem summable_spliced_amplitude_fourier {w d : ℕ} (G : Garden w) (hp : G.IsPlain)
    (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D) {L : ℝ} (hL : 0 < L)
    (γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) :
    Summable (fun z : GenDecoration G d roots 0 => splicedMomentumAmplitude G D L γ η base z.1 *
      splicedFourierB G D.layer D.rootTime (splicedFrequency G D L γ δ base z.1)) := by
  apply summable_of_hasFiniteSupport
  apply (finite_spliced_amplitude_support G hp D hD hL γ η base roots).subset
  intro z hz he
  exact hz (by dsimp only; rw [he, zero_mul])

end WaveTurbulence.LGSpine
