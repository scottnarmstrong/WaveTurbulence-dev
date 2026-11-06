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

noncomputable def ladderBoundaryLabels {w d : ℕ} (G : Garden w) (S : Finset (GBranch G.tree))
    (z : GNode G.tree → (Fin d → ℤ)) : GardenDart G → (Fin d → ℤ) :=
  fun x => if G.molecule.InGroup S x then 0 else bondIndex G z x

 theorem boundary_labels_eq_iff {w d : ℕ} (G : Garden w) (S : Finset (GBranch G.tree))
    (z z' : GNode G.tree → (Fin d → ℤ)) :
    ladderBoundaryLabels G S z = ladderBoundaryLabels G S z' ↔
      ∀ x, ¬ G.molecule.InGroup S x → bondIndex G z x = bondIndex G z' x := by
  classical
  constructor
  · intro h x hx
    simpa only [ladderBoundaryLabels, if_neg hx] using congrFun h x
  · intro h
    funext x
    by_cases hx : G.molecule.InGroup S x
    · simp only [ladderBoundaryLabels, if_pos hx]
    · simpa only [ladderBoundaryLabels, if_neg hx] using h x hx

 theorem boundary_fiber_eq_localDecorations {w d : ℕ} (G : Garden w) (S : Finset (GBranch G.tree))
    (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration G d roots 0) :
    ((fun z' : GenDecoration G d roots 0 => ladderBoundaryLabels G S z'.1) ⁻¹'
      {ladderBoundaryLabels G S z.1}) = localLadderDecorations G S roots (bondIndex G z.1) := by
  ext z'
  exact boundary_labels_eq_iff G S z'.1 z.1

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
