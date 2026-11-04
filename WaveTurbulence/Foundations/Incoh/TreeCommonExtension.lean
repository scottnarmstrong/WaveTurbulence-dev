/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.TreeNormalizedMixtureSource
public import WaveTurbulence.Foundations.Incoh.TreeCausalGlobalSource
public import WaveTurbulence.Foundations.Incoh.TreeRootOrder

/-!
# One common tree extension for both Fourier regularity estimates

The actual causal root marginal equals the literal normalized phase
mixture on every external clock pair, including reversed pairs.
-/

public section
noncomputable section
open MeasureTheory

namespace WaveTurbulence.Incoh

/-- TARGET (incohproof26) and (incohproof28) estimate one actual extension globally. -/
theorem treeCausalExtension_eq_phaseKernel {d n m : ℕ} (R : RootCoordinates n)
    (Q : Mom d → Fin n → LayerLink d) (T : ∀ k, TreeClockFibers m (Q k))
    (hfirst : ∀ k, R.rootVertex 0 = (T k).selection.coordinates.rootVertex 0)
    (hlast : ∀ k, R.rootVertex 1 = (T k).selection.coordinates.rootVertex (Fin.last (m + 1)))
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) {χ : ℝ → ℝ} (hmχ : Measurable χ)
    (hc : Fourier.CutoffControl χ)
    (hχroot : ∀ k v, v ∈ R.rootBox (Q k) → ∀ j, χ (v j) = 1)
    (hχselected : ∀ k v, v ∈ (T k).selection.coordinates.rootBox (Q k) → ∀ j, χ (v j) = 1) :
    R.treeCausalExtension χ L γ δ Q (fun k => (T k).timeDomain) =
      fun t k => (T k).causalPhaseKernel χ L γ δ t := by
  funext t k
  by_cases ht : t 1 ≤ t 0
  · rw [R.treeCausalExtension_eq_weighted_source hL γ δ Q (fun k => (T k).timeDomain) k
      (T k).measurableSet_timeDomain (T k).timeDomain_subset_linkBoxes (hχroot k) ht]
    exact ((T k).causalPhaseKernel_eq_source R (hfirst k) (hlast k) hL γ δ hmχ hc (hχselected k) ht).symm
  · rw [R.treeCausalExtension_eq_zero_of_reverse χ L γ δ Q (fun k => (T k).timeDomain) k
      ((T k).root_order R (hfirst k) (hlast k)) (le_of_not_ge ht),
      (T k).causalPhaseKernel_eq_zero_of_reverse χ L γ δ (le_of_not_ge ht)]

end WaveTurbulence.Incoh
