/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Basic

/-! # Finite derivative bounds under contractive linear changes -/

public section
namespace WaveTurbulence.WeylSums

/-- A linear contraction does not enlarge the operator norm of any derivative.
This applies to the bilinear diagonal-to-original coordinate change. -/
theorem norm_iteratedFDeriv_comp_contraction_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {N j : ℕ}
    {f : E → ℂ} (hf : ContDiff ℝ N f) (A : E →L[ℝ] E) (hA : ‖A‖ ≤ 1)
    (x : E) (hj : j ≤ N) :
    ‖iteratedFDeriv ℝ j (f ∘ A) x‖ ≤ ‖iteratedFDeriv ℝ j f (A x)‖ := by
  rw [A.iteratedFDeriv_comp_right hf x (by exact_mod_cast hj)]
  have hh := (iteratedFDeriv ℝ j f (A x)).norm_compContinuousLinearMap_le (fun _ : Fin j => A)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hh
  refine hh.trans ?_
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg A) hA)

end WaveTurbulence.WeylSums
