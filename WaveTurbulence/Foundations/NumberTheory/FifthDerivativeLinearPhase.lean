/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.FifthDerivativeScaleConstants
public import WaveTurbulence.Foundations.NumberTheory.LinearPhaseTower
import Mathlib.Tactic

/-!
# Uniform arbitrary linear perturbations of the dual-curve scale bound

The lattice shift of a translated circle produces an arbitrary linear dual
phase. The actual derivative tower shows that it does not change the pure
third/fourth/fifth derivative bound or any of its constants.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- The actual pure `(1/30,26/30)` derivative scale estimate is uniform in
both coefficients of an arbitrary added real linear phase. -/
theorem norm_exp_sum_add_linear_le_of_signed_derivative_scales
    (F : ℕ → ℝ → ℝ) (a : ℤ) (N : ℕ) (p q : ℝ) {Y T c K : ℝ}
    (hY : 1 ≤ Y) (hT : 0 < T) (hK : 1 ≤ K) (hTY : Y ≤ K*T) (hNY : (N:ℝ) ≤ Y) (hc : 1 ≤ c)
    (hd : ∀ r : ℕ, r < 5 → ∀ x ∈ Set.Icc ((a:ℝ)+1) ((a:ℝ)+N+2),
      HasDerivAt (F r) (F (r+1) x) x)
    (h3 : ∀ x ∈ Set.Icc ((a:ℝ)+1) ((a:ℝ)+N+2),
      F 3 x ∈ Set.Icc (-c*(T/Y^3)) (-(T/Y^3)))
    (h4 : ∀ x ∈ Set.Icc ((a:ℝ)+1) ((a:ℝ)+N+2),
      F 4 x ∈ Set.Icc (T/Y^4) (c*(T/Y^4)))
    (h5 : ∀ x ∈ Set.Icc ((a:ℝ)+1) ((a:ℝ)+N+2),
      F 5 x ∈ Set.Icc (-c*(T/Y^5)) (-(T/Y^5))) :
    ‖∑ n ∈ Finset.Ioc a (a+N), expPhase (F 0 n+p*(n:ℝ)+q)‖ ≤
      (K^2+16384*Real.sqrt c)*((T/Y)^((1:ℝ)/30)*Y^((26:ℝ)/30)) := by
  have he := norm_exp_sum_le_of_signed_derivative_scales_with_constant
    (addLinearPhaseTower F p q) a N hY hT hK hTY hNY hc
    (fun r hr x hx => addLinearPhaseTower_hasDerivAt p q r x (hd r hr x hx))
    (fun x hx => by
      simpa only [addLinearPhaseTower_of_two_le F p q (by norm_num : 2 ≤ 3)] using h3 x hx)
    (fun x hx => by
      simpa only [addLinearPhaseTower_of_two_le F p q (by norm_num : 2 ≤ 4)] using h4 x hx)
    (fun x hx => by
      simpa only [addLinearPhaseTower_of_two_le F p q (by norm_num : 2 ≤ 5)] using h5 x hx)
  simpa [addLinearPhaseTower,add_assoc] using! he

end WaveTurbulence.NumberTheory
