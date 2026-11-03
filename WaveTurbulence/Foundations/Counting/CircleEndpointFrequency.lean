/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.CircleEndpointBlocks
import Mathlib.Tactic

/-!
# From endpoint power-profile blocks to circular frequency bounds

The local block estimates have the exponent-pair scale
`n^kappa * R^(kappa/2) * U^(lambda-kappa/2)`. Their dyadic sum has the global
scale `n^kappa * R^lambda`, with an explicit finite constant. The local
hypothesis remains distinct from the shared VdCB exponent-pair predicate.
-/

public section

namespace WaveTurbulence.Counting

/-- Normalize the exact power weights on an endpoint-distance block. -/
theorem circle_endpoint_power_weight {R kappa lambda : ℝ} (hR : 0 < R) (j : ℕ) :
    R^(kappa/2)*(R/(2:ℝ)^(j+1))^(lambda-kappa/2) =
      R^lambda*(1/(2:ℝ)^(lambda-kappa/2))^(j+1) := by
  rw [Real.div_rpow hR.le (by positivity),← mul_div_assoc,← Real.rpow_add hR]
  have he : kappa/2+(lambda-kappa/2) = lambda := by ring
  rw [he]
  have hp : ((2:ℝ)^(j+1))^(lambda-kappa/2) = ((2:ℝ)^(lambda-kappa/2))^(j+1) := by
    rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),mul_comm,
      Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2)]
  rw [hp,one_div_pow]
  ring

/-- Conditional global circular-cap frequency bound from the actual
endpoint-profile block sums. There is no logarithmic loss at the terminal
cutoff. Only the six terminal samples use a trivial estimate. -/
theorem circle_outer_cap_exp_sum_le_of_endpoint_power_bounds
    {R T c C kappa lambda : ℝ} (hR : 1 ≤ R) (hC : 0 ≤ C)
    (hk : 0 ≤ kappa) (hk1 : kappa < 1) (hl : (1:ℝ)/2 ≤ lambda)
    (n : ℕ) (hn : 0 < n)
    (hblock : ∀ j : ℕ, 1 ≤ R/(2:ℝ)^(j+1) →
      ‖∑ x ∈ (integerInterval (c-R) (c+R)).filter (fun x : ℤ =>
        T < |(x:ℝ)-c| ∧ R/(2:ℝ)^(j+1) < R-|(x:ℝ)-c| ∧
          R-|(x:ℝ)-c| ≤ R/(2:ℝ)^j),
        NumberTheory.expPhase ((n:ℝ)*circleHeight R c x)‖ ≤
          C*(n:ℝ)^kappa*R^(kappa/2)*(R/(2:ℝ)^(j+1))^(lambda-kappa/2)) :
    ‖∑ x ∈ (integerInterval (c-R) (c+R)).filter (fun x : ℤ => T < |(x:ℝ)-c|),
      NumberTheory.expPhase ((n:ℝ)*circleHeight R c x)‖ ≤
        ((6+C/((2:ℝ)^(lambda-kappa/2)-1))*R^lambda)*(n:ℝ)^kappa := by
  let a : ℝ := lambda-kappa/2
  let q : ℝ := 1/(2:ℝ)^a
  have ha : 0 < a := by dsimp only [a]; linarith only [hl,hk1]
  have hpow : 1 < (2:ℝ)^a := Real.one_lt_rpow (by norm_num) ha
  have hpow0 : 0 < (2:ℝ)^a := by positivity
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := (div_lt_one hpow0).mpr hpow
  obtain ⟨J,hcut1,hcut2⟩ := exists_dyadic_unit_cutoff hR
  have hbound := norm_outer_cap_sum_le_of_dyadic_bounds
    (fun x : ℤ => (n:ℝ)*circleHeight R c x) J (le_trans zero_le_one hR) hcut2
    (by positivity : 0 ≤ (C*R^lambda)*(n:ℝ)^kappa) hq0 hq1
    (fun j hj => by
      have hU : 1 ≤ R/(2:ℝ)^(j+1) := hcut1.trans
        (div_le_div_of_nonneg_left (le_trans zero_le_one hR) (by positivity)
          (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.succ_le_of_lt hj)))
      apply (hblock j hU).trans_eq
      have he := circle_endpoint_power_weight (zero_lt_one.trans_le hR) (kappa := kappa) (lambda := lambda) j
      calc
        _ = C*(n:ℝ)^kappa*(R^(kappa/2)*(R/(2:ℝ)^(j+1))^(lambda-kappa/2)) := by ring
        _ = _ := by rw [he]; dsimp only [q,a]; ring)
  have hqe : q/(1-q) = 1/((2:ℝ)^a-1) := by
    dsimp only [q]
    field_simp
  rw [hqe] at hbound
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hs : 1 ≤ R^lambda*(n:ℝ)^kappa := by
    have hr := Real.one_le_rpow hR ((by norm_num : (0:ℝ) ≤ 1/2).trans hl)
    have hn := Real.one_le_rpow hn1 hk
    nlinarith only [hr,hn,mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hn)]
  calc
    _ ≤ 6+((C*R^lambda)*(n:ℝ)^kappa)*(1/((2:ℝ)^a-1)) := hbound
    _ ≤ 6*(R^lambda*(n:ℝ)^kappa)+((C*R^lambda)*(n:ℝ)^kappa)*(1/((2:ℝ)^a-1)) :=
      add_le_add (by linarith only [hs]) le_rfl
    _ = _ := by dsimp only [a]; ring

end WaveTurbulence.Counting
