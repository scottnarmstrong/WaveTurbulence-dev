/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.AnnulusThreshold
public import WaveTurbulence.Foundations.Counting.LatticeBox

/-! # Planar squared-energy bands, with unrestricted centers -/

public section
namespace WaveTurbulence.CountLemmas

/-- A planar squared-radius band of width `W ≥ 1`, localized in a translated
box of radius `R`, contains `O(U)` lattice points under the explicit threshold budgets. The constant and endpoints
are explicit; the energy center may be negative. -/
theorem card_planar_squared_shell_threshold_le (s : Finset (Fin 2 → ℤ))
    (c : Mom 2) (b : Fin 2 → ℝ) {K W R U : ℝ}
    (hW : 1 ≤ W) (hR : 0 ≤ R) (hWU : W ≤ U) (hbudget : R^2*W ≤ U^3)
    (hbox : ∀ n ∈ s, ∀ i, |(n i : ℝ)-b i| ≤ R)
    (hband : ∀ n ∈ s, |‖latticePoint 1 n-c‖^2-K| ≤ W) :
    (s.card : ℝ) ≤ (6*Real.pi+1924002)*U := by
  have hWp : 0 < W := lt_of_lt_of_le zero_lt_one hW
  by_cases hK : K < 4*W
  · let A := Real.sqrt (5*W)
    have hA : 0 ≤ A := Real.sqrt_nonneg _
    have hA2 : A^2 = 5*W := Real.sq_sqrt (by positivity)
    have hA1 : 1 ≤ A := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by linarith only [hW])
    have hc := Counting.card_le_of_coordinate_bounds s (fun i => c i) hA (by
      intro n hn i
      have hh := (abs_le.mp (hband n hn)).2
      have hnorm : ‖latticePoint 1 n-c‖ ≤ A := by
        nlinarith only [norm_nonneg (latticePoint 1 n-c),hA,hA2,hh,hK]
      have hi : |(n i : ℝ)-c i| ≤ ‖latticePoint 1 n-c‖ := by
        simpa [latticePoint] using PiLp.norm_apply_le (latticePoint 1 n-c) i
      exact hi.trans hnorm)
    have hpoly : (2*A+1)^2 ≤ 45*W := by
      have hm := mul_nonneg (sub_nonneg.mpr hA1) (by linarith only [hA1] : 0 ≤ 5*A+1)
      nlinarith only [hm,hA2]
    have hUp : 0 < U := hWp.trans_le hWU
    have hp : 0 ≤ Real.pi*U := mul_nonneg Real.pi_pos.le hUp.le
    nlinarith only [hc,hpoly,hp,hWU,hWp]
  · have hK4 : 4*W ≤ K := le_of_not_gt hK
    let Q := Real.sqrt K
    let ρ := W/Q
    have hKp : 0 < K := by linarith only [hK4,hWp]
    have hQp : 0 < Q := Real.sqrt_pos.mpr hKp
    have hQ2 : Q^2 = K := Real.sq_sqrt hKp.le
    have hQ : 2 ≤ Q := (Real.le_sqrt (by norm_num) hKp.le).mpr (by linarith only [hK4,hW])
    have hρ : 0 < ρ := div_pos hWp hQp
    have hρQ : ρ ≤ Q/4 := (div_le_iff₀ hQp).mpr (by nlinarith only [hK4,hQ2])
    have heq : Q*ρ = W := by dsimp only [ρ]; field_simp
    have hann : ∀ n ∈ s, |‖latticePoint 1 n-c‖-Q| ≤ ρ := by
      intro n hn
      apply (le_div_iff₀ hQp).mpr
      have hd := norm_nonneg (latticePoint 1 n-c)
      have hm := mul_le_mul_of_nonneg_left (show Q ≤ ‖latticePoint 1 n-c‖+Q from le_add_of_nonneg_left hd)
        (abs_nonneg (‖latticePoint 1 n-c‖-Q))
      calc
        _ ≤ |‖latticePoint 1 n-c‖-Q| * (‖latticePoint 1 n-c‖+Q) := hm
        _ = |‖latticePoint 1 n-c‖^2-K| := by
          rw [← abs_of_nonneg (by positivity : 0 ≤ ‖latticePoint 1 n-c‖+Q),← abs_mul,← hQ2]
          congr 1
          ring
        _ ≤ W := hband n hn
    simpa only [heq] using card_annulus_threshold_le s c b hQ hρ hρQ
      (by simpa only [heq] using hW) hR
      (by simpa only [heq] using hWU) (by simpa only [heq] using hbudget) hbox hann

end WaveTurbulence.CountLemmas
