/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.PlanarShell
public import WaveTurbulence.Foundations.VdCB.CircleCountingBridge

/-! # A threshold form of the improved 27/41 annulus saving -/

public section
namespace WaveTurbulence.CountLemmas

/-- Both annulus branches are at most a fixed multiple of U whenever
`Qρ ≤ U` and `R² Qρ ≤ U^(244/81)`. This retains the strict gain when `Qρ=o(R)`. -/
theorem card_annulus_improved_threshold_le (s : Finset (Fin 2 → ℤ))
    (c : Mom 2) (b : Fin 2 → ℝ) {Q ρ R U : ℝ}
    (hQ : 2 ≤ Q) (hρ : 0 < ρ) (hρQ : ρ ≤ Q/4)
    (hW : 1 ≤ Q*ρ) (hR : 0 ≤ R) (hWU : Q*ρ ≤ U)
    (hbudget : R^2*(Q*ρ) ≤ U^((244 : ℝ)/81))
    (hbox : ∀ n ∈ s, ∀ i, |(n i : ℝ)-b i| ≤ R)
    (hann : ∀ n ∈ s, |‖latticePoint 1 n-c‖-Q| ≤ ρ) :
    (s.card : ℝ) ≤ (6*Real.pi+3*|VdCB.circleDiscrepancyConstant|+1924002)*U := by
  let W := Q*ρ
  let r := Q^((1 : ℝ)/3)
  have hQp : 0 < Q := by linarith only [hQ]
  have hr : 0 < r := Real.rpow_pos_of_pos hQp _
  have hUp : 0 < U := lt_of_lt_of_le zero_lt_one (hW.trans hWU)
  have hr3 : r^3 = Q := by
    simpa only [r,one_div,Nat.cast_ofNat] using Real.rpow_inv_natCast_pow hQp.le (by norm_num : (3 : ℕ) ≠ 0)
  have hr2 : Q^((2 : ℝ)/3) = r^2 := by
    dsimp only [r]
    rw [← Real.rpow_natCast,← Real.rpow_mul hQp.le]
    congr 1
    norm_num
  have hWp : 0 < W := lt_of_lt_of_le zero_lt_one hW
  have hU1 : 1 ≤ U := hW.trans hWU
  by_cases hs : Q^((27 : ℝ)/41) ≤ U
  · have hb := VdCB.card_annulus_le s c hQ hρ hρQ hann
    have herr := mul_le_mul_of_nonneg_right (le_abs_self VdCB.circleDiscrepancyConstant)
      (by positivity : 0 ≤ 3*Q^((27 : ℝ)/41))
    have hm := mul_le_mul_of_nonneg_left hWU (by positivity : 0 ≤ 6*Real.pi)
    have hn := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 3*|VdCB.circleDiscrepancyConstant|)
    nlinarith only [hb,herr,hm,hn,hUp]
  · have hUr2 : U^((82 : ℝ)/81) ≤ r^2 := by
      have hh := Real.rpow_le_rpow hUp.le (le_of_not_ge hs) (by norm_num : (0 : ℝ) ≤ 82/81)
      have heq : (Q^((27 : ℝ)/41))^((82 : ℝ)/81) = r^2 := by
        rw [← Real.rpow_mul hQp.le]
        norm_num
        exact hr2
      exact hh.trans_eq heq
    have hUg : U ≤ U^((82 : ℝ)/81) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hU1
        (by norm_num : (1 : ℝ) ≤ 82/81)
    have hUr : U ≤ r^2 := hUg.trans hUr2
    have hsr : Real.sqrt W ≤ W := Real.sqrt_le_iff.mpr ⟨hWp.le,by nlinarith only [hW]⟩
    have hmain : R*Real.sqrt W ≤ U*r := by
      have hUcube : U^((244 : ℝ)/81) ≤ (U*r)^2 := by
        have hh := mul_le_mul_of_nonneg_left hUr2 (sq_nonneg U)
        have heq : U^((244 : ℝ)/81) = U^2*U^((82 : ℝ)/81) := by
          rw [← Real.rpow_two,← Real.rpow_add hUp]
          norm_num
        rw [heq]
        exact hh.trans_eq (by ring)
      apply (sq_le_sq₀ (by positivity : 0 ≤ R*Real.sqrt W) (by positivity : 0 ≤ U*r)).mp
      calc
        _ = R^2*W := by rw [mul_pow,Real.sq_sqrt hWp.le]
        _ ≤ U^((244 : ℝ)/81) := hbudget
        _ ≤ _ := hUcube
    have hterm₂ : R/r*Real.sqrt W ≤ U := by
      apply (mul_le_mul_iff_right₀ hr).mp
      convert hmain using 1 <;> field_simp
    have hratio : W/r^2 ≤ 1 := (div_le_one (sq_pos_of_pos hr)).mpr (hWU.trans hUr)
    have hterm₁ : R*ρ*Real.sqrt W ≤ U := by
      calc
        _ = (R/r*Real.sqrt W)*(W/r^2) := by
          dsimp only [W]
          rw [← hr3]
          field_simp
        _ ≤ U*1 := mul_le_mul hterm₂ hratio (by positivity) hUp.le
        _ = U := mul_one _
    have hb := Counting.card_annulus_square_le s hQp hρ.le
      (by linarith only [hρQ,hQp]) hW hR (fun n hn => ⟨hbox n hn 0,hbox n hn 1⟩)
      (by intro n hn; rw [← Counting.norm_latticePoint_one_sub_eq_sqrt]; exact hann n hn)
    change (s.card : ℝ) ≤ 640000*(1+R*ρ+R/r)*Real.sqrt W at hb
    have hsU : Real.sqrt W ≤ U := hsr.trans hWU
    have hp := mul_nonneg Real.pi_pos.le hUp.le
    have hcp := mul_nonneg (abs_nonneg VdCB.circleDiscrepancyConstant) hUp.le
    nlinarith only [hb,hsU,hterm₁,hterm₂,hUp,hp,hcp]

end WaveTurbulence.CountLemmas
