/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.PlanarShell

/-! # A threshold form of the two-thirds annulus saving -/

public section
namespace WaveTurbulence.CountLemmas

/-- Both annulus branches are at most a fixed multiple of U whenever
`Qρ ≤ U` and `R² Qρ ≤ U³`. This retains the strict gain when `Qρ=o(R)`. -/
theorem card_annulus_threshold_le (s : Finset (Fin 2 → ℤ))
    (c : Mom 2) (b : Fin 2 → ℝ) {Q ρ R U : ℝ}
    (hQ : 2 ≤ Q) (hρ : 0 < ρ) (hρQ : ρ ≤ Q/4)
    (hW : 1 ≤ Q*ρ) (hR : 0 ≤ R) (hWU : Q*ρ ≤ U)
    (hbudget : R^2*(Q*ρ) ≤ U^3)
    (hbox : ∀ n ∈ s, ∀ i, |(n i : ℝ)-b i| ≤ R)
    (hann : ∀ n ∈ s, |‖latticePoint 1 n-c‖-Q| ≤ ρ) :
    (s.card : ℝ) ≤ (6*Real.pi+1924002)*U := by
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
  by_cases hs : r^2 ≤ U
  · have hb := Counting.card_annulus_le_two_thirds s c hQ hρ hρQ hann
    rw [hr2] at hb
    change (s.card : ℝ) ≤ 6*Real.pi*W+4002*r^2 at hb
    have hm := mul_le_mul_of_nonneg_left hWU (by positivity : 0 ≤ 6*Real.pi)
    have hn := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 4002)
    nlinarith only [hb,hm,hn,hUp]
  · have hUr : U ≤ r^2 := le_of_not_ge hs
    have hsr : Real.sqrt W ≤ W := Real.sqrt_le_iff.mpr ⟨hWp.le,by nlinarith only [hW]⟩
    have hmain : R*Real.sqrt W ≤ U*r := by
      have hUcube : U^3 ≤ (U*r)^2 := by
        have hh := mul_le_mul_of_nonneg_left hUr (sq_nonneg U)
        nlinarith only [hh]
      apply (sq_le_sq₀ (by positivity : 0 ≤ R*Real.sqrt W) (by positivity : 0 ≤ U*r)).mp
      calc
        _ = R^2*W := by rw [mul_pow,Real.sq_sqrt hWp.le]
        _ ≤ U^3 := hbudget
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
    nlinarith only [hb,hsU,hterm₁,hterm₂,hUp,hp]

end WaveTurbulence.CountLemmas
