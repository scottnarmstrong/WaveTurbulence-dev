/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.FourierAmplitudeSetup

/-! # The leading singular integral has a linear amplitude budget

Only the geometric box support and the actual Fourier mass enter; no
temporal-symbol moment is used in this size estimate.
-/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Finset
open scoped ENNReal

/-- Natural dimensional size of the literal iterated singular integral. -/
theorem exists_singular_integral_size_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      ∀ (lt : Fin n → Fin n → Prop) [IsStrictOrder (Fin n) lt] (xs ys : Fin n → Shift n),
      (∀ j, (xs j).Below lt j) → (∀ j, (ys j).Below lt j) →
      ∀ (a b : Fin n → Mom d) (lam : Fin n → ℝ), (∀ j, 1 ≤ lam j) →
      ∀ W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ, Continuous (Function.uncurry W) →
      (∀ x y, W x y ≠ 0 → (x,y) ∈ supportSet xs ys a b lam) →
      ∀ H : ℝ, 0 ≤ H →
      (∫⁻ τ : (Fin n → Mom d) × (Fin n → Mom d), ‖fourierW W τ.1 τ.2‖ₑ *
        ENNReal.ofReal (1+2*Real.pi*freqNorm τ.1 τ.2)) ≤ ENNReal.ofReal H →
      ∀ J : Finset (Fin n), ‖singInt J W‖ ≤ (∏ j, lam j)^(2*d)*C^n*H := by
  obtain ⟨K,hK,hb⟩ := exists_cellOp_bound hd
  let C : ℝ := 7^(2*d)*K
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro n hn lt _ xs ys hxs hys a b lam hlam W hWc hWs H hH hW J
  obtain ⟨hF,hinv,hI,hInt⟩ := fourierAmplitude_setup hn hxs hys hWc hWs hH hW
  have hFmass := integral_norm_fourierW_le hF hI hInt
  let Q := (cellBox_finite hxs hys a b lam).toFinset
  have hcell (pq : Fin n → (Fin d → ℤ) × (Fin d → ℤ)) :
      ‖∫ τ : (Fin n → Mom d) × (Fin n → Mom d), fourierW W τ.1 τ.2 *
        ∏ j, cellOp J j (NTSP.intVec (pq j).1) (NTSP.intVec (pq j).2) (τ.1 j) (τ.2 j)‖ ≤ H*K^n := by
    apply (norm_integral_le_of_norm_le (hF.norm.mul_const (K^n)) (Filter.Eventually.of_forall fun τ => ?_)).trans
      (show (∫ τ : (Fin n → Mom d) × (Fin n → Mom d), ‖fourierW W τ.1 τ.2‖*K^n) ≤ H*K^n by
        rw [integral_mul_const]
        exact mul_le_mul_of_nonneg_right hFmass (by positivity))
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply (Finset.norm_prod_le _ _).trans
    calc
      _ ≤ ∏ _j : Fin n, K := prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => hb J j _ _ _ _)
      _ = _ := by simp
  rw [singInt_eq hd J Q hF (W_eq_sum_appFac hxs hys hWs hinv J)]
  calc
    _ ≤ ∑ pq ∈ Q, ‖∫ τ : (Fin n → Mom d) × (Fin n → Mom d), fourierW W τ.1 τ.2 *
        ∏ j, cellOp J j (NTSP.intVec (pq j).1) (NTSP.intVec (pq j).2) (τ.1 j) (τ.2 j)‖ := norm_sum_le _ _
    _ ≤ ∑ _pq ∈ Q, H*K^n := sum_le_sum (fun pq _ => hcell pq)
    _ = (Q.card:ℝ)*(H*K^n) := by simp
    _ ≤ (7^(2*d*n)*(∏ j, lam j)^(2*d))*(H*K^n) :=
      mul_le_mul_of_nonneg_right (card_cells_le hxs hys a b hlam) (by positivity)
    _ = _ := by
      dsimp only [C]
      rw [pow_mul,mul_pow]
      ring

end WaveTurbulence.RegAsymp
