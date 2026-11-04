/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.ContinuousCellSize
public import WaveTurbulence.Foundations.RegAsymp.FourierAmplitudeSetup

/-! # Global continuous NT size with no temporal moment hypothesis -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Finset
open scoped ENNReal ContDiff

/-- Finite cell decomposition preserves the natural μ⁻ⁿ size, with only
a geometric dimensional cost and the actual linear Fourier mass. -/
theorem exists_continuous_integral_size_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      ∀ (lt : Fin n → Fin n → Prop) [IsStrictOrder (Fin n) lt] (xs ys : Fin n → Shift n),
      (∀ j, (xs j).Below lt j) → (∀ j, (ys j).Below lt j) →
      ∀ (a b : Fin n → Mom d) (lam : Fin n → ℝ), (∀ j, 1 ≤ lam j) →
      ∀ W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ, Continuous (Function.uncurry W) →
      (∀ x y, W x y ≠ 0 → (x,y) ∈ supportSet xs ys a b lam) →
      ∀ H : ℝ, 0 ≤ H →
      (∫⁻ τ : (Fin n → Mom d) × (Fin n → Mom d), ‖fourierW W τ.1 τ.2‖ₑ *
        ENNReal.ofReal (1+2*Real.pi*freqNorm τ.1 τ.2)) ≤ ENNReal.ofReal H →
      ∀ (J : Finset (Fin n)) (Ψ : EuclideanSpace ℝ {j // j ∉ J} → ℂ) (D : ℕ → ℝ),
      ContDiff ℝ ∞ Ψ → WordDerivL1 Ψ D → (∀ k, 0 ≤ D k) →
      ∀ D0 : ℝ, (∫ Ω, ‖Ψ Ω‖) ≤ D0 → ∀ μ : ℝ, 1 < μ →
      ‖approxInt μ W (resProfile J Ψ)‖ ≤ (∏ j, lam j)^(2*d)*(C/μ)^n*D0*H := by
  obtain ⟨K,hK,hcell⟩ := exists_continuous_cell_size_bound d hd
  let C : ℝ := 7^(2*d)*K
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro n hn lt _ xs ys hxs hys a b lam hlam W hWc hWs H hH hW J Ψ D hΨ hD hD0 D0 hD0' μ hμ
  have := isFiniteMeasureOnCompacts_pairs (n := n) (d := d)
  have hμ0 : 0 < μ := by linarith
  have hD00 : 0 ≤ D0 := (integral_nonneg (fun _ => norm_nonneg _)).trans hD0'
  obtain ⟨hF,hinv,hI,hInt⟩ := fourierAmplitude_setup hn hxs hys hWc hWs hH hW
  have hFmass := integral_norm_fourierW_le hF hI hInt
  let Q := (cellBox_finite hxs hys a b lam).toFinset
  let P := fun z : (Fin n → Mom d) × (Fin n → Mom d) =>
    resProfile J Ψ (fun j => μ*inner ℝ (z.1 j) (z.2 j))
  have hPc : Continuous P := (continuous_resProfile J hΨ.continuous).comp
    (continuous_pi (fun j => continuous_const.mul
      (((continuous_apply j).comp continuous_fst).inner ((continuous_apply j).comp continuous_snd))))
  have hhm (pq) : Continuous (fun z : (Fin n → Mom d) × (Fin n → Mom d) =>
      cellWeight pq z.1 z.2*P z) := (continuous_cellWeight pq).mul hPc
  have hhs (pq) : HasCompactSupport (fun z : (Fin n → Mom d) × (Fin n → Mom d) =>
      cellWeight pq z.1 z.2*P z) := (hasCompactSupport_cellWeight pq).mul_right
  have hh (pq) : Integrable (fun z : (Fin n → Mom d) × (Fin n → Mom d) =>
      cellWeight pq z.1 z.2*P z) := (hhm pq).integrable_of_hasCompactSupport (hhs pq)
  have hcelli (pq) : Integrable (fun z : (Fin n → Mom d) × (Fin n → Mom d) =>
      W z.1 z.2*cellWeight pq z.1 z.2*P z) := by
    apply ((hWc.mul (hhm pq)).integrable_of_hasCompactSupport (hhs pq).mul_left).congr
    exact Filter.Eventually.of_forall (fun z => by simp only [Function.uncurry,Pi.mul_apply,mul_assoc])
  have hcellK (pq : Fin n → (Fin d → ℤ) × (Fin d → ℤ)) (j : Fin n) :
      μ*((‖NTSP.intVec (pq j).1‖+Real.sqrt d)*(‖NTSP.intVec (pq j).2‖+Real.sqrt d)) ≤
        2^cellLevels μ pq j := (Nat.le_ceil _).trans (by
      have hh := (Nat.lt_two_pow_self (n := cellLevels μ pq j)).le
      exact_mod_cast hh)
  have hbound (pq : Fin n → (Fin d → ℤ) × (Fin d → ℤ))
      (τ : (Fin n → Mom d) × (Fin n → Mom d)) :
      ‖multiInt μ (resProfile J Ψ) (cellData pq τ).p (cellData pq τ).q
        (cellData pq τ).ξ (cellData pq τ).ζ‖ ≤ (K/μ)^n*D0 := by
    rw [multiInt_res_eq_trunc hμ0.le J Ψ pq τ]
    simpa only [Fintype.card_fin] using hcell J (cellLevels μ pq) Ψ D hΨ hD hD0 D0 hD0' μ hμ
      (cellData pq τ) (hcellK pq)
  have hpiece (pq : Fin n → (Fin d → ℤ) × (Fin d → ℤ)) :
      ‖∫ z : (Fin n → Mom d) × (Fin n → Mom d), W z.1 z.2*cellWeight pq z.1 z.2*P z‖ ≤
        H*((K/μ)^n*D0) := by
    obtain ⟨_,heq⟩ := approxInt_cell μ hinv hF (resProfile J Ψ) pq (hh pq) (hhm pq)
    change ‖approxInt μ (fun x y => W x y*cellWeight pq x y) (resProfile J Ψ)‖ ≤ _
    rw [heq]
    apply (norm_integral_le_of_norm_le (hF.norm.mul_const ((K/μ)^n*D0)) (Filter.Eventually.of_forall fun τ => ?_)).trans
      (show (∫ τ : (Fin n → Mom d) × (Fin n → Mom d), ‖fourierW W τ.1 τ.2‖*((K/μ)^n*D0)) ≤
        H*((K/μ)^n*D0) by rw [integral_mul_const]; exact mul_le_mul_of_nonneg_right hFmass (by positivity))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound pq τ) (norm_nonneg _)
  rw [approxInt_eq_sum_cells hxs hys hWs μ (resProfile J Ψ) hcelli]
  calc
    _ ≤ ∑ pq ∈ Q, ‖∫ z : (Fin n → Mom d) × (Fin n → Mom d),
        W z.1 z.2*cellWeight pq z.1 z.2*P z‖ := norm_sum_le _ _
    _ ≤ ∑ _pq ∈ Q, H*((K/μ)^n*D0) := sum_le_sum (fun pq _ => hpiece pq)
    _ = (Q.card:ℝ)*(H*((K/μ)^n*D0)) := by simp
    _ ≤ (7^(2*d*n)*(∏ j, lam j)^(2*d))*(H*((K/μ)^n*D0)) :=
      mul_le_mul_of_nonneg_right (card_cells_le hxs hys a b hlam) (by positivity)
    _ = _ := by
      have he : (C/μ)^n = (7^(2*d))^n*(K/μ)^n := by dsimp only [C]; rw [mul_div_assoc,mul_pow]
      rw [he,pow_mul]
      ring

end WaveTurbulence.RegAsymp
