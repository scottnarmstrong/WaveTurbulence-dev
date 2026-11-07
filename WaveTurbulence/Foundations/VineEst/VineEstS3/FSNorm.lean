/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.FSFamily
public import WaveTurbulence.Foundations.IncohInst.Regref.SpatialBridge

/-! # The Fourier-series coefficients are controlled in `S^{Λ₁,Λ₂}` (B2, step 6b)

For `Λ₁ ≠ 0`, `θ ≥ 0` and an extension `G` with `XNorm θ Λ₁ Λ₂ G < ⊤`,
`∑_m ⟨m/2⟩^θ ‖c_m‖_{S^{Λ₁,Λ₂}} ≤ C · ‖G‖_{X^{θ,Λ₁,Λ₂}}`, with `C` independent of `G`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3.FS
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.NormBridgeScratch MeasureTheory Set Filter
open scoped ENNReal ContDiff

variable {r d : ℕ}

/-- The sum of the weighted envelope integrals over all words of length at most `Λ₁`. -/
noncomputable def wordSum (Λ₁ Λ₂ : ℕ) (Φ : (Fin r → ℝ) → Mom d → ℂ) (a : (Fin r → ℝ) → ℂ) : ℝ≥0∞ :=
  ∑ n ∈ Finset.range (Λ₁ + 1), ∑ σ : Fin n → Fin d, ∫⁻ lam, ENNReal.ofReal ‖a lam‖ * wenv Λ₂ σ (Φ lam)

theorem coeff_eq_integral (q : Fin r → ℝ) (G : (Fin r → ℝ) → Mom d → ℂ)
    {Φ : (Fin r → ℝ) → Mom d → ℂ} (hΦ : ∀ᵐ lam, Φ lam = timeFT G lam) (m : Fin r → ℤ) :
    coeff q G m = fun k => ∫ lam, kern q m lam * Φ lam k := by
  funext k
  unfold coeff
  refine integral_congr_ae ?_
  filter_upwards [hΦ] with lam hl using by rw [hl]

/-- Pointwise: the `S`-norm of a mixture is at most the `wordSum`. -/
theorem SNorm_mixture_le {Λ₁ Λ₂ : ℕ} {Φ : (Fin r → ℝ) → Mom d → ℂ} {a : (Fin r → ℝ) → ℂ} {Ka : ℝ}
    (ha : Measurable a) (hab : ∀ lam, ‖a lam‖ ≤ Ka) (hs : ∀ lam, ContDiff ℝ Λ₁ (Φ lam))
    (hm : ∀ k, StronglyMeasurable fun lam => Φ lam k)
    (hfin : ∀ n ≤ Λ₁, ∀ σ : Fin n → Fin d, ∀ lam, wenv Λ₂ σ (Φ lam) < ⊤)
    (hint : ∀ n ≤ Λ₁, ∀ σ : Fin n → Fin d, ∫⁻ lam, wenv Λ₂ σ (Φ lam) ≠ ⊤) :
    SNorm Λ₁ Λ₂ (fun k => ∫ lam, a lam * Φ lam k) ≤ wordSum Λ₁ Λ₂ Φ a := by
  obtain ⟨hcd, hb⟩ := mixture_bound ha hab hs hm hfin hint
  rw [SNorm_eq_spatialNorm]
  unfold spatialNorm
  rw [ite_eq_left (Or.inr hcd)]
  refine iSup₂_le fun n hn => iSup_le fun σ => ?_
  unfold momentumSupNorm
  refine iSup_le fun k => ?_
  have hmul : ENNReal.ofReal (momentumBracket k ^ Λ₂) *
      ‖momentumDerivative σ (fun k => ∫ lam, a lam * Φ lam k) k‖ₑ =
      ENNReal.ofReal (momentumBracket k ^ Λ₂ *
        ‖momentumDerivative σ (fun k => ∫ lam, a lam * Φ lam k) k‖) := by
    rw [ENNReal.ofReal_mul (pow_nonneg (le_trans zero_le_one (one_le_momentumBracket k)) _), ofReal_norm]
  rw [hmul]
  refine (hb n hn σ k).trans ?_
  unfold wordSum
  refine le_trans ?_ (Finset.single_le_sum (f := fun n => ∑ σ : Fin n → Fin d,
    ∫⁻ lam, ENNReal.ofReal ‖a lam‖ * wenv Λ₂ σ (Φ lam)) (fun _ _ => zero_le)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hn)))
  exact Finset.single_le_sum (f := fun σ : Fin n → Fin d =>
    ∫⁻ lam, ENNReal.ofReal ‖a lam‖ * wenv Λ₂ σ (Φ lam)) (fun _ _ => zero_le) (Finset.mem_univ σ)


theorem weight_kern_tsum_le {θ : ℝ} (hθ : 0 ≤ θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q lam : Fin r → ℝ),
      ∑' m : Fin r → ℤ, maxBracketPow θ (half m) * ENNReal.ofReal ‖kern q m lam‖ ≤
        ENNReal.ofReal C * maxBracketPow θ lam := by
  obtain ⟨C, hC, hb⟩ := sum_kern_weight_le_uniform (r := r) hθ
  refine ⟨C, hC, fun q lam => ?_⟩
  obtain ⟨hs, ht⟩ := hb q lam
  have hnn : ∀ m : Fin r → ℤ, 0 ≤ timeBracket (half m) ^ θ * ‖kern q m lam‖ := fun m =>
    mul_nonneg (Real.rpow_nonneg (le_trans zero_le_one (one_le_timeBracket' _)) _) (norm_nonneg _)
  have h1 : ∀ m : Fin r → ℤ, maxBracketPow θ (half m) * ENNReal.ofReal ‖kern q m lam‖ =
      ENNReal.ofReal (timeBracket (half m) ^ θ * ‖kern q m lam‖) := by
    intro m
    rw [maxBracketPow_eq_timeWeight, timeWeight, ENNReal.ofReal_mul
      (Real.rpow_nonneg (le_trans zero_le_one (one_le_timeBracket' _)) _)]
  simp_rw [h1]
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hs, maxBracketPow_eq_timeWeight, timeWeight,
    ← ENNReal.ofReal_mul hC]
  exact ENNReal.ofReal_le_ofReal ht

theorem tsum_weight_lintegral_le {θ : ℝ} (hθ : 0 ≤ θ) {Λ₁ Λ₂ : ℕ} (q : Fin r → ℝ) {C : ℝ}
    (hC : ∀ lam : Fin r → ℝ, ∑' m : Fin r → ℤ, maxBracketPow θ (half m) * ENNReal.ofReal ‖kern q m lam‖ ≤
        ENNReal.ofReal C * maxBracketPow θ lam)
    {Φ : (Fin r → ℝ) → Mom d → ℂ} (hs : ∀ lam, ContDiff ℝ Λ₁ (Φ lam))
    (hm : ∀ k, StronglyMeasurable fun lam => Φ lam k) {n : ℕ} (hn : n ≤ Λ₁) (σ : Fin n → Fin d)
    {X : ℝ≥0∞} (hb : ∫⁻ lam, maxBracketPow θ lam * wenv Λ₂ σ (Φ lam) ≤ X) :
    ∑' m : Fin r → ℤ, maxBracketPow θ (half m) * ∫⁻ lam, ENNReal.ofReal ‖kern q m lam‖ * wenv Λ₂ σ (Φ lam)
      ≤ ENNReal.ofReal C * X := by
  have hw : ∀ m : Fin r → ℤ, maxBracketPow θ (half m) ≠ ⊤ := fun m => ENNReal.ofReal_ne_top
  have hwm := measurable_wenv (Λ₂ := Λ₂) hs hm hn σ
  have h1 : ∀ m : Fin r → ℤ, maxBracketPow θ (half m) * ∫⁻ lam, ENNReal.ofReal ‖kern q m lam‖ *
      wenv Λ₂ σ (Φ lam) = ∫⁻ lam, (maxBracketPow θ (half m) * ENNReal.ofReal ‖kern q m lam‖) *
      wenv Λ₂ σ (Φ lam) := fun m => by
    rw [← lintegral_const_mul' _ _ (hw m)]
    simp_rw [mul_assoc]
  simp_rw [h1]
  have hmeas : ∀ m : Fin r → ℤ, AEMeasurable (fun lam => (maxBracketPow θ (half m) *
      ENNReal.ofReal ‖kern q m lam‖) * wenv Λ₂ σ (Φ lam)) volume := fun m =>
    ((((continuous_kern q m).measurable.norm.ennreal_ofReal).const_mul _).mul hwm).aemeasurable
  rw [← lintegral_tsum hmeas]
  simp_rw [ENNReal.tsum_mul_right]
  calc ∫⁻ lam, (∑' m : Fin r → ℤ, maxBracketPow θ (half m) * ENNReal.ofReal ‖kern q m lam‖) *
        wenv Λ₂ σ (Φ lam)
      ≤ ∫⁻ lam, ENNReal.ofReal C * (maxBracketPow θ lam * wenv Λ₂ σ (Φ lam)) :=
        lintegral_mono fun lam => by rw [← mul_assoc]; exact mul_le_mul_left (hC lam) _
    _ = ENNReal.ofReal C * ∫⁻ lam, maxBracketPow θ lam * wenv Λ₂ σ (Φ lam) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C * X := mul_le_mul_right hb _

/-- **The Fourier-series coefficients of an extension are summable in `S^{Λ₁,Λ₂}`.** -/
theorem sum_SNorm_coeff_le {θ : ℝ} (hθ : 0 ≤ θ) {Λ₁ Λ₂ : ℕ} (hΛ : Λ₁ ≠ 0) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (q : Fin r → ℝ) (G : (Fin r → ℝ) → Mom d → ℂ), XNorm θ Λ₁ Λ₂ G < ⊤ →
      ∑' m : Fin r → ℤ, maxBracketPow θ (half m) * SNorm Λ₁ Λ₂ (coeff q G m) ≤
        C * XNorm θ Λ₁ Λ₂ G := by
  classical
  obtain ⟨C0, hC0, hC0b⟩ := weight_kern_tsum_le (r := r) hθ
  refine ⟨ENNReal.ofReal C0 * ((∑ n ∈ Finset.range (Λ₁ + 1), d ^ n : ℕ) : ℝ≥0∞),
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _), fun q G hG => ?_⟩
  obtain ⟨Φ, hae, hcd, hm, hfin, hb, hint⟩ := exists_good_family hθ hΛ G hG
  have hstep : ∀ m : Fin r → ℤ, SNorm Λ₁ Λ₂ (coeff q G m) ≤ wordSum Λ₁ Λ₂ Φ (kern q m) := by
    intro m
    rw [coeff_eq_integral q G hae m]
    exact SNorm_mixture_le (Ka := ((2 : ℝ) ^ r)⁻¹ * ∫ u, ‖cutQ q u‖) (continuous_kern q m).measurable
      (norm_kern_le q m) hcd hm hfin hint
  calc ∑' m : Fin r → ℤ, maxBracketPow θ (half m) * SNorm Λ₁ Λ₂ (coeff q G m)
      ≤ ∑' m : Fin r → ℤ, maxBracketPow θ (half m) * wordSum Λ₁ Λ₂ Φ (kern q m) :=
        ENNReal.tsum_le_tsum fun m => mul_le_mul_right (hstep m) _
    _ = ∑ n ∈ Finset.range (Λ₁ + 1), ∑ σ : Fin n → Fin d, ∑' m : Fin r → ℤ,
          maxBracketPow θ (half m) * ∫⁻ lam, ENNReal.ofReal ‖kern q m lam‖ * wenv Λ₂ σ (Φ lam) := by
        unfold wordSum
        simp_rw [Finset.mul_sum]
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ ≤ ∑ n ∈ Finset.range (Λ₁ + 1), ∑ σ : Fin n → Fin d, ENNReal.ofReal C0 * XNorm θ Λ₁ Λ₂ G := by
        refine Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun σ _ => ?_
        exact tsum_weight_lintegral_le hθ q (hC0b q) hcd hm (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)) σ
          (hb n (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)) σ)
    _ = (ENNReal.ofReal C0 * ((∑ n ∈ Finset.range (Λ₁ + 1), d ^ n : ℕ) : ℝ≥0∞)) *
          XNorm θ Λ₁ Λ₂ G := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun n _ => ?_
        ring

end WaveTurbulence.VineEstS3.FS
