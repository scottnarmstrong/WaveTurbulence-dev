/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WKE.Taylor
public import WaveTurbulence.Foundations.Fourier.MixedNorm

/-! TARGET (taylorbound), L756–758: Fréchet bounds dominate the spatial coordinate-word norm. -/

public section
namespace WaveTurbulence.WKE
open Finset
open scoped ENNReal

/-- The real Schwartz function is embedded isometrically in the complex spatial norm. -/
theorem spatialNorm_real_le_of_weighted_derivatives {d A B : ℕ}
    (f : SchwartzMap (Mom d) ℝ) {C : ℝ} (_hC : 0 ≤ C)
    (hf : ∀ r ≤ A, ∀ k, (1 + ‖k‖) ^ (B : ℝ) * ‖iteratedFDeriv ℝ r f k‖ ≤ C) :
    Fourier.spatialNorm A B (fun k => (f k : ℂ)) ≤ ENNReal.ofReal C := by
  have hcont : ContDiff ℝ A (fun k => (f k : ℂ)) := Complex.ofRealLI.contDiff.comp (f.smooth A)
  rw [Fourier.spatialNorm, ite_eq_left (Or.inr hcont)]
  apply iSup_le
  intro r
  apply iSup_le
  intro hr
  apply iSup_le
  intro ρ
  apply iSup_le
  intro k
  have hder : ‖Fourier.momentumDerivative ρ (fun k => (f k : ℂ)) k‖ ≤
      ‖iteratedFDeriv ℝ r f k‖ := by
    have hnorm := (iteratedFDeriv ℝ r (fun k => (f k : ℂ)) k).le_opNorm
      (fun i => EuclideanSpace.single (ρ i) 1)
    have he : ‖iteratedFDeriv ℝ r (fun k => (f k : ℂ)) k‖ = ‖iteratedFDeriv ℝ r f k‖ :=
      Complex.ofRealLI.norm_iteratedFDeriv_comp_left (f.smooth r).contDiffAt le_rfl
    simpa only [Fourier.momentumDerivative, PiLp.norm_single, norm_one, prod_const_one, mul_one, he] using hnorm
  have hbr : Fourier.momentumBracket k ≤ 1 + ‖k‖ := by
    unfold Fourier.momentumBracket
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [norm_nonneg k]
  have hw : Fourier.momentumBracket k ^ B ≤ (1 + ‖k‖) ^ (B : ℝ) := by
    rw [Real.rpow_natCast]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hbr B
  have hbound := (mul_le_mul hw hder (norm_nonneg _) (by positivity)).trans (hf r hr k)
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (pow_nonneg (show 0 ≤ Fourier.momentumBracket k from Real.sqrt_nonneg _) B)]
  exact ENNReal.ofReal_le_ofReal hbound

/-- A single prefactor controls all lower derivative and weight orders, uniformly in p. -/
theorem taylor_spatial_bound_all_orders {d : ℕ} (hd : 2 ≤ d)
    {φin : SchwartzMap (Mom d) ℝ} {T : ℝ} {φ : ℝ → SchwartzMap (Mom d) ℝ}
    (hφ : IsWKESolution φin T φ) {B : ℝ} (hB : 0 < B)
    (hbound : ∀ τ ∈ Set.Icc 0 T, ∀ y, (1 + ‖y‖) ^ (2 * (d : ℝ) + 1) * |φ τ y| ≤ B)
    {δ : ℝ} (hδ : 0 < δ) (Amax Wmax : ℕ) :
    ∃ C, 1 ≤ C ∧ ∀ A ≤ Amax, ∀ W ≤ Wmax, ∀ p : ℕ, ((p : ℝ) + 1) * δ ≤ T → ∀ n : ℕ,
      ∀ t ∈ Set.Icc (p : ℝ) (p + 1),
        Fourier.spatialNorm A W (fun k => (taylorU hd φ δ p n t k : ℂ)) ≤
          ENNReal.ofReal (C * (2 * taylorRate d (2 * d + 1) B * δ) ^ n) := by
  obtain ⟨C, hC⟩ := taylorbound hd hφ hB hbound hδ Amax Wmax
  refine ⟨max C 1, le_max_right _ _, fun A hA W hW p hp n t ht => ?_⟩
  apply spatialNorm_real_le_of_weighted_derivatives
  · exact mul_nonneg (zero_le_one.trans (le_max_right _ _)) (pow_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (taylorRate_nonneg _ _ _)) hδ.le) _)
  · intro r hr k
    have hw : (1 + ‖k‖) ^ (W : ℝ) ≤ (1 + ‖k‖) ^ (Wmax : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg k]) (by exact_mod_cast hW)
    exact ((mul_le_mul_of_nonneg_right hw (norm_nonneg _)).trans
      (hC p hp n t ht r (hr.trans hA) k)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (pow_nonneg (mul_nonneg (mul_nonneg (by norm_num) (taylorRate_nonneg _ _ _)) hδ.le) _))

end WaveTurbulence.WKE
