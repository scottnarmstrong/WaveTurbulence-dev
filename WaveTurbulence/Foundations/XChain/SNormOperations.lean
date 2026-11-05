/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.IncohInst.Regref.SpatialBridge
public import WaveTurbulence.Foundations.XChain.SNormPointwise
/-! Finite sums and monotonicity of the exact spatial norm, using its universal bridge. -/
public section
namespace WaveTurbulence.Induct
open Finset
open scoped ENNReal

theorem ofReal_jbr_mul_norm {d : ℕ} (x : Mom d) (B : ℕ) (z : ℂ) :
    ENNReal.ofReal (jbr x ^ B * ‖z‖) =
      ENNReal.ofReal (Fourier.momentumBracket x ^ B) * ‖z‖ₑ := by
  rw [ENNReal.ofReal_mul (pow_nonneg (jbr_pos x).le B), ofReal_norm]
  rfl

theorem SNorm_momentum_pointwise {d A B : ℕ} (f : Mom d → ℂ) (hf : ContDiff ℝ A f)
    (C : ℝ) (hC : 0 ≤ C) (h : SNorm A B f ≤ ENNReal.ofReal C)
    {n : ℕ} (hn : n ≤ A) (ρ : Fin n → Fin d) (x : Mom d) :
    jbr x ^ B * ‖Fourier.momentumDerivative ρ f x‖ ≤ C := by
  rw [NormBridgeScratch.SNorm_eq_spatialNorm] at h
  simp only [Fourier.spatialNorm, ite_eq_left (Or.inr hf)] at h
  have hi : ENNReal.ofReal (jbr x ^ B * ‖Fourier.momentumDerivative ρ f x‖) ≤
      ⨆ (m : ℕ) (_ : m ≤ A) (σ : Fin m → Fin d),
        Fourier.momentumSupNorm B (Fourier.momentumDerivative σ f) := by
    have hh : ENNReal.ofReal (Fourier.momentumBracket x ^ B) *
        ‖Fourier.momentumDerivative ρ f x‖ₑ ≤
        ⨆ (m : ℕ) (_ : m ≤ A) (σ : Fin m → Fin d),
          Fourier.momentumSupNorm B (Fourier.momentumDerivative σ f) := le_iSup_of_le n (le_iSup_of_le hn (le_iSup_of_le ρ
      (le_iSup (fun y => ENNReal.ofReal (Fourier.momentumBracket y ^ B) *
        ‖Fourier.momentumDerivative ρ f y‖ₑ) x)))
    rw [ofReal_jbr_mul_norm]
    exact hh
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp (hi.trans h)

theorem SNorm_le_of_momentum_bounds {d A B : ℕ} (f : Mom d → ℂ) (hf : ContDiff ℝ A f)
    (C : ℝ) (h : ∀ n ≤ A, ∀ ρ : Fin n → Fin d, ∀ x,
      jbr x ^ B * ‖Fourier.momentumDerivative ρ f x‖ ≤ C) :
    SNorm A B f ≤ ENNReal.ofReal C := by
  rw [NormBridgeScratch.SNorm_eq_spatialNorm]
  simp only [Fourier.spatialNorm, ite_eq_left (Or.inr hf)]
  apply iSup_le
  intro n
  apply iSup_le
  intro hn
  apply iSup_le
  intro ρ
  apply iSup_le
  intro x
  have hi := ENNReal.ofReal_le_ofReal (h n hn ρ x)
  rw [← ofReal_jbr_mul_norm]
  exact hi

theorem SNorm_finset_sum_bound {d A B : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Mom d → ℂ) (C : ι → ℝ)
    (hf : ∀ i ∈ s, ContDiff ℝ A (f i)) (hC : ∀ i ∈ s, 0 ≤ C i)
    (h : ∀ i ∈ s, SNorm A B (f i) ≤ ENNReal.ofReal (C i)) :
    SNorm A B (fun x => ∑ i ∈ s, f i x) ≤ ENNReal.ofReal (∑ i ∈ s, C i) := by
  apply SNorm_le_of_momentum_bounds _ (ContDiff.sum hf)
  intro n hn ρ x
  have hderiv : Fourier.momentumDerivative ρ (fun x => ∑ i ∈ s, f i x) x =
      ∑ i ∈ s, Fourier.momentumDerivative ρ (f i) x := by
    unfold Fourier.momentumDerivative
    rw [iteratedFDeriv_fun_sum_apply (fun i hi => (hf i hi).contDiffAt.of_le (by exact_mod_cast hn))]
    simp only [_root_.sum_apply]
  rw [hderiv]
  calc
    _ ≤ jbr x ^ B * ∑ i ∈ s, ‖Fourier.momentumDerivative ρ (f i) x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg (jbr_pos x).le B)
    _ = ∑ i ∈ s, jbr x ^ B * ‖Fourier.momentumDerivative ρ (f i) x‖ := mul_sum ..
    _ ≤ _ := sum_le_sum (fun i hi => SNorm_momentum_pointwise (f i) (hf i hi) (C i) (hC i hi) (h i hi) hn ρ x)

theorem SNorm_mono_bound {d A B A' B' : ℕ} (hA : A' ≤ A) (hB : B' ≤ B)
    (f : Mom d → ℂ) (hf : ContDiff ℝ A f) (C : ℝ) (hC : 0 ≤ C)
    (h : SNorm A B f ≤ ENNReal.ofReal C) : SNorm A' B' f ≤ ENNReal.ofReal C := by
  apply SNorm_le_of_momentum_bounds f (hf.of_le (by exact_mod_cast hA))
  intro n hn ρ x
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (one_le_jbr x) hB) (norm_nonneg _)).trans
    (SNorm_momentum_pointwise f hf C hC h (hn.trans hA) ρ x)

end WaveTurbulence.Induct
