/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SpectralMomentSummability

/-! # Individual leaf Fourier moment masses and exact finite-product transport -/

public section
noncomputable section
open MeasureTheory WithLp
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Literal actual Fourier moment mass of one localized leaf input. -/
@[expose] def leafFourierMomentMass {d : ℕ} (J : ℕ) (f : Mom d → ℂ) (c : Fin d → ℤ) : ℝ≥0∞ :=
  ∫⁻ ξ : Fin d → ℝ, ‖(((1 + ‖toLp 2 ξ‖) ^ J : ℝ) : ℂ) *
    Fourier.timeFourier (fun x => leafCell f c (toLp 2 x)) ξ‖ₑ

/-- Total actual moment mass after all leaf-center localizations. -/
@[expose] def leafFourierMomentTotal {d : ℕ} (J : ℕ) (f : Mom d → ℂ) : ℝ≥0∞ :=
  ∑' c : Fin d → ℤ, leafFourierMomentMass J f c

/-- The literal actual single-input moment total is bounded by the finite source spatial norm. -/
theorem leafFourierMomentTotal_le {d K M : ℕ} (J : ℕ) {f : Mom d → ℂ} {B : ℝ}
    (hK : d + 1 + J ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (hf : Fourier.spatialNorm K M f ≤ ENNReal.ofReal B) :
    leafFourierMomentTotal J f ≤ ENNReal.ofReal (leafMomentLocalizationConstant d J M * B) := by
  have hcell (c : Fin d → ℤ) : leafFourierMomentMass J f c ≤
      ENNReal.ofReal (leafCellFourierMomentConstant d J M * B / Fourier.momentumBracket (NTSP.intVec c) ^ M) :=
    lintegral_enorm_spectralMomentProfile_leaf_le (n := 0) J (fun _ : Fin 1 => f)
      (fun _ : Fin 1 => c) hK hB (fun _ => hf) 0
  apply (ENNReal.tsum_le_tsum hcell).trans_eq
  rw [tsum_ofReal_div_momentumBracket_intVec hM
    (mul_nonneg (leafCellFourierMomentConstant_nonneg d J M) hB)]
  congr 1
  unfold leafMomentLocalizationConstant
  ring

/-- The all-leaf moment envelope factors over actual individual moment totals. The source
spatial bound here justifies Fourier integrability; no bound depending on its size enters
this factorization. -/
theorem tsum_lintegral_spectralMomentReference_le_product_actual_totals {d n m K M : ℕ} (J : ℕ)
    (f : Fin m → Mom d → ℂ) {B : ℝ} (hK : d + 1 + J ≤ K) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) :
    (∑' c : Fin m → Fin d → ℤ,
      ∫⁻ ξ : LocalizedCellIndex n m → Fin d → ℝ, ‖localizedSpectralMomentReference J f c ξ‖ₑ) ≤
        (∏ a : Fin m, leafFourierMomentTotal J (f a)) *
          ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n) := by
  have hcell (c : Fin m → Fin d → ℤ) :
      (∫⁻ ξ : LocalizedCellIndex n m → Fin d → ℝ, ‖localizedSpectralMomentReference J f c ξ‖ₑ) ≤
        (∏ a : Fin m, leafFourierMomentMass J (f a) (c a)) *
          ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n) := by
    rw [lintegral_enorm_localizedSpectralMomentReference J f c hK hB hf, Fintype.prod_sum_type]
    apply mul_le_mul' le_rfl
    calc
      _ ≤ ∏ _p : Fin n × Fin 2, ENNReal.ofReal (halfCellFourierConstant d) :=
        Finset.prod_le_prod (fun p _ => lintegral_enorm_spectralMomentProfile_link_le J f c p)
      _ = _ := by simp [Nat.mul_comm]
  apply (ENNReal.tsum_le_tsum hcell).trans_eq
  rw [ENNReal.tsum_mul_right, tsum_fin_product_ennreal m (fun a c => leafFourierMomentMass J (f a) c)]
  rfl

end WaveTurbulence.Incoh
