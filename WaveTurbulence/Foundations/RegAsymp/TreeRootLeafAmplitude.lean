/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.TreeLeafProfiles
public import WaveTurbulence.Foundations.RegAsymp.MaskedModulation
public import WaveTurbulence.Foundations.Incoh.SingleRootSpectralAmplitude

/-! # Moving-root amplitudes for leaf-only Fourier profiles

The extra total leaf-frequency moment pays the linear modulation loss in NT.
All root derivatives remain on the literal cutoffs and root Fourier character.
-/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Incoh WithLp
open scoped ContDiff

/-- The literal moving-root cutoff and masked leaf modulation, with one scalar frequency moment. -/
def treeRootLeafModulation {d m : ℕ} (q : Fin d → ℤ) (c : Fin m → Fin d → ℤ)
    (a : ℂ) (α : Fin m → Mom d) (k : Mom d) : ℂ :=
  treeRootCutoff q k * maskedModulation c ((((1+∑ i, ‖α i‖):ℝ):ℂ)*a) (∑ i, α i) k

/-- This dimensional cost is independent of the tree order and moving root center. -/
def treeRootLeafDerivativeConstant (d J : ℕ) : ℝ :=
  treeRootAmplitudeDerivativeFactor d J * maskedSourceSpatialConstant d 0 J 0

theorem treeRootLeafDerivativeConstant_nonneg (d J : ℕ) :
    0 ≤ treeRootLeafDerivativeConstant d J :=
  mul_nonneg (treeRootAmplitudeDerivativeFactor_nonneg _ _)
    (maskedSourceSpatialConstant_nonneg _ _ _ _)

theorem contDiff_treeRootLeafModulation {d m : ℕ} (q : Fin d → ℤ)
    (c : Fin m → Fin d → ℤ) (a : ℂ) (α : Fin m → Mom d) :
    ContDiff ℝ ∞ (treeRootLeafModulation q c a α) :=
  (contDiff_treeRootCutoff q).mul (contDiff_maskedModulation _ _ _)

/-- The support identity needed by the landed locally finite root-mixture theorem. -/
theorem treeRootLeafModulation_eq_zero {d m : ℕ} (q : Fin d → ℤ)
    (c : Fin m → Fin d → ℤ) (a : ℂ) (α : Fin m → Mom d) (k : Mom d)
    (hk : treeRootCutoff q k = 0) : treeRootLeafModulation q c a α k = 0 := by
  simp only [treeRootLeafModulation, hk, zero_mul]

/-- One additional independent leaf moment controls every root derivative below J.
No derivative order grows with the number of inputs. -/
theorem norm_iteratedFDeriv_treeRootLeafModulation_le {d m J j : ℕ}
    (q : Fin d → ℤ) (c : Fin m → Fin d → ℤ) (a : ℂ) (α : Fin m → Mom d)
    (hj : j ≤ J) (k : Mom d) :
    ‖iteratedFDeriv ℝ j (treeRootLeafModulation q c a α) k‖ ≤
      treeRootLeafDerivativeConstant d J * (1+∑ i, ‖α i‖)^(J+1) * ‖a‖ := by
  let S := ∑ i, ‖α i‖
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hD : 0 ≤ rootMaskDerivativeConstant d J := zero_le_one.trans (one_le_rootMaskDerivativeConstant d J)
  have hb (i : ℕ) (hi : i ≤ J) (x : Mom d) :
      ‖iteratedFDeriv ℝ i (maskedModulation c (((1+S:ℝ):ℂ)*a) (∑ i, α i)) x‖ ≤
        maskedSourceSpatialConstant d 0 J 0 * (1+S)^(J+1) * ‖a‖ := by
    have h := norm_iteratedFDeriv_maskedModulation_le c (((1+S:ℝ):ℂ)*a) (∑ i, α i) x hi
    have hn : (1+‖∑ i, α i‖)^J ≤ (1+S)^J :=
      pow_le_pow_left₀ (add_nonneg zero_le_one (norm_nonneg (∑ i, α i)))
        (add_le_add (le_refl (1:ℝ)) (norm_sum_le Finset.univ α)) J
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith only [hS] : (0:ℝ) ≤ 1+S)] at h
    apply h.trans
    change (2:ℝ)^J * rootMaskDerivativeConstant d J * (2*Real.pi)^J *
      (1+‖∑ i, α i‖)^J * ((1+S)*‖a‖) ≤ _
    calc
      _ ≤ (2:ℝ)^J * rootMaskDerivativeConstant d J * (2*Real.pi)^J *
          (1+S)^J * ((1+S)*‖a‖) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hn (by positivity)) (by positivity)
      _ = _ := by simp only [maskedSourceSpatialConstant, pow_zero, mul_one, pow_succ]; ring
  have hroot (i : ℕ) (hi : i ≤ J) (x : Mom d) :
      ‖iteratedFDeriv ℝ i (treeRootCutoff q) x‖ ≤ rootMaskDerivativeConstant d J := by
    have hc : NTSP.chiDerivConst d i ≤ rootMaskDerivativeConstant d J := by
      unfold rootMaskDerivativeConstant
      have h := Finset.single_le_sum (fun a _ => NTSP.chiDerivConst_nonneg d a)
        (Finset.mem_range.mpr (by omega : i < J+1))
      linarith only [h]
    exact (norm_iteratedFDeriv_treeRootCutoff_le q i x).trans hc
  change ‖iteratedFDeriv ℝ j (fun x => treeRootCutoff q x *
    maskedModulation c (((1+S:ℝ):ℂ)*a) (∑ i, α i) x) k‖ ≤ _
  apply (norm_iteratedFDeriv_mul_le_uniform (contDiff_treeRootCutoff q)
    (contDiff_maskedModulation _ _ _) hD
    (mul_nonneg (mul_nonneg (maskedSourceSpatialConstant_nonneg _ _ _ _) (by positivity)) (norm_nonneg _))
    hroot hb hj k).trans_eq
  dsimp only [treeRootLeafDerivativeConstant, treeRootAmplitudeDerivativeFactor]
  ring

/-- All pointwise leaf moment envelopes are finite, before any integration. -/
theorem treeLeafMomentEnvelope_ne_top {d m : ℕ} (J : ℕ) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (α : Fin m → Fin d → ℝ) :
    treeLeafMomentEnvelope J f c α ≠ ⊤ := by
  unfold treeLeafMomentEnvelope
  exact ENNReal.prod_ne_top (fun _ _ => enorm_ne_top)

/-- The real envelope for root-derivative transport follows from the actual leaf profile. -/
theorem treeLeafSpectrum_real_moment_le {d m : ℕ} (J : ℕ) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (α : Fin m → Fin d → ℝ) :
    (1+∑ a, ‖toLp 2 (α a)‖)^J * ‖treeLeafSpectrum f c α‖ ≤
      (treeLeafMomentEnvelope J f c α).toReal := by
  apply (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp
  rw [ENNReal.ofReal_toReal (treeLeafMomentEnvelope_ne_top J f c α),
    ENNReal.ofReal_mul (by positivity), ofReal_norm]
  exact treeLeafSpectrum_moment_le J f c α

/-- Applied to the actual leaf coefficient, every root derivative is paid by J+1 moments. -/
theorem norm_iteratedFDeriv_treeRootLeafModulation_spectrum_le {d m J j : ℕ}
    (q : Fin d → ℤ) (f : Fin m → Mom d → ℂ) (c : Fin m → Fin d → ℤ)
    (α : Fin m → Fin d → ℝ) (hj : j ≤ J) (k : Mom d) :
    ‖iteratedFDeriv ℝ j
      (treeRootLeafModulation q c (treeLeafSpectrum f c α) (fun a => toLp 2 (α a))) k‖ ≤
      treeRootLeafDerivativeConstant d J * (treeLeafMomentEnvelope (J+1) f c α).toReal := by
  apply (norm_iteratedFDeriv_treeRootLeafModulation_le q c _ _ hj k).trans
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (treeLeafSpectrum_real_moment_le (J+1) f c α)
    (treeRootLeafDerivativeConstant_nonneg _ _)

end WaveTurbulence.RegAsymp
