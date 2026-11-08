/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.MaskedSourceAmplitude
public import WaveTurbulence.Foundations.Incoh.SpectralMomentProfiles
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Ported by source from C2-B-TOP `Cut2BReg.MaskedSourceDerivativeBound` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.
 # Actual source spatial derivative and root-weight envelope -/

public section
noncomputable section
open WithLp Set
open scoped ContDiff

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- A common actual moment envelope controls every source amplitude derivative below order `J`. -/
theorem MomentumTreeData.norm_iteratedFDeriv_sourceAmplitude_le_commonMomentSpatial {d n m w J j : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (ξ : LocalizedCellIndex n m → Fin d → ℝ) (k : Mom d) (hj : j ≤ J) :
    ‖iteratedFDeriv ℝ j (fun k => (MomentumTreeData.sourceSpectralAmplitudeSpatial (P := P)) ζ f c z k ξ) k‖ ≤
      (2 * Real.pi) ^ J * ‖localizedSpectralMomentReference J f c ξ‖ := by
  rw [norm_localizedSpectralMomentReference]
  apply ((MomentumTreeData.norm_iteratedFDeriv_sourceSpectralAmplitude_leSpatial (P := P)) ζ f c z ξ k j).trans
  have hp : (2 * Real.pi) ^ j ≤ (2 * Real.pi) ^ J :=
    pow_le_pow_right₀ (by nlinarith [Real.pi_gt_three]) hj
  have hm : (∏ a : Fin m, (1 + ‖toLp 2 (ξ (.inl a))‖) ^ j) ≤
      ∏ a : Fin m, (1 + ‖toLp 2 (ξ (.inl a))‖) ^ J :=
    Finset.prod_le_prod₀ (fun a _ => by positivity)
      (fun a _ => pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg _)) hj)
  simpa only [mul_assoc] using (mul_le_mul_of_nonneg_right
    (mul_le_mul hp hm (by positivity) (by positivity)) (norm_nonneg (localizedSpectralReference (n := n) f c ξ)))

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Uniform actual derivative bound after insertion of the fixed smooth source root mask. -/
theorem MomentumTreeData.norm_iteratedFDeriv_maskedSourceAmplitude_leSpatial {d n m w J j : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (ξ : LocalizedCellIndex n m → Fin d → ℝ) (k : Mom d) (hj : j ≤ J) :
    ‖iteratedFDeriv ℝ j (fun k => (MomentumTreeData.maskedSourceSpectralAmplitudeSpatial (P := P)) ζ f c z k ξ) k‖ ≤
      (2 : ℝ) ^ J * rootMaskDerivativeConstant d J * (2 * Real.pi) ^ J *
        ‖localizedSpectralMomentReference J f c ξ‖ := by
  have hD : 0 ≤ rootMaskDerivativeConstant d J := zero_le_one.trans (one_le_rootMaskDerivativeConstant d J)
  have hp := norm_iteratedFDeriv_mul_le (contDiff_sourceRootMask c)
    ((MomentumTreeData.contDiff_sourceSpectralAmplitudeSpatial (P := P)) ζ f c z ξ) k (show (j : ℕ∞ω) ≤ ∞ by simp)
  change ‖iteratedFDeriv ℝ j (fun k => (MomentumTreeData.maskedSourceSpectralAmplitudeSpatial (P := P)) ζ f c z k ξ) k‖ ≤ _ at hp
  apply hp.trans
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * rootMaskDerivativeConstant d J *
        ((2 * Real.pi) ^ J * ‖localizedSpectralMomentReference J f c ξ‖) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_sourceRootMask_le c
          ((Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hj) k) (Nat.cast_nonneg _))
        ((MomentumTreeData.norm_iteratedFDeriv_sourceAmplitude_le_commonMomentSpatial (P := P)) ζ f c z ξ k ((Nat.sub_le j i).trans hj))
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hD)
    _ = (2 : ℝ) ^ j * rootMaskDerivativeConstant d J * (2 * Real.pi) ^ J *
        ‖localizedSpectralMomentReference J f c ξ‖ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      have hchoose : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = (2 : ℝ) ^ j := by
        exact_mod_cast Nat.sum_range_choose j
      rw [hchoose]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj) hD)
        (by positivity)) (norm_nonneg _)

/-- Explicit dimensional/leaf-count constant for the actual full weighted derivative envelope. -/
@[expose] def maskedSourceSpatialConstantSpatial (d m J W : ℕ) : ℝ :=
  ((2 : ℝ) ^ J * rootMaskDerivativeConstant d J * (2 * Real.pi) ^ J) *
    ((1 + 2 * Real.sqrt d) * (2 + Real.sqrt d) ^ m) ^ W

open WaveTurbulence.Incoh.MomentumTreeData in
/-- The actual source mask transfers the root weight to summable leaf-center weights. -/
theorem MomentumTreeData.weighted_norm_iteratedFDeriv_maskedSourceAmplitude_leSpatial
    {d n m w J j W : ℕ} (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (ξ : LocalizedCellIndex n m → Fin d → ℝ) (k : Mom d) (hj : j ≤ J) :
    Fourier.momentumBracket k ^ W *
        ‖iteratedFDeriv ℝ j (fun k => (MomentumTreeData.maskedSourceSpectralAmplitudeSpatial (P := P)) ζ f c z k ξ) k‖ ≤
      maskedSourceSpatialConstantSpatial d m J W *
        (∏ a : Fin m, Fourier.momentumBracket (NTSP.intVec (c a)) ^ W) *
          ‖localizedSpectralMomentReference J f c ξ‖ := by
  have hcent : 0 ≤ ∏ a : Fin m, Fourier.momentumBracket (NTSP.intVec (c a)) ^ W :=
    Finset.prod_nonneg (fun a _ => pow_nonneg (zero_le_one.trans (one_le_momentumBracket _)) W)
  by_cases hk : k ∈ tsupport (sourceRootMask c)
  · have hw := momentumBracket_pow_le_on_sourceRootMask (W := W) c k hk
    have hd := (MomentumTreeData.norm_iteratedFDeriv_maskedSourceAmplitude_leSpatial (P := P)) ζ f c z ξ k hj
    have hD : 0 ≤ rootMaskDerivativeConstant d J := zero_le_one.trans (one_le_rootMaskDerivativeConstant d J)
    apply (mul_le_mul hw hd (norm_nonneg _) (by positivity)).trans_eq
    unfold maskedSourceSpatialConstantSpatial
    ring
  · have hz : iteratedFDeriv ℝ j (fun k => (MomentumTreeData.maskedSourceSpectralAmplitudeSpatial (P := P)) ζ f c z k ξ) k = 0 := by
      by_contra hn
      have hs := support_iteratedFDeriv_subset j hn
      exact hk (tsupport_mul_subset_left hs)
    rw [hz, norm_zero, mul_zero]
    unfold maskedSourceSpatialConstantSpatial
    have hD : 0 ≤ rootMaskDerivativeConstant d J := zero_le_one.trans (one_le_rootMaskDerivativeConstant d J)
    positivity

end WaveTurbulence.Flower.IncTop