/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.MaskedCellFamily
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.TreeRootPartition
public import WaveTurbulence.Foundations.Incoh.SmoothModulatedDerivative
public import WaveTurbulence.Foundations.Incoh.UniformDerivativeProduct

/-! Ported by source from C2-B-TOP `Cut2BReg.SingleRootSpectralAmplitude` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.
 # Actual single-root spectral amplitudes and their full derivative envelope -/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- An actual source spectral amplitude confined to one fixed root cell. -/
@[expose] def MomentumTreeData.rootCutoffSpectralAmplitudeSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (q : Fin d → ℤ) (k : Mom d) (u : SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) : ℂ :=
  treeRootCutoffSpatial q k * (MomentumTreeData.allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S k u

/-- Uniform dimensional derivative cost of the extra root cutoff. -/
@[expose] def treeRootAmplitudeDerivativeFactorSpatial (d J : ℕ) : ℝ :=
  (2 : ℝ) ^ J * rootMaskDerivativeConstant d J

theorem treeRootAmplitudeDerivativeFactor_nonnegSpatial (d J : ℕ) : 0 ≤ treeRootAmplitudeDerivativeFactorSpatial d J :=
  mul_nonneg (by positivity) (zero_le_one.trans (one_le_rootMaskDerivativeConstant d J))

open WaveTurbulence.Incoh.MomentumTreeData in
theorem MomentumTreeData.contDiff_rootCutoffSpectralAmplitudeSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (q : Fin d → ℤ) (u : SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) :
    ContDiff ℝ ∞ (fun k => (MomentumTreeData.rootCutoffSpectralAmplitudeSpatial (P := P)) ζ f S q k u) :=
  (contDiff_treeRootCutoffSpatial q).mul ((MomentumTreeData.contDiff_allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S u)

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Every actual derivative has an envelope given by the actual source Fourier moments. -/
theorem MomentumTreeData.norm_iteratedFDeriv_rootCutoffSpectralAmplitude_leSpatial {d n m w J j : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (q : Fin d → ℤ) (hj : j ≤ J) (k : Mom d)
    (u : SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) :
    ‖iteratedFDeriv ℝ j (fun k => (MomentumTreeData.rootCutoffSpectralAmplitudeSpatial (P := P)) ζ f S q k u) k‖ ≤
      treeRootAmplitudeDerivativeFactorSpatial d J * maskedCellEnvelopeSpatial J 0 f S u := by
  apply norm_iteratedFDeriv_mul_le_uniform (contDiff_treeRootCutoffSpatial q)
    ((MomentumTreeData.contDiff_allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S u)
    (zero_le_one.trans (one_le_rootMaskDerivativeConstant d J)) (maskedCellEnvelope_nonnegSpatial J 0 f S u)
    (fun i hi x => ?_) (fun i hi x => ?_) hj k
  · have hc : NTSP.chiDerivConst d i ≤ rootMaskDerivativeConstant d J := by
      unfold rootMaskDerivativeConstant
      have h := Finset.single_le_sum (fun a _ => NTSP.chiDerivConst_nonneg d a)
        (Finset.mem_range.mpr (by omega : i < J + 1))
      linarith only [h]
    exact (norm_iteratedFDeriv_treeRootCutoff_leSpatial q i x).trans hc
  · have h := MomentumTreeData.weighted_norm_allCellMaskedAmplitudeDerivative_leSpatial (P := P) ζ f S (W := 0) hi x u
    simpa only [pow_zero, one_mul] using h

end WaveTurbulence.Flower.IncTop