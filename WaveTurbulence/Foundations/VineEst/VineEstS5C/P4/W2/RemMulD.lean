/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AuxRows

/-! # P4-W2 (b1): `remRowMulD`, the `𝒦` row of a weight-0 remainder (a tree remainder) times a DECAYING multiplier

Copy-edit of `AuxMul.remRowMul` (that file is unchanged): the remainder `f` has weight `0`, the multiplier `G` carries the row weight (`rowOrder`, the decaying couple factor),
so that the product has the row weight (`SNorm_mul_le` with the weight-`0` factor first).  `AuxMul`'s version has `f` at the row weight and `G` at weight `0`. -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS4c MeasureTheory
  WaveTurbulence.LGSpine
open scoped ENNReal

variable {P : WTParams}

/-- One mode (weight `0`) times a decaying multiplier (weight `B`). -/
theorem snorm_mulGD_le {d A B : ℕ} (hd : 1 ≤ d) (hA : A ≠ 0) (g G : Mom d → ℂ) {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hg : SNorm A 0 g ≠ ⊤) (hG : SNorm A B G ≤ ENNReal.ofReal Cg) :
    SNorm A B (fun k => g k * G k) ≤ ENNReal.ofReal ((2 : ℝ) ^ A * (d : ℝ) ^ A * Cg) * SNorm A 0 g := by
  have hgc : ContDiff ℝ A g := contDiff_of_SNorm_le' hA g (SNorm A 0 g).toReal (by rw [ENNReal.ofReal_toReal hg])
  have hGc : ContDiff ℝ A G := contDiff_of_SNorm_le' hA G Cg hG
  have h := SNorm_mul_le hd g G hgc hGc ENNReal.toReal_nonneg hCg (by rw [ENNReal.ofReal_toReal hg]) hG
  refine h.trans (le_of_eq ?_)
  have hK : 0 ≤ (2 : ℝ) ^ A * (d : ℝ) ^ A * Cg := by positivity
  rw [show (2 : ℝ) ^ A * (d : ℝ) ^ A * (SNorm A 0 g).toReal * Cg = (2 ^ A * (d : ℝ) ^ A * Cg) * (SNorm A 0 g).toReal by ring,
    ENNReal.ofReal_mul hK, ENNReal.ofReal_toReal hg]

end WaveTurbulence.VineEstS5C.P4.W2
