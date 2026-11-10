/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AuxRows

/-! # P4-W2 AUX (c): `remRowMul`, the `𝒦` row of a remainder times a bounded spatial multiplier

In the twisted family the remainder function `RT(t₁,t₀,x)` of the exceptional couple/tree sits at the row of momentum `x`; for a twisted state
that is the `𝒦` row, which also carries the `r`-dependent spatial factor `G(r,k)` of the other piece.  `remRowW` has no `r`-dependent factor.
`remRowMul`: the row `f(c₀,c₁,k) · G(r,k)` (with `f` time-continuous, slots arbitrary) with the coefficients `ĉ_m(k) G(r,k)` bounded per mode by
`SNorm_mul_le` (`G r` at weight `0`, the coefficient at the row weight): size `C · 2^{Λ₁} d^{Λ₁} · b · sup_r ‖G r‖_{𝔖^{Λ₁,0}}`. -/

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

/-- One mode times a multiplier. -/
theorem snorm_mulG_le {d A B : ℕ} (hd : 1 ≤ d) (hA : A ≠ 0) (g G : Mom d → ℂ) {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hg : SNorm A B g ≠ ⊤) (hG : SNorm A 0 G ≤ ENNReal.ofReal Cg) :
    SNorm A B (fun k => g k * G k) ≤ ENNReal.ofReal ((2 : ℝ) ^ A * (d : ℝ) ^ A * Cg) * SNorm A B g := by
  have hgc : ContDiff ℝ A g := contDiff_of_SNorm_le' hA g (SNorm A B g).toReal (by rw [ENNReal.ofReal_toReal hg])
  have hGc : ContDiff ℝ A G := contDiff_of_SNorm_le' hA G Cg hG
  have h := SNorm_mul_le hd G g hGc hgc hCg ENNReal.toReal_nonneg hG (by rw [ENNReal.ofReal_toReal hg])
  have e : (fun k => g k * G k) = fun k => G k * g k := funext fun k => mul_comm _ _
  rw [e]
  refine h.trans (le_of_eq ?_)
  have hK : 0 ≤ (2 : ℝ) ^ A * (d : ℝ) ^ A * Cg := by positivity
  rw [ENNReal.ofReal_mul hK, ENNReal.ofReal_toReal hg]

end WaveTurbulence.VineEstS5C.P4.W2
