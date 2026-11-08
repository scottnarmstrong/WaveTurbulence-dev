/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SourceRootMask
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.LocalizedSourceIntegral

/-! Ported by source from C2-B-TOP `Cut2BReg.SourceRootMaskAgreement` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.
 # Exact insertion of the fixed smooth root mask in the actual source -/

public section
noncomputable section
open MeasureTheory

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.RootInputCoordinates in
/-- The source root mask is exactly one wherever the actual localized leaf product is nonzero. -/
theorem RootInputCoordinates.sourceRootMask_mul_localizedLeafWeightSpatial {d n m w : ℕ}
    {P : MomentumTreeData n m w} (C : RootInputCoordinates P)
    (f : Fin m → Mom d → ℂ) (c : Fin m → Fin d → ℤ) (k : Mom d)
    (x : Fin n → Fin 2 → Mom d) :
    sourceRootMask c k * P.localizedLeafWeight f c k x = P.localizedLeafWeight f c k x := by
  by_cases hz : P.inputCellWeight c k x = 0
  · simp only [P.localizedLeafWeight_eq, hz, mul_zero]
  · rw [C.sourceRootMask_eq_one c k x hz, one_mul]

open WaveTurbulence.Incoh.RootInputCoordinates in
/-- The smooth root mask changes none of the literal localized source operators. No analytic
assumption is needed for this identity; it follows from the finite integer root row. -/
theorem RootInputCoordinates.sourceRootMask_mul_localizedSourceIntegralSpatial {d n m w : ℕ}
    {P : MomentumTreeData n m w} (C : RootInputCoordinates P)
    (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (f : Fin m → Mom d → ℂ) (c : Fin m → Fin d → ℤ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (k : Mom d) :
    sourceRootMask c k * (MomentumTreeData.localizedSourceIntegralSpatial (P := P)) ζ L γ δ Q I f c z k =
      (MomentumTreeData.localizedSourceIntegralSpatial (P := P)) ζ L γ δ Q I f c z k := by
  by_cases hm : sourceRootMask c k = 1
  · rw [hm, one_mul]
  · have hz (x : Fin n → Fin 2 → Mom d) : P.localizedLeafWeight f c k x = 0 := by
      have hc : P.inputCellWeight c k x = 0 := by
        by_contra hn
        exact hm (C.sourceRootMask_eq_one c k x hn)
      simp only [P.localizedLeafWeight_eq, hc, mul_zero]
    have hi : (MomentumTreeData.localizedSourceIntegralSpatial (P := P)) ζ L γ δ Q I f c z k = 0 := by
      simp only [MomentumTreeData.localizedSourceIntegralSpatial, hz, mul_zero, zero_mul, tsum_zero, integral_zero]
    rw [hi, mul_zero]

end WaveTurbulence.Flower.IncTop