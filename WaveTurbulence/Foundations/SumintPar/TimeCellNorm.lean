/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.TimeCellAgreement
public import WaveTurbulence.Foundations.SumintPar.CellMultiplierBound
public import WaveTurbulence.Foundations.Fourier.Norm00VBasic

/-!
# The finite time-cell extension costs at most h inverse squared

The bound keeps the output supremum inside the Fourier integral. It
uses the guarded norm triangle inequality and the explicit cell count.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set ENNReal
namespace WaveTurbulence.SumintPar

/-- Finite sums satisfy the triangle inequality for the drafted guarded norm. -/
theorem XNorm00_finsetSum_le {ι V : Type*} {r : ℕ} (s : Finset ι) (θ : ℝ)
    (F : ι → (Fin r → ℝ) → V → ℂ) :
    XNorm00 θ (fun z v => ∑ j ∈ s, F j z v) ≤ ∑ j ∈ s, XNorm00 θ (F j) := by
  classical
  simp_rw [NormBridgeScratch.XNorm00_eq_mixedFourierNorm00]
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (Fourier.mixedFourierNorm00_add_le θ _ _).trans (add_le_add le_rfl ih)

/-- The literal finite cell extension has a cost independent of the source input count. -/
theorem XNorm00_timeCellExtension_le {d : ℕ} {V : Type*} (D : SumintDatum d)
    (hI : 0 < D.S.I) (N : ℕ) {h θ : ℝ} (hh : h ∈ Ioc (0:ℝ) 1)
    (hθ : |θ| ≤ 1) (F : V → (D.S.TVar → ℝ) → ℂ) (B : ℝ≥0∞) (hB : B < ⊤)
    (hF : ∀ j : ℤ, XNorm00 θ (fun z v => kernelExtension D hI ((j:ℝ)*h) h (F v) z) ≤ B) :
    XNorm00 θ (fun z v => timeCellExtension D hI N h (F v) z) ≤
      ENNReal.ofReal (cellMultiplierRealConstant N*((N:ℝ)+5)*h⁻¹*h⁻¹)*B := by
  classical
  apply (XNorm00_finsetSum_le (timeCellIndices N h) θ _).trans
  calc
    _ ≤ ∑ j ∈ timeCellIndices N h, ENNReal.ofReal (cellMultiplierRealConstant N*h⁻¹)*B := by
      apply Finset.sum_le_sum
      intro j _
      exact (XNorm00_mul_cellInverseExponential_le N hh hθ j _ ((hF j).trans_lt hB)).trans
        (mul_le_mul' le_rfl (hF j))
    _ = ENNReal.ofReal ((timeCellIndices N h).card:ℝ)*
        (ENNReal.ofReal (cellMultiplierRealConstant N*h⁻¹)*B) := by simp
    _ ≤ ENNReal.ofReal (((N:ℝ)+5)/h)*
        (ENNReal.ofReal (cellMultiplierRealConstant N*h⁻¹)*B) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal (card_timeCellIndices_le N hh)) le_rfl
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg (by positivity) hh.1.le)]
      congr 2
      ring

end WaveTurbulence.SumintPar
