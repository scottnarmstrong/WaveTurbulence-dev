/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.WeightedKernelAgreement
public import WaveTurbulence.Foundations.SumintPar.CellInverseExponential
public import WaveTurbulence.Foundations.SumintPar.SourceTimeShear

/-!
# Exact recombination of the local time-cell kernels

The finite partition restores the original weighted source integral
on the complete output cube. Off a cell's support both sides vanish.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
namespace WaveTurbulence.SumintPar

/-- The literal finite sum of the compact local source kernels. -/
@[expose] noncomputable def timeCellExtension {d : ℕ} (D : SumintDatum d)
    (hI : 0 < D.S.I) (N : ℕ) (h : ℝ) (F : (D.S.TVar → ℝ) → ℂ)
    (z : Fin 3 → ℝ) : ℂ :=
  ∑ j ∈ timeCellIndices N h,
    kernelExtension D hI ((j:ℝ)*h) h F z * cellInverseExponential N h j z

end WaveTurbulence.SumintPar
