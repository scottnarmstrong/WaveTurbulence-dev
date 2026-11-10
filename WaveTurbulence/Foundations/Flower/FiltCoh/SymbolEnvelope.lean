/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickCorrectionSourceEnvelope
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.PhysicalLocalSymbol
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.HalfCellCrudeSumAllOrders
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.ErrorCoefficientBudget
public import WaveTurbulence.Foundations.RegAsymp.DerivativeCoefficientNormalizer
public import WaveTurbulence.Foundations.RegAsymp.SymbolLinearity
public import WaveTurbulence.Foundations.RegAsymp.RemainderMeasurability

/-! # FILT-COH: the actual physical cell symbol at an arbitrary time weight

Bound-only counterpart of main's error envelope (`RA1Leafwise.physical_error_scalar_envelope`, weight `η`): the
full physical cell symbol of DH23 (the local NT lattice sum with the squared Wick factors, at energy `2δ`) is
bounded at any time weight `θ ≤ 1` by

* the crude NT sum `halfCell_crude_normalized_sum_all_orders` (no moment premise) with the derivative-only
  normalizer `derivative_coefficient_NT_normalizer` (o82 Thm 10.1 (10.5), Lemma 16.1 coherent case); and
* the Wick correction, through main's `wick_slice_scalar_envelope`, which is already generic in the weight.

No principal value and no small error estimate is used. -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory ClassJR ApproxNT Finset WithLp
open scoped ENNReal

variable {d : ℕ}

/-- The physical cell symbol is the normalized NT sum at energy `2δ` plus the normalized Wick correction
(main's exact decomposition, with its leading term cancelled against the remainder's). -/
theorem physicalWeightedCellSymbol_eq_sum_add_wick {n : ℕ} {L : ℝ} (hL : 0 < L)
    (δ γ : ℝ) (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d)
    (J : Finset (Fin n)) (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (lam : ℝ × ℝ) :
    physicalWeightedCellSymbol L δ γ z β γ' J C lam =
      (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
        approxSum L (L^(2*γ)*(2*δ)) (halfCellAmplitude z β γ') (resProfile J (fun Ω => C (ofLp Ω) lam)) +
      ((4:ℂ)^n)⁻¹ * normalizedWickCorrection L (2*δ) γ z β γ' J C lam := by
  rw [physicalWeightedCellSymbol_decomposition hL]
  unfold localRemainder
  rw [doubled_coupling_prefactor]
  have h4 : (4:ℂ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  ring

end WaveTurbulence.Flower.FiltCoh
