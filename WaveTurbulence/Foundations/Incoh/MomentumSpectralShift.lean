/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LocalizedCellProfiles

/-!
# Actual linear Fourier shifts induced by the source integer rows

TARGET (incohproof6–10). Transposing the integer momentum map gives the
root modulation and each link's linear phase; these shifts are computed.
-/

public section
noncomputable section
open WithLp

namespace WaveTurbulence.Incoh

/-- The actual integer row of each leaf or link profile. -/
@[expose] def MomentumTreeData.profileRow {n m w : ℕ} (P : MomentumTreeData n m w) :
    LocalizedCellIndex n m → MomentumCoordinate n → ℤ
  | .inl a => P.inputRow a
  | .inr p => momentumUnitRow (some p)

/-- The actual transpose momentum map, evaluated at the profile Fourier variables. -/
@[expose] def MomentumTreeData.spectralShift {d n m w : ℕ} (P : MomentumTreeData n m w)
    (ξ : LocalizedCellIndex n m → Fin d → ℝ) (j : MomentumCoordinate n) : Mom d :=
  ∑ i, P.profileRow i j • toLp 2 (ξ i)

/-- Every profile's actual momentum is the evaluation of its structural row. -/
theorem MomentumTreeData.localizedCellMomenta_eq_rowEval {d n m w : ℕ}
    (P : MomentumTreeData n m w) (k : Mom d) (x : Fin n → Fin 2 → Mom d)
    (i : LocalizedCellIndex n m) :
    toLp 2 (P.localizedCellMomenta k x i) = momentumRowEval (rootLinkMomenta k x) (P.profileRow i) := by
  cases i with
  | inl a => simp only [localizedCellMomenta, toLp_ofLp, profileRow, inputMomentum]
  | inr p => simp only [localizedCellMomenta, toLp_ofLp, profileRow, momentumRowEval_unit, rootLinkMomenta]

/-- Finite Fubini identifies the source profile phases with the computed link/root shifts. -/
theorem MomentumTreeData.sum_inner_localizedCellMomenta {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ξ : LocalizedCellIndex n m → Fin d → ℝ)
    (k : Mom d) (x : Fin n → Fin 2 → Mom d) :
    (∑ i, inner ℝ (toLp 2 (ξ i)) (toLp 2 (P.localizedCellMomenta k x i))) =
      ∑ j : MomentumCoordinate n, inner ℝ (P.spectralShift ξ j) (rootLinkMomenta k x j) := by
  simp only [P.localizedCellMomenta_eq_rowEval k x]
  change (∑ i, inner ℝ (toLp 2 (ξ i))
    (∑ j : MomentumCoordinate n, P.profileRow i j • rootLinkMomenta k x j)) = _
  simp only [inner_sum, spectralShift, sum_inner, ← Int.cast_smul_eq_zsmul ℝ,
    inner_smul_right, inner_smul_left, conj_trivial]
  rw [Finset.sum_comm]


end WaveTurbulence.Incoh
