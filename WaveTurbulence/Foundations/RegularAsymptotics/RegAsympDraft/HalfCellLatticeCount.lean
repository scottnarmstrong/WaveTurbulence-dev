/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.HalfCellAmplitudeSupport
public import WaveTurbulence.Foundations.ApproxNT.Cells
import Mathlib.Tactic

/-! # The free vector count on a Wick zero-coordinate slice

A retained half-cell contains at most 2^d L^d lattice points for L≥1,
uniformly in its center. This is the dimensional counting loss in the
exceptional-set estimate.
-/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Incoh ApproxNT

/-- A fixed finite box containing the actual half-cell lattice support. -/
def halfCellLatticeBox {d : ℕ} (L : ℝ) (z : Fin d → ℤ) : Finset (Fin d → ℤ) :=
  intBox ((L/2:ℝ) • NTSP.intVec z) (L/2)

/-- All actual nonzero lattice values belong to the uniform translated box. -/
theorem mem_halfCellLatticeBox {d : ℕ} {L : ℝ} (hL : 0 < L)
    {z p : Fin d → ℤ} (hp : halfLinkCell z (latticePoint L p) ≠ 0) : p ∈ halfCellLatticeBox L z := by
  have hθ : thetaMom d ((2:ℝ) • latticePoint L p-NTSP.intVec z) ≠ 0 := by
    intro hz
    exact hp (by simp only [halfLinkCell,hz,Complex.ofReal_zero])
  apply mem_intBox
  intro i
  have hi := abs_lt_one_of_thetaMom_ne_zero hθ i
  change |2*((p i:ℝ)/L)-(z i:ℝ)| < 1 at hi
  change |(p i:ℝ)-(L/2)*(z i:ℝ)| ≤ L/2
  have he : (p i:ℝ)-(L/2)*(z i:ℝ) = (L/2)*(2*((p i:ℝ)/L)-(z i:ℝ)) := by
    field_simp
  rw [he,abs_mul,abs_of_nonneg (by positivity : 0 ≤ L/2)]
  exact (mul_le_mul_of_nonneg_left hi.le (by positivity : 0 ≤ L/2)).trans_eq (mul_one _)

/-- The dimensional count is independent of the center and all modulations. -/
theorem card_halfCellLatticeBox_le {d : ℕ} {L : ℝ} (hL : 1 ≤ L) (z : Fin d → ℤ) :
    ((halfCellLatticeBox L z).card:ℝ) ≤ 2^d*L^d := by
  have h := card_intBox_le ((L/2:ℝ) • NTSP.intVec z) (by positivity : 0 ≤ L/2)
  apply h.trans
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  linarith only [hL]

/-- The uncounted amplitude factor on the slice has norm at most one. -/
theorem norm_halfLinkCell_le_one {d : ℕ} (z : Fin d → ℤ) (x : Mom d) :
    ‖halfLinkCell z x‖ ≤ 1 := by
  rw [halfLinkCell,Complex.norm_real,Real.norm_of_nonneg (thetaMom_nonneg _)]
  exact thetaMom_le_one _

end WaveTurbulence.RegAsymp
