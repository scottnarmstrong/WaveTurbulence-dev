/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineLatticeGaps
import Mathlib.Tactic

/-! # Gap-kind separation used by TARGET subsetvc -/

public section
namespace WaveTurbulence.Vine

/-- The pinned SG condition includes nonzero gap and its exact upper bound. -/
theorem gapKind_eq_SG_iff {d : ℕ} (L γ η : ℝ) (r : Mom d) :
    Molecule.gapKind L γ η r=.SG ↔ r ≠ 0 ∧ ‖r‖ ≤ L^(-γ+η) := by
  classical
  unfold Molecule.gapKind
  split_ifs <;> simp_all

/-- Gap kind is invariant under reversing the ordered joint or gap sign. -/
theorem gapKind_neg {d : ℕ} (L γ η : ℝ) (r : Mom d) :
    Molecule.gapKind L γ η (-r)=Molecule.gapKind L γ η r := by
  classical
  simp only [Molecule.gapKind,neg_eq_zero,norm_neg]

/-- Equal gap norms imply equal kinds, including the zero/nonzero distinction. -/
theorem gapKind_eq_of_norm_eq {d : ℕ} (L γ η : ℝ) {r r' : Mom d}
    (hn : ‖r‖=‖r'‖) : Molecule.gapKind L γ η r=Molecule.gapKind L γ η r' := by
  classical
  have hz : r=0 ↔ r'=0 :=
    ⟨fun h => norm_eq_zero.mp (hn.symm.trans (norm_eq_zero.mpr h)),
      fun h => norm_eq_zero.mp (hn.trans (norm_eq_zero.mpr h))⟩
  simp only [Molecule.gapKind,hz,hn]

end WaveTurbulence.Vine
