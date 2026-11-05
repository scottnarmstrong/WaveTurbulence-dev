/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.UnitCounts

/-! # The source fourth-power range makes attached truncation automatic

TARGET lftwistprop uses total order at most `N_(p+1)^4`. The restriction
`p+1 ≤ D` is essential because the parameter definitions saturate beyond D.
-/

public section
namespace WaveTurbulence.LFTwist

/-- A small arithmetic consequence of the source downward parameter recursion. -/
theorem N_fourth_le_pred (P : WTParams) {q : ℕ} (hq : 1 ≤ q)
    (hD : q ≤ P.D) (hd : 1 ≤ P.d) : P.N q ^ 4 ≤ P.N (q - 1) := by
  unfold WTParams.N WTParams.R
  rw [show P.D - (q - 1) = (P.D - q) + 1 by omega, WTParams.Rdown]
  set x := P.Rdown (P.D - q) ^ (40 * P.d)
  change x ^ 4 ≤ (x ^ (40 * P.d)) ^ (40 * P.d)
  by_cases hx : x = 0
  · simp [hx, show 40 * P.d ≠ 0 by omega]
  · exact (pow_le_pow_right' (show 1 ≤ x by omega) (show 4 ≤ 40 * P.d by omega)).trans
      (Nat.le_self_pow (show 40 * P.d ≠ 0 by omega) _)

/-- Truncation in the source fourth-power range tests only top-tree counts. -/
theorem source_trunc_iff_topOrder {w : ℕ} (LG : LayeredGarden w) (P : WTParams)
    {p : ℕ} (hD : p + 1 ≤ P.D) (hd : 1 ≤ P.d)
    (hn : LG.garden.order ≤ P.N (p + 1) ^ 4) :
    LG.IsTrunc p (P.N (p + 1)) (P.N p) ↔
      ∀ j, LG.topOrder p j ≤ P.N (p + 1) := by
  apply trunc_iff_topOrder
  exact hn.trans (by simpa using N_fourth_le_pred P (q := p + 1) (by omega) hD hd)

end WaveTurbulence.LFTwist
