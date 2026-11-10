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

end WaveTurbulence.LFTwist
