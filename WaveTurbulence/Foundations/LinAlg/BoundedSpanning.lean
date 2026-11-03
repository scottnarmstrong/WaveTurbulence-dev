/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LinAlg.MaxVolume
public import WaveTurbulence.Frozen.Defs.Mom

/-!
# Bounded spanning selection

TARGET Lemma A.7 (`lincomblem`, L2449–L2457). The maximal-volume proof gives
coefficients bounded by one, strengthening the source bound `2^(d-1)`.
Natural subtraction in that bound also covers `d = 0` (the selection is empty).
-/

public section

namespace WaveTurbulence.LinAlg

/-- TARGET Lemma A.7: select at most `d` vectors of a finite set spanning it
with coefficients bounded by `2^(d-1)`. -/
theorem exists_bounded_spanning_selection {d : ℕ} (S : Finset (Mom d)) :
    ∃ q ≤ d, ∃ X : Fin q → Mom d,
      (∀ i, X i ∈ S) ∧ ∀ Y ∈ S, ∃ c : Fin q → ℝ,
        (∀ i, |c i| ≤ (2 : ℝ) ^ (d - 1)) ∧ (∑ i, c i • X i) = Y := by
  obtain ⟨q, hq, X, hX, hspan⟩ := exists_spanning_selection S
  refine ⟨q, ?_, X, hX, ?_⟩
  · simpa [Mom] using hq
  intro Y hY
  obtain ⟨c, hc, hsum⟩ := hspan Y hY
  exact ⟨c, fun i => (hc i).trans (one_le_pow₀ (by norm_num)), hsum⟩

end WaveTurbulence.LinAlg
