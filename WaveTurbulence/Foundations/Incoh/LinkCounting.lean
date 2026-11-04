/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.LayerLink

/-!
# Counting the incoherent links

TARGET (incohproof16): the incoherence count is an actual finite filter,
so it never exceeds the number of links. Nontrivial incoherence implies
at least one link, as used when absorbing one cutoff-dependent constant.
-/

public section

namespace WaveTurbulence.Incoh

/-- The computed incoherence count never exceeds the number of links. -/
theorem incoherenceCount_le {d n : ℕ} (Q : Fin n → LayerLink d) : incoherenceCount Q ≤ n := by
  classical
  unfold incoherenceCount
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

/-- A nonzero incoherence count implies a nonempty link family. -/
theorem one_le_linkCount_of_incoherent {d n : ℕ} (Q : Fin n → LayerLink d)
    (hg : 1 ≤ incoherenceCount Q) : 1 ≤ n := hg.trans (incoherenceCount_le Q)

end WaveTurbulence.Incoh
