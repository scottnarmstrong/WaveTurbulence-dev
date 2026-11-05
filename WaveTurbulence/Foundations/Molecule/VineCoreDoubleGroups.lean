/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineTemplates
import Mathlib.Tactic

/-! # Finite core multiplicities determine the nonjoint double-bond groups -/

public section
namespace WaveTurbulence.Vine

/-- No base template contains a loop. -/
theorem template_no_loop_counts (X : VineType) : ∀ i : Fin X.template.n,
    X.template.bonds.count (i.1,i.1)=0 := by
  cases X <;> decide

/-- Every nonjoint doubled core pair belongs to one pinned coherence group.
The exceptional single pair in VII contributes no doubled edge here. -/
theorem template_double_same_group (X : VineType) : ∀ i j : Fin X.template.n,
    2 ≤ i.1 → 2 ≤ j.1 → i ≠ j →
    2 ≤ X.template.bonds.count (i.1,j.1)+X.template.bonds.count (j.1,i.1) →
      ∃ q : Fin X.template.groups.length,
        i.1 ∈ X.template.groups[q.1] ∧ j.1 ∈ X.template.groups[q.1] := by
  cases X <;> decide

end WaveTurbulence.Vine
