/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineExpansionCounts
import Mathlib.Tactic

/-! # Atom and group counts for bad and normal vines (TARGET L1515, L1803) -/

public section
namespace WaveTurbulence.Vine

/-- Bad templates have two atoms per group plus the joints; normal templates
have one additional atom, in their unique three-atom group. -/
theorem template_atoms_groups (X : VineType) :
    X.template.n = 2*X.template.groups.length+(if X.IsBad then 2 else 3) := by
  cases X <;> rfl

/-- The exact atom/group relation is preserved by every expansion. -/
theorem expand_atoms_groups (X : VineType) (k : List ℕ)
    (hk : k.length = X.template.slots.length) :
    (X.expand k).n = 2*(X.expand k).groups.length+(if X.IsBad then 2 else 3) := by
  rw [expand_atoms_exact X k hk,expand_groups_exact X k hk,template_atoms_groups]
  omega

end WaveTurbulence.Vine
