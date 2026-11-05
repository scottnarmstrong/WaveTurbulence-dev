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

/-- TARGET L1515: a bad vine with m groups has 2m+2 atoms. -/
theorem bad_expand_atoms (X : VineType) (hX : X.IsBad = true) (k : List ℕ)
    (hk : k.length = X.template.slots.length) :
    (X.expand k).n = 2*(X.expand k).groups.length+2 := by
  simpa only [hX,ite_true] using expand_atoms_groups X k hk

/-- Every normal vine has at least its three-atom group. -/
theorem normal_expand_group_pos (X : VineType) (hX : X.IsBad = false) (k : List ℕ)
    (hk : k.length = X.template.slots.length) : 1 ≤ (X.expand k).groups.length := by
  rw [expand_groups_exact X k hk]
  cases X <;> simp_all [VineType.IsBad,VineType.template]
  all_goals omega

/-- TARGET L1803: a normal vine with m two-atom groups has 2m+5 atoms. -/
theorem normal_expand_atoms (X : VineType) (hX : X.IsBad = false) (k : List ℕ)
    (hk : k.length = X.template.slots.length) :
    (X.expand k).n = 2*((X.expand k).groups.length-1)+5 := by
  have h := expand_atoms_groups X k hk
  have hp := normal_expand_group_pos X hX k hk
  simp only [hX,Bool.false_eq_true,ite_false] at h
  omega

end WaveTurbulence.Vine
