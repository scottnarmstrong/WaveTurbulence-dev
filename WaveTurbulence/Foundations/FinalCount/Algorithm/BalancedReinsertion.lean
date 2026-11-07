/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.BalancedDeletion
public import WaveTurbulence.Foundations.FinalCount.Algorithm.BalancedInsertion
public import WaveTurbulence.Foundations.FinalCount.AppBResidualLabels
import Mathlib.Tactic

/-! # Controlled costs for the source reinsertion and combined R3 operations -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem postWithBond_balanced_drop_le (M : Molecule V D) (hM : M.IsMolecule)
    (k : AppbPatternKind) (r : AppbRealization M k.pattern) (a b : ℕ)
    (ha : a ∈ k.pattern.vertices) (hb : b ∈ k.pattern.vertices)
    (hka : a ∉ k.pattern.removed) (hkb : b ∉ k.pattern.removed) (hab : a ≠ b)
    (hpath : r.post.SameComponent (r.vertex a) (r.vertex b)) :
    balancedPotential M-8100 ≤ balancedPotential (r.postWithBond a b) := by
  have hdel := pattern_deletion_balanced_drop_le M hM k r
  have hM' := appb_eraseAtoms_isMolecule M hM r.removedAtoms
  have hneq : r.vertex a ≠ r.vertex b := (r.vertex_eq_iff a b ha hb).not.mpr hab
  have hadd := same_component_insertion_balanced_drop_le r.post hM'
    (r.vertex_mem_post a ha hka) (r.vertex_mem_post b hb hkb) hneq hpath
  change balancedPotential r.post-50 ≤ balancedPotential (r.postWithBond a b) at hadd
  omega

theorem directedPostWithBond_balanced_drop_le (M : Molecule V D) (hM : M.IsMolecule)
    (k : AppbPatternKind) (r : AppbRealization M k.pattern) (a b : ℕ) (i : Fin k.pattern.edges.length)
    (ha : a ∈ k.pattern.vertices) (hb : b ∈ k.pattern.vertices)
    (hka : a ∉ k.pattern.removed) (hkb : b ∉ k.pattern.removed) (hab : a ≠ b)
    (hpath : r.post.SameComponent (r.vertex a) (r.vertex b)) :
    balancedPotential M-8100 ≤ balancedPotential (r.directedPostWithBond a b i) := by
  unfold AppbRealization.directedPostWithBond
  split_ifs
  · exact postWithBond_balanced_drop_le M hM k r a b ha hb hka hkb hab hpath
  · exact postWithBond_balanced_drop_le M hM k r b a hb ha hkb hka hab.symm hpath.symm

/-- The two literal deletions in source 3R-2G have a uniform combined
resource cost; all possible vertex overlaps are retained in the post graph. -/
theorem r32_balanced_drop_le (M : Molecule V D) (hM : M.IsMolecule)
    (r : AppbRealization M AppbPatternKind.r3.pattern)
    (t : AppbRealization r.post AppbPatternKind.s33new3.pattern) :
    balancedPotential M-16000 ≤ balancedPotential t.post := by
  have h1 := pattern_deletion_balanced_drop_le M hM .r3 r
  have hM' := appb_eraseAtoms_isMolecule M hM r.removedAtoms
  have h2 := pattern_deletion_balanced_drop_le r.post hM' .s33new3 t
  omega

end WaveTurbulence.Mole.AppbAlgorithm
