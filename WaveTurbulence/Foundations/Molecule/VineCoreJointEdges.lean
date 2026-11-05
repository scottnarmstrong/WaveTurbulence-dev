/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCoreAtoms
public import WaveTurbulence.Foundations.Molecule.VineRealizationAdjacency
import Mathlib.Tactic

/-! # Original joint edges survive all rung insertions -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- The first endpoint of each encoded slot rail is a non-joint atom. -/
theorem template_slot_nonjoints (X : VineType) :
    ∀ s ∈ X.template.slots,2 ≤ s.1.1 ∧ 2 ≤ s.2.1 := by
  cases X <;> decide

/-- Every old bond incident to an original joint keeps all its copies. -/
theorem expand_joint_edge_count (X : VineType) (ks : List ℕ) (i j : ℕ) (hi : i<2) :
    X.template.bonds.count (i,j) ≤ (X.expand ks).bonds.count (i,j) := by
  apply count_le_fold_insertRungs
  intro sk hsk
  have hs := template_slot_nonjoints X sk.1 (List.of_mem_zip hsk).1
  constructor
  · intro he
    have hh := congrArg (fun e : ℕ×ℕ => e.1) he
    dsimp only at hh
    omega
  · intro he
    have hh := congrArg (fun e : ℕ×ℕ => e.1) he
    dsimp only at hh
    omega

/-- An original joint-to-core edge is an actual edge after any expansion. -/
theorem VineRealization.core_joint_adj {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b) (i j : Fin X.template.n)
    (hi : i.1<2) (he : (i.1,j.1) ∈ X.template.bonds) :
    M.Adj (R.coreAtom i).1 (R.coreAtom j).1 := by
  apply R.adj_of_edge (R.coreAtom i).2 (R.coreAtom j).2
  rw [R.label_coreAtom,R.label_coreAtom]
  apply Or.inl
  apply List.count_pos_iff.mp
  exact (List.count_pos_iff.mpr he).trans_le (expand_joint_edge_count X R.k i.1 j.1 hi)

end WaveTurbulence.Vine
