/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCoreAtoms
public import WaveTurbulence.Foundations.Molecule.VineRealizationAdjacency
import Mathlib.Tactic

/-! # Exact survival of core edges outside the marked slots -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- An unmarked original edge keeps all its copies through expansion. -/
theorem expand_untouched_edge_count (X : VineType) (ks : List ℕ) (e : ℕ×ℕ)
    (he : ∀ s ∈ X.template.slots,e ≠ s.1 ∧ e ≠ s.2) :
    X.template.bonds.count e ≤ (X.expand ks).bonds.count e := by
  apply count_le_fold_insertRungs
  intro sk hsk
  exact he sk.1 (List.of_mem_zip hsk).1

/-- Every unmarked core edge is present in the actual expanded molecule. -/
theorem VineRealization.core_untouched_adj {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b) (i j : Fin X.template.n)
    (hmem : (i.1,j.1) ∈ X.template.bonds)
    (he : ∀ s ∈ X.template.slots,(i.1,j.1) ≠ s.1 ∧ (i.1,j.1) ≠ s.2) :
    M.Adj (R.coreAtom i).1 (R.coreAtom j).1 := by
  apply R.adj_of_edge (R.coreAtom i).2 (R.coreAtom j).2
  rw [R.label_coreAtom,R.label_coreAtom]
  apply Or.inl
  apply List.count_pos_iff.mp
  exact (List.count_pos_iff.mpr hmem).trans_le (expand_untouched_edge_count X R.k _ he)

end WaveTurbulence.Vine
