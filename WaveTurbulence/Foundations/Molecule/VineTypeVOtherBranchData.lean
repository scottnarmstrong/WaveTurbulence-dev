/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineOtherBranchMembership
public import WaveTurbulence.Foundations.Molecule.VineSlotProtectedPaths
import Mathlib.Tactic

/-! # Type-V rails avoid a second branch sharing only the joints -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The source type-V slot gives protected primitive rail data after
another branch sharing only the two joints is removed. All old slot
ports and every fresh rung are nonjoint atoms of the retained branch. -/
theorem VineRealization.typeV_other_branch_slot_data {M : Molecule V D}
    {B : Finset V} {a b : V} (R : VineRealization M .V B a b) (hB : M.IsBlock B a b)
    (A : Finset V) (hAB : A ∩ B={a,b}) (k : ℕ) (hk : R.k=[k]) :
    ∃ Q : FullRungSequence M k,(∀ i,Q.u i ∈ B ∧ Q.v i ∈ B) ∧
      (R.f (Q.u 0)=2 ∧ R.f (Q.v 0)=3 ∧ R.f (Q.u (k+1))=4 ∧ R.f (Q.v (k+1))=5) ∧
      (∀ i,1 ≤ i → i ≤ k → R.f (Q.u i)=9+(i-1) ∧ R.f (Q.v i)=9+k+(i-1)) ∧
      RailAvoidsPiece Q A a b ∧
      (k=0 → ¬(Q.u 0 ∈ A ∧ Q.u (k+1) ∈ A) ∧ ¬(Q.v 0 ∈ A ∧ Q.v (k+1) ∈ A)) := by
  have hloc : VineType.V.template.slots.zip R.k=[]++(((2,4),(3,5)),k)::[] := by rw [hk]; rfl
  obtain ⟨Q,hmem,hports,hlabels⟩ := R.has_rungSequence_ports [] [] ((2,4),(3,5)) k hloc
  change R.f (Q.u 0)=2 ∧ R.f (Q.v 0)=3 ∧ R.f (Q.u (k+1))=4 ∧ R.f (Q.v (k+1))=5 at hports
  have hlabels' : ∀ i,1 ≤ i → i ≤ k →
      R.f (Q.u i)=9+(i-1) ∧ R.f (Q.v i)=9+k+(i-1) := hlabels
  have H : RailAvoidsPiece Q A a b := by
    constructor
    · intro i _hi
      exact ⟨other_branch_atoms_survive hAB (hmem i).1,other_branch_atoms_survive hAB (hmem i).2⟩
    · intro i hi hin
      exact ⟨R.nonjoint_outside_other_branch hB A hAB (hmem i).1 (by rw [(hlabels' i hi hin).1]; omega),
        R.nonjoint_outside_other_branch hB A hAB (hmem i).2 (by rw [(hlabels' i hi hin).2]; omega)⟩
  refine ⟨Q,hmem,hports,hlabels',H,?_⟩
  intro _hz
  constructor
  · intro hm
    exact R.nonjoint_outside_other_branch hB A hAB (hmem 0).1 (by rw [hports.1]) hm.1
  · intro hm
    exact R.nonjoint_outside_other_branch hB A hAB (hmem 0).2 (by rw [hports.2.1]; omega) hm.1

end WaveTurbulence.Vine
