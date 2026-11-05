/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineActualRailFrame
public import WaveTurbulence.Foundations.Molecule.VineDoubleRemovalRails
public import WaveTurbulence.Foundations.Molecule.VineFullRungRailEdges
import Mathlib.Tactic

/-! # Complete actual rail paths along single bonds -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace RailLabelFrame
variable {M : Molecule V D} {n : ℕ} {Q : FullRungSequence M n}
    (F : RailLabelFrame Q) (hM : M.IsMolecule) (S : Finset V)
    (hmem : ∀ i,Q.u i ∈ S ∧ Q.v i ∈ S)
include F hM hmem

/-- Each initial upper rail segment is a path of actual single bonds. -/
theorem upper_single_prefix (j : ℕ) (hj : j ≤ n) :
    Relation.EqvGen (SingleGroupAdj M S) (Q.u 0) (Q.u j) := by
  induction j with
  | zero => exact Relation.EqvGen.refl _
  | succ j ih =>
    have hne : Q.u (j+1) ≠ Q.u j := by
      intro he
      have hh := congrArg Fin.val (F.upper_injective
        (a₁ := ⟨j+1,by omega⟩) (a₂ := ⟨j,by omega⟩) he)
      change j+1=j at hh
      omega
    have hprev := Q.upper_prev_adj (j+1) (by omega) hj
    have hd := F.upper_prev_pair_degree hM (j+1) (by omega) hj
    simp only [Nat.add_sub_cancel] at hprev hd
    exact Relation.EqvGen.trans _ _ _ (ih (by omega))
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
        ⟨(hmem (j+1)).1,(hmem j).1,hne,hprev,hd⟩))

/-- The lower initial rail segment is also a path of single bonds. -/
theorem lower_single_prefix (j : ℕ) (hj : j ≤ n) :
    Relation.EqvGen (SingleGroupAdj M S) (Q.v 0) (Q.v j) := by
  induction j with
  | zero => exact Relation.EqvGen.refl _
  | succ j ih =>
    have hne : Q.v (j+1) ≠ Q.v j := by
      intro he
      have hh := congrArg Fin.val (F.lower_injective
        (a₁ := ⟨j+1,by omega⟩) (a₂ := ⟨j,by omega⟩) he)
      change j+1=j at hh
      omega
    have hprev := Q.lower_prev_adj (j+1) (by omega) hj
    have hd := F.lower_prev_pair_degree hM (j+1) (by omega) hj
    simp only [Nat.add_sub_cancel] at hprev hd
    exact Relation.EqvGen.trans _ _ _ (ih (by omega))
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
        ⟨(hmem (j+1)).2,(hmem j).2,hne,hprev,hd⟩))

/-- A positive-length upper slot joins its two old ports by single bonds. -/
theorem upper_single_complete (hn : 1 ≤ n) :
    Relation.EqvGen (SingleGroupAdj M S) (Q.u 0) (Q.u (n+1)) := by
  have hne : Q.u n ≠ Q.u (n+1) := by
    intro he
    have hh := congrArg Fin.val (F.upper_injective
      (a₁ := ⟨n,by omega⟩) (a₂ := ⟨n+1,by omega⟩) he)
    change n=n+1 at hh
    omega
  exact Relation.EqvGen.trans _ _ _ (F.upper_single_prefix hM S hmem n le_rfl)
    (Relation.EqvGen.rel _ _ ⟨(hmem n).1,(hmem (n+1)).1,hne,
      Q.upper_next_adj n hn le_rfl,F.upper_next_pair_degree hM n hn le_rfl⟩)

/-- The corresponding lower slot path joins its two old ports. -/
theorem lower_single_complete (hn : 1 ≤ n) :
    Relation.EqvGen (SingleGroupAdj M S) (Q.v 0) (Q.v (n+1)) := by
  have hne : Q.v n ≠ Q.v (n+1) := by
    intro he
    have hh := congrArg Fin.val (F.lower_injective
      (a₁ := ⟨n,by omega⟩) (a₂ := ⟨n+1,by omega⟩) he)
    change n=n+1 at hh
    omega
  exact Relation.EqvGen.trans _ _ _ (F.lower_single_prefix hM S hmem n le_rfl)
    (Relation.EqvGen.rel _ _ ⟨(hmem n).2,(hmem (n+1)).2,hne,
      Q.lower_next_adj n hn le_rfl,F.lower_next_pair_degree hM n hn le_rfl⟩)

end RailLabelFrame
end WaveTurbulence.Vine
