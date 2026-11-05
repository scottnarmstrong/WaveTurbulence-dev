/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineMixedSinglePaths
public import WaveTurbulence.Foundations.Molecule.VineActualRailFrame
public import WaveTurbulence.Foundations.Molecule.VineFullRungRailEdges
import Mathlib.Tactic

/-! # Rail paths avoiding the bonds and interior of one ordinary removal -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Primitive membership facts for a rail frame outside one removed piece.
Every fresh atom is outside the piece; its four old ports survive. -/
structure RailAvoidsPiece {M : Molecule V D} {n : ℕ} (Q : FullRungSequence M n)
    (A : Finset V) (a b : V) : Prop where
  survive : ∀ i,i ≤ n+1 → Q.u i ∉ A \ {a,b} ∧ Q.v i ∉ A \ {a,b}
  fresh : ∀ i,1 ≤ i → i ≤ n → Q.u i ∉ A ∧ Q.v i ∉ A

namespace RailLabelFrame
variable {M : Molecule V D} {n : ℕ} {Q : FullRungSequence M n}
    (F : RailLabelFrame Q) (hM : M.IsMolecule) (S A : Finset V) (a b : V)
    (hmem : ∀ i,Q.u i ∈ S ∧ Q.v i ∈ S) (H : RailAvoidsPiece Q A a b)
include F hM hmem H

/-- Each protected upper predecessor edge is single and survives the piece. -/
theorem upper_protected_prev (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    ProtectedSingleAdj M S A a b (Q.u i) (Q.u (i-1)) := by
  have hne : Q.u i ≠ Q.u (i-1) := by
    intro he
    have hh := congrArg Fin.val (F.upper_injective
      (a₁ := ⟨i,by omega⟩) (a₂ := ⟨i-1,by omega⟩) he)
    change i=i-1 at hh
    omega
  exact ⟨⟨(hmem i).1,(hmem (i-1)).1,hne,Q.upper_prev_adj i hi hin,
    F.upper_prev_pair_degree hM i hi hin⟩,(H.survive i (by omega)).1,
    (H.survive (i-1) (by omega)).1,fun h => (H.fresh i hi hin).1 h.1⟩

/-- The corresponding protected lower predecessor edge. -/
theorem lower_protected_prev (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    ProtectedSingleAdj M S A a b (Q.v i) (Q.v (i-1)) := by
  have hne : Q.v i ≠ Q.v (i-1) := by
    intro he
    have hh := congrArg Fin.val (F.lower_injective
      (a₁ := ⟨i,by omega⟩) (a₂ := ⟨i-1,by omega⟩) he)
    change i=i-1 at hh
    omega
  exact ⟨⟨(hmem i).2,(hmem (i-1)).2,hne,Q.lower_prev_adj i hi hin,
    F.lower_prev_pair_degree hM i hi hin⟩,(H.survive i (by omega)).2,
    (H.survive (i-1) (by omega)).2,fun h => (H.fresh i hi hin).2 h.1⟩

/-- The full initial upper rail segment avoids the removed piece. -/
theorem upper_protected_prefix (j : ℕ) (hj : j ≤ n) :
    Relation.EqvGen (ProtectedSingleAdj M S A a b) (Q.u 0) (Q.u j) := by
  induction j with
  | zero => exact Relation.EqvGen.refl _
  | succ j ih =>
    have he := F.upper_protected_prev hM S A a b hmem H (j+1) (by omega) hj
    simp only [Nat.add_sub_cancel] at he
    exact Relation.EqvGen.trans _ _ _ (ih (by omega))
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ he))

/-- The full initial lower rail segment avoids the removed piece. -/
theorem lower_protected_prefix (j : ℕ) (hj : j ≤ n) :
    Relation.EqvGen (ProtectedSingleAdj M S A a b) (Q.v 0) (Q.v j) := by
  induction j with
  | zero => exact Relation.EqvGen.refl _
  | succ j ih =>
    have he := F.lower_protected_prev hM S A a b hmem H (j+1) (by omega) hj
    simp only [Nat.add_sub_cancel] at he
    exact Relation.EqvGen.trans _ _ _ (ih (by omega))
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ he))

/-- A positive-length protected upper rail joins its surviving old ports. -/
theorem upper_protected_complete (hn : 1 ≤ n) :
    Relation.EqvGen (ProtectedSingleAdj M S A a b) (Q.u 0) (Q.u (n+1)) := by
  have hne : Q.u n ≠ Q.u (n+1) := by
    intro he
    have hh := congrArg Fin.val (F.upper_injective
      (a₁ := ⟨n,by omega⟩) (a₂ := ⟨n+1,by omega⟩) he)
    change n=n+1 at hh
    omega
  exact Relation.EqvGen.trans _ _ _ (F.upper_protected_prefix hM S A a b hmem H n le_rfl)
    (Relation.EqvGen.rel _ _ ⟨⟨(hmem n).1,(hmem (n+1)).1,hne,
      Q.upper_next_adj n hn le_rfl,F.upper_next_pair_degree hM n hn le_rfl⟩,
      (H.survive n (by omega)).1,(H.survive (n+1) le_rfl).1,
      fun h => (H.fresh n hn le_rfl).1 h.1⟩)

/-- The protected lower rail joins its surviving old ports as well. -/
theorem lower_protected_complete (hn : 1 ≤ n) :
    Relation.EqvGen (ProtectedSingleAdj M S A a b) (Q.v 0) (Q.v (n+1)) := by
  have hne : Q.v n ≠ Q.v (n+1) := by
    intro he
    have hh := congrArg Fin.val (F.lower_injective
      (a₁ := ⟨n,by omega⟩) (a₂ := ⟨n+1,by omega⟩) he)
    change n=n+1 at hh
    omega
  exact Relation.EqvGen.trans _ _ _ (F.lower_protected_prefix hM S A a b hmem H n le_rfl)
    (Relation.EqvGen.rel _ _ ⟨⟨(hmem n).2,(hmem (n+1)).2,hne,
      Q.lower_next_adj n hn le_rfl,F.lower_next_pair_degree hM n hn le_rfl⟩,
      (H.survive n (by omega)).2,(H.survive (n+1) le_rfl).2,
      fun h => (H.fresh n hn le_rfl).2 h.1⟩)

end RailLabelFrame
end WaveTurbulence.Vine
