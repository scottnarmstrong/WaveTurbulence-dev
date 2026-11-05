/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineHyperTransitions
public import WaveTurbulence.Foundations.Molecule.VineRungPairIndices
import Mathlib.Tactic

/-! # A hyper-block has at most one transition along any full-rung sequence -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Hyper-block membership is matched on every rung of any length sequence. -/
theorem hyperBlock_sequence_pair_membership (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (hH : Mole.IsHyperBlock M S a b) {n : ℕ}
    (Q : FullRungSequence M n) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    Q.u i ∈ S ↔ Q.v i ∈ S :=
  hyperBlock_rung_membership M hM hH (Q.upper i hi hin) (Q.lower i hi hin)

/-- A membership drop places both joints at its selected left rung. -/
theorem hyperBlock_drop_joints (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (hH : Mole.IsHyperBlock M S a b) {n : ℕ}
    (Q : FullRungSequence M n) (i : ℕ) (hi : 1 ≤ i) (hin : i+1 ≤ n)
    (hx : Q.u i ∈ S) (hnext : Q.u (i+1) ∉ S) :
    ({Q.u i,Q.v i} : Finset V)={a,b} := by
  have hy := (hyperBlock_sequence_pair_membership M hM hH Q i hi (by omega)).mp hx
  have hynext : Q.v (i+1) ∉ S := fun hy => hnext
    ((hyperBlock_sequence_pair_membership M hM hH Q (i+1) (by omega) hin).mpr hy)
  exact hyperBlock_transition_joints M hM hH (Q.upper i hi (by omega))
    (Q.lower i hi (by omega)) hx hy (Q.upper_ne_lower hi (by omega) hi (by omega))
    (Or.inr hnext) (Or.inr hynext)

/-- A membership rise places both joints at its selected right rung. -/
theorem hyperBlock_rise_joints (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (hH : Mole.IsHyperBlock M S a b) {n : ℕ}
    (Q : FullRungSequence M n) (i : ℕ) (hi : 1 ≤ i) (hin : i+1 ≤ n)
    (hx : Q.u i ∉ S) (hnext : Q.u (i+1) ∈ S) :
    ({Q.u (i+1),Q.v (i+1)} : Finset V)={a,b} := by
  have hy := (hyperBlock_sequence_pair_membership M hM hH Q (i+1) (by omega) hin).mp hnext
  have hyprev : Q.v i ∉ S := fun hy => hx
    ((hyperBlock_sequence_pair_membership M hM hH Q i hi (by omega)).mpr hy)
  apply hyperBlock_transition_joints M hM hH (Q.upper (i+1) (by omega) hin)
    (Q.lower (i+1) (by omega) hin) hnext hy
    (Q.upper_ne_lower (by omega) hin (by omega) hin)
  · exact Or.inl (by simpa only [Nat.add_sub_cancel] using hx)
  · exact Or.inl (by simpa only [Nat.add_sub_cancel] using hyprev)

/-- TARGET subsetvc, hyper-block ladder reduction: two membership jumps in
one full-rung sequence must be the same jump. This holds for every length. -/
theorem hyperBlock_sequence_jump_unique (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (hH : Mole.IsHyperBlock M S a b) {n : ℕ}
    (Q : FullRungSequence M n) {i j : ℕ} (hi : 1 ≤ i) (hin : i+1 ≤ n)
    (hj : 1 ≤ j) (hjn : j+1 ≤ n)
    (hjumpi : ¬(Q.u i ∈ S ↔ Q.u (i+1) ∈ S))
    (hjumpj : ¬(Q.u j ∈ S ↔ Q.u (j+1) ∈ S)) : i=j := by
  have hcasesi : (Q.u i ∈ S ∧ Q.u (i+1) ∉ S) ∨
      (Q.u i ∉ S ∧ Q.u (i+1) ∈ S) := by tauto
  have hcasesj : (Q.u j ∈ S ∧ Q.u (j+1) ∉ S) ∨
      (Q.u j ∉ S ∧ Q.u (j+1) ∈ S) := by tauto
  rcases hcasesi with ⟨hxi,hni⟩ | ⟨hni,hxi⟩
  · have hei := hyperBlock_drop_joints M hM hH Q i hi hin hxi hni
    rcases hcasesj with ⟨hxj,hnj⟩ | ⟨hnj,hxj⟩
    · have hej := hyperBlock_drop_joints M hM hH Q j hj hjn hxj hnj
      exact Q.pair_index_eq hi (by omega) hj (by omega) (hei.trans hej.symm)
    · have hej := hyperBlock_rise_joints M hM hH Q j hj hjn hnj hxj
      have he := Q.pair_index_eq hi (by omega) (by omega) hjn (hei.trans hej.symm)
      have hp := hyperBlock_rung_not_isolated M hM hH (Q.upper i hi (by omega)) hxi
      have hprev : Q.u (i-1) ∉ S := by simpa only [show i-1=j by omega] using hnj
      exact False.elim (hp.elim hprev hni)
  · have hei := hyperBlock_rise_joints M hM hH Q i hi hin hni hxi
    rcases hcasesj with ⟨hxj,hnj⟩ | ⟨hnj,hxj⟩
    · have hej := hyperBlock_drop_joints M hM hH Q j hj hjn hxj hnj
      have he := Q.pair_index_eq (by omega) hin hj (by omega) (hei.trans hej.symm)
      have hp := hyperBlock_rung_not_isolated M hM hH (Q.upper j hj (by omega)) hxj
      have hprev : Q.u (j-1) ∉ S := by simpa only [show j-1=i by omega] using hni
      exact False.elim (hp.elim hprev hnj)
    · have hej := hyperBlock_rise_joints M hM hH Q j hj hjn hnj hxj
      have he := Q.pair_index_eq (by omega) hin (by omega) hjn (hei.trans hej.symm)
      omega

end WaveTurbulence.Vine
