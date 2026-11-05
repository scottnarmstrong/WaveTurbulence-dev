/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCoreJointEdges
public import WaveTurbulence.Foundations.Molecule.VineThinEmptyPairs
public import WaveTurbulence.Foundations.Molecule.VineActualPartition
import Mathlib.Tactic

/-! # Empty stem pairs next to an absent outer vine joint -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- Either original joint label names one of the actual outer joints. -/
theorem VineRealization.core_joint_eq {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b) (hS : M.IsBlock S a b)
    (i : Fin X.template.n) (hi : i.1<2) : (R.coreAtom i).1=a ∨ (R.coreAtom i).1=b := by
  apply (realization_index_lt_two_iff R hS (R.coreAtom i).2).mp
  rw [R.label_coreAtom]
  exact hi

/-- A core double pair adjacent to an absent outer joint is absent from
a connected block larger than two atoms, for arbitrary slot rung counts.
The graph hypotheses are literal core edges and distinct finite indices. -/
theorem core_stem_start_absent (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (hS : M.IsBlock S a b) {A : Finset V} {x y : V} (hA : M.IsBlock A x y)
    (hC : GroupConnected M A) (hcard : 2<A.card) (ha : a ∉ A) (hb : b ∉ A)
    (j i k : Fin X.template.n) (hj : j.1<2) (hik : i ≠ k) (hji : j ≠ i) (hjk : j ≠ k)
    (hdouble : 2 ≤ X.template.bonds.count (i.1,k.1))
    (hrail1 : (j.1,i.1) ∈ X.template.bonds) (hrail2 : (j.1,k.1) ∈ X.template.bonds) :
    (R.coreAtom i).1 ∉ A ∧ (R.coreAtom k).1 ∉ A := by
  have hjA : (R.coreAtom j).1 ∉ A := by
    rcases R.core_joint_eq hS j hj with he | he
    · simpa only [he] using ha
    · simpa only [he] using hb
  obtain ⟨Rd⟩ := R.core_twoIncidences i k hdouble
  apply block_empty_double_pair M hM hA hC hcard Rd
    (fun he => hik (R.coreAtom_injective he)) hjA hjA
    (fun he => hjk (R.coreAtom_injective he)) (fun he => hji (R.coreAtom_injective he))
  · exact Mole.adj_symmetric M (R.core_joint_adj j i hj hrail1)
  · exact Mole.adj_symmetric M (R.core_joint_adj j k hj hrail2)

/-- The same propagation starts from two different absent outer joints,
as in type V, whose first pair has one rail to each outer joint. -/
theorem core_stem_start_absent_two_joints (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (hS : M.IsBlock S a b) {A : Finset V} {x y : V} (hA : M.IsBlock A x y)
    (hC : GroupConnected M A) (hcard : 2<A.card) (ha : a ∉ A) (hb : b ∉ A)
    (j l i k : Fin X.template.n) (hj : j.1<2) (hl : l.1<2)
    (hik : i ≠ k) (hl_i : l ≠ i) (hj_k : j ≠ k)
    (hdouble : 2 ≤ X.template.bonds.count (i.1,k.1))
    (hrail1 : (j.1,i.1) ∈ X.template.bonds) (hrail2 : (l.1,k.1) ∈ X.template.bonds) :
    (R.coreAtom i).1 ∉ A ∧ (R.coreAtom k).1 ∉ A := by
  have absent (t : Fin X.template.n) (ht : t.1<2) : (R.coreAtom t).1 ∉ A := by
    rcases R.core_joint_eq hS t ht with he | he
    · simpa only [he] using ha
    · simpa only [he] using hb
  obtain ⟨Rd⟩ := R.core_twoIncidences i k hdouble
  apply block_empty_double_pair M hM hA hC hcard Rd
    (fun he => hik (R.coreAtom_injective he)) (absent j hj) (absent l hl)
    (fun he => hj_k (R.coreAtom_injective he)) (fun he => hl_i (R.coreAtom_injective he))
  · exact Mole.adj_symmetric M (R.core_joint_adj j i hj hrail1)
  · exact Mole.adj_symmetric M (R.core_joint_adj l k hl hrail2)

end WaveTurbulence.Vine
