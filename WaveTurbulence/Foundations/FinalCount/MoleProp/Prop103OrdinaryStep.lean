/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103CoreGeometry
public import WaveTurbulence.Foundations.FinalCount.MoleProp.LowDegreeConnectivity
public import WaveTurbulence.Foundations.FinalCount.MoleProp.SimpleGraphRank
public import WaveTurbulence.Foundations.FinalCount.Degen.EraseMolecule
public import WaveTurbulence.Foundations.FinalCount.Degen.LadderDeletionGeometry
import Mathlib.Tactic

/-! # Exact rank and surviving-vertex progress of an ordinary source R/B step -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Removing the chosen degree-three atom of a bridgeless graph loses
exactly two circuits, even when unrelated components are present. -/
theorem circuitRank_erase_three_of_bridgeless (M : Molecule V D)
    (hloop : ∀ x, M.atom x ≠ M.atom (M.mate x))
    (hbridge : ∀ e, ¬ IsBridge M e) {v : V}
    (hv : v ∈ M.atoms) (hv3 : M.deg v = 3) :
    (eraseAtoms M {v}).circuitRank = M.circuitRank - 2 := by
  have hlo := newComponents_card_pos_of_degree_pos M hloop hv (by omega)
  have hhi := card_newComponents_singleton_le_one M hbridge (by omega : M.deg v ≤ 3)
  have hcard : (newComponents M {v}).card = 1 := by omega
  have hi := incident_card_eq_deg_of_loopless M hloop v
  have hχ := circuitRank_erase_singleton_sub_general M hv
  rw [hcard,hi,hv3] at hχ
  omega

/-- A connected simple minimum-degree-three input cannot disappear under
one ordinary R step followed by removal of all bridges: a genuine
nonisolated core vertex remains. -/
theorem exists_positive_degree_after_ordinary_step (M : Molecule V D)
    (hloop : ∀ x, M.atom x ≠ M.atom (M.mate x))
    (hsimple : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1)
    (hbridge : ∀ e, ¬ IsBridge M e)
    (hconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b)
    (hmin : ∀ a ∈ M.atoms, 3 ≤ M.deg a)
    {v : V} (hv : v ∈ M.atoms) (hv3 : M.deg v = 3) :
    ∃ a ∈ (eraseAtoms M {v}).atoms, 0 < (bridgeCore (eraseAtoms M {v})).deg a := by
  have hχ := circuitRank_ge_three_of_simple_min_degree M hloop hsimple ⟨v,hv⟩ hmin hconn
  have hR := circuitRank_erase_three_of_bridgeless M hloop hbridge hv hv3
  have hB := (bridgeCore_bridgefree_and_circuitRank (eraseAtoms M {v})).2
  have hh : 0 < (bridgeCore (eraseAtoms M {v})).circuitRank := by omega
  exact exists_positive_degree_of_circuitRank_pos _ hh

/-- Selecting any actual core component after R strictly decreases the
old atom count. This is the well-founded measure of the source search. -/
theorem coreComponent_card_lt_after_removal (M : Molecule V D) {v : V}
    (hv : v ∈ M.atoms) (a : V) :
    (componentSet (bridgeCore (eraseAtoms M {v})) a).card < M.atoms.card := by
  have hs : componentSet (bridgeCore (eraseAtoms M {v})) a ⊆ M.atoms := by
    intro b hb
    exact (mem_sdiff.mp ((mem_componentSet _ _ _).mp hb).1).1
  have hvnot : v ∉ componentSet (bridgeCore (eraseAtoms M {v})) a := by
    intro hh
    exact (mem_sdiff.mp ((mem_componentSet _ _ _).mp hh).1).2 (mem_singleton_self v)
  apply card_lt_card
  exact Finset.ssubset_iff_subset_ne.mpr ⟨hs,fun he => hvnot (he.symm ▸ hv)⟩

/-- In a simple graph, deleting one other atom removes at most one dart
from a surviving star. -/
theorem degree_erase_singleton_add_one_ge (M : Molecule V D)
    (hsimple : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1)
    {a v : V} (hav : a ≠ v) :
    M.deg a ≤ (eraseAtoms M {v}).deg a + 1 := by
  have hr : removedDartsAt M {v} a = neighborDarts M a v := by
    ext x
    simp only [removedDartsAt,neighborDarts,mem_filter,mem_singleton]
  have he := deg_eraseAtoms_add_removed M {v} (by simpa only [mem_singleton] using hav)
  rw [hr,card_neighborDarts M hav] at he
  have hh := hsimple a v hav
  omega

/-- The temporary graph inspected in cases (1)--(3) has actual degrees
between two and four; this is derived from source simplicity and caps. -/
theorem degree_profile_after_removing_three (M : Molecule V D) (hM : M.IsMolecule)
    (hsimple : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1)
    (hmin : ∀ a ∈ M.atoms, 3 ≤ M.deg a) (v : V) :
    ∀ a ∈ (eraseAtoms M {v}).atoms, 2 ≤ (eraseAtoms M {v}).deg a ∧
      (eraseAtoms M {v}).deg a ≤ 4 := by
  intro a ha
  have ha' := mem_sdiff.mp ha
  have hav : a ≠ v := by simpa only [mem_singleton] using ha'.2
  have hlo := degree_erase_singleton_add_one_ge M hsimple hav
  have hmin' := hmin a ha'.1
  exact ⟨by omega,Mole.deg_le_four _ (isMolecule_eraseAtoms M hM {v}) ha⟩

/-- The literal local degree/bridge configurations in source cases (1)
and (3). Case (2), the newly enabled beta split, is separate. -/
def OrdinaryDegreeGood (M : Molecule V D) (a : V) : Prop :=
  ∃ B : Finset D, (∀ x, x ∈ B ↔ x ∈ M.dartsAt a ∧ IsBridge M x) ∧
    ((M.deg a = 2 ∧ B.card = 0) ∨ (M.deg a = 3 ∧ B.card = 1) ∨
      (M.deg a = 4 ∧ B.card = 2))

/-- The graph-only good predicate exposes its literal bridge counts. -/
theorem ordinaryDegreeGood_iff (M : Molecule V D) (a : V) [DecidablePred (IsBridge M)] :
    OrdinaryDegreeGood M a ↔
      (M.deg a = 2 ∧ ((M.dartsAt a).filter (IsBridge M)).card = 0) ∨
      (M.deg a = 3 ∧ ((M.dartsAt a).filter (IsBridge M)).card = 1) ∨
      (M.deg a = 4 ∧ ((M.dartsAt a).filter (IsBridge M)).card = 2) := by
  constructor
  · rintro ⟨B,hB,hcase⟩
    have hEq : B = (M.dartsAt a).filter (IsBridge M) := by
      ext x
      rw [mem_filter]
      exact hB x
    simpa only [hEq] using hcase
  · intro h
    exact ⟨(M.dartsAt a).filter (IsBridge M),fun _ => mem_filter,h⟩

/-- Excluding the literal local degree/bridge good configurations forces
the actual core profile; this is a derived search invariant. -/
theorem bridgeCore_profile_of_no_degree_good (M : Molecule V D)
    (hp : ∀ a ∈ M.atoms, 2 ≤ M.deg a ∧ M.deg a ≤ 4)
    (hno : ¬ ∃ a ∈ M.atoms, OrdinaryDegreeGood M a) :
    ∀ a ∈ M.atoms, (bridgeCore M).deg a = 0 ∨ (bridgeCore M).deg a = 3 ∨
      (bridgeCore M).deg a = 4 := by
  classical
  intro a ha
  apply bridgeCore_degree_profile M a (hp a ha).1 (hp a ha).2
  all_goals
    intro hd hb
    apply hno
    refine ⟨a,ha,(M.dartsAt a).filter (IsBridge M),?_,?_⟩
    · intro x
      exact mem_filter
    · first | exact Or.inl ⟨hd,hb⟩ | exact Or.inr (Or.inl ⟨hd,hb⟩) |
        exact Or.inr (Or.inr ⟨hd,hb⟩)

/-- Actual local exhaustion after R: either one of the degree/bridge good
configurations is present, or actual B pruning supplies a next degree-three
vertex in a strictly smaller old induced vertex set. No schedule is assumed. -/
theorem ordinary_step_degree_exhaustion (M : Molecule V D) (hM : M.IsMolecule)
    (hloop : ∀ x, M.atom x ≠ M.atom (M.mate x))
    (hsimple : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1)
    (hbridge : ∀ e, ¬ IsBridge M e)
    (hconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b)
    (hmin : ∀ a ∈ M.atoms, 3 ≤ M.deg a)
    {v : V} (hv : v ∈ M.atoms) (hv3 : M.deg v = 3) :
    (∃ a ∈ (eraseAtoms M {v}).atoms, OrdinaryDegreeGood (eraseAtoms M {v}) a) ∨
    ∃ a ∈ (eraseAtoms M {v}).atoms,
      (bridgeCore (eraseAtoms M {v})).deg a = 3 ∧
      (componentSet (bridgeCore (eraseAtoms M {v})) a).card < M.atoms.card := by
  classical
  let N := eraseAtoms M {v}
  by_cases hg : ∃ a ∈ N.atoms, OrdinaryDegreeGood N a
  · exact Or.inl hg
  right
  have hp : ∀ a ∈ N.atoms, (bridgeCore N).deg a = 0 ∨
      (bridgeCore N).deg a = 3 ∨ (bridgeCore N).deg a = 4 := by
    intro a ha
    have hprof := degree_profile_after_removing_three M hM hsimple hmin v a ha
    apply bridgeCore_degree_profile N a hprof.1 hprof.2
    all_goals
      intro hd hb
      apply hg
      refine ⟨a,ha,(N.dartsAt a).filter (IsBridge N),?_,?_⟩
      · intro x
        exact mem_filter
      · first | exact Or.inl ⟨hd,hb⟩ | exact Or.inr (Or.inl ⟨hd,hb⟩) |
          exact Or.inr (Or.inr ⟨hd,hb⟩)
  have hχ := circuitRank_ge_three_of_simple_min_degree M hloop hsimple ⟨v,hv⟩ hmin hconn
  have hR := circuitRank_erase_three_of_bridgeless M hloop hbridge hv hv3
  obtain ⟨a,ha,h3⟩ := exists_degree_three_after_bridge_pruning N
    (isMolecule_eraseAtoms M hM {v}) (by change 0 < (eraseAtoms M {v}).circuitRank; omega) hp
  exact ⟨a,ha,h3,coreComponent_card_lt_after_removal M hv a⟩

/-- The auxiliary source phase has a genuine one-circuit gain at every
actual degree-two atom of a bridgeless loopless graph. -/
theorem circuitRank_erase_two_of_bridgeless (M : Molecule V D)
    (hloop : ∀ x, M.atom x ≠ M.atom (M.mate x))
    (hbridge : ∀ e, ¬ IsBridge M e) {v : V}
    (hv : v ∈ M.atoms) (hv2 : M.deg v = 2) :
    (eraseAtoms M {v}).circuitRank = M.circuitRank - 1 := by
  have hlo := newComponents_card_pos_of_degree_pos M hloop hv (by omega)
  have hhi := card_newComponents_singleton_le_one M hbridge (by omega : M.deg v ≤ 3)
  have hcard : (newComponents M {v}).card = 1 := by omega
  have hi := incident_card_eq_deg_of_loopless M hloop v
  have hχ := circuitRank_erase_singleton_sub_general M hv
  rw [hcard,hi,hv2] at hχ
  omega

end WaveTurbulence.MoleProp
