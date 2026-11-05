/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRemoval
public import WaveTurbulence.Foundations.Molecule.VineChainCounts
public import WaveTurbulence.Foundations.Molecule.VineEmptyRungs
import Mathlib.Tactic

/-! # Single rail bonds survive simultaneous type-I removals -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [DecidableEq D] [Fintype D]

omit [DecidableEq D] in
/-- Type-I pieces have no nonjoint atoms, so any family of their removals
retains the whole ambient atom set. -/
theorem remainingAtoms_eq_of_typeI (M : Molecule V D) (S : Finset V)
    (ps : List (RemovalPiece V D))
    (hI : ∀ P ∈ ps,M.IsVine .I P.atoms P.left P.right) : remainingAtoms S ps=S := by
  apply filter_eq_self.mpr
  intro v _hv P hP
  have hat := typeI_atoms (hI P hP)
  simp [RemovalPiece.interior,hat]

omit [DecidableEq D] in
/-- A genuine single bond cannot have both endpoints in a type-I vine. -/
theorem single_pair_not_in_typeI (M : Molecule V D) {A : Finset V} {a b u v : V}
    (hI : M.IsVine .I A a b) (hu : u ∈ A) (hv : v ∈ A) (huv : u ≠ v)
    (hd : M.degIn {u,v} u=1) : False := by
  have he : ({u,v} : Finset V)=A := by
    apply eq_of_subset_of_card_le
    · intro w hw
      rcases mem_insert.mp hw with hw | hw
      · exact hw.symm ▸ hu
      · exact (mem_singleton.mp hw).symm ▸ hv
    · rw [typeI_atoms hI,card_pair hI.1.2.2.2.1,card_pair huv]
  have hlo := block_degree_ge_two M hI.1 hu
  rw [← he,hd] at hlo
  omega

omit [DecidableEq D] in
/-- A single actual rail dart survives any family of complete double-bond
removals. This is a local removal helper; source applications must supply
the template's single-rail degree calculation and connecting paths. -/
theorem keepDart_of_typeI_removals_single_pair (M : Molecule V D) (S : Finset V)
    (ps : List (RemovalPiece V D))
    (hI : ∀ P ∈ ps,M.IsVine .I P.atoms P.left P.right)
    (hD : ∀ P ∈ ps,P.darts=univ.filter (M.InGroup P.atoms))
    (d : D) (hu : M.atom d ∈ S) (hv : M.atom (M.mate d) ∈ S)
    (hne : M.atom d ≠ M.atom (M.mate d))
    (hd : M.degIn {M.atom d,M.atom (M.mate d)} (M.atom d)=1) : KeepDart M S ps d := by
  have hr := remainingAtoms_eq_of_typeI M S ps hI
  refine ⟨hr.symm ▸ hu,hr.symm ▸ hv,?_⟩
  intro P hP
  have hnot : ¬M.InGroup P.atoms d := by
    intro hin
    exact single_pair_not_in_typeI M (hI P hP) hin.1 hin.2 hne hd
  constructor
  · rw [hD P hP]
    simpa only [mem_filter,mem_univ,true_and] using hnot
  · rw [hD P hP]
    intro hm
    have hh := (mem_filter.mp hm).2
    apply hnot
    exact ⟨by simpa only [M.mate_mate] using hh.2,hh.1⟩

omit [DecidableEq D] in
/-- Type-I pieces cannot contain three distinct atoms. -/
theorem typeI_not_three_atoms (M : Molecule V D) {A : Finset V} {a b u v w : V}
    (hI : M.IsVine .I A a b) (hu : u ∈ A) (hv : v ∈ A) (hw : w ∈ A)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) : False := by
  have hat := typeI_atoms hI
  have hc : A.card=2 := by rw [hat,card_pair hI.1.2.2.2.1]
  have hs : ({u,v,w} : Finset V) ⊆ A := by
    intro z hz
    simp only [mem_insert,mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact hu
    · exact hv
    · exact hw
  have hle := card_le_card hs
  have hcard : ({u,v,w} : Finset V).card=3 := by simp [huv,huw,hvw]
  omega

omit [DecidableEq D] in
/-- Among two distinct neighbors of an atom, a disjoint family of type-I
pieces cannot contain both incident edges. This supplies a surviving
attachment for a normal vine's center outside its single-bond backbone. -/
theorem typeI_family_keeps_one_neighbor (M : Molecule V D)
    (ps : List (RemovalPiece V D))
    (hI : ∀ P ∈ ps,M.IsVine .I P.atoms P.left P.right)
    (hdis : ∀ P ∈ ps,∀ Q ∈ ps,P ≠ Q → Disjoint P.atoms Q.atoms)
    {u v w : V} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    (∀ P ∈ ps,¬(u ∈ P.atoms ∧ v ∈ P.atoms)) ∨
      (∀ P ∈ ps,¬(u ∈ P.atoms ∧ w ∈ P.atoms)) := by
  classical
  by_cases hfirst : ∀ P ∈ ps,¬(u ∈ P.atoms ∧ v ∈ P.atoms)
  · exact Or.inl hfirst
  · push Not at hfirst
    obtain ⟨P,hP,hu,hv⟩ := hfirst
    apply Or.inr
    intro Q hQ hQmem
    have he : P=Q := by
      by_contra hne
      exact (disjoint_left.mp (hdis P hP Q hQ hne)) hu hQmem.1
    subst Q
    exact typeI_not_three_atoms M (hI P hP) hu hv hQmem.2 huv huw hvw

/-- A source subgroup edge whose two-atom induced degree is one. -/
@[expose] def SingleGroupAdj (M : Molecule V D) (S : Finset V) (u v : V) : Prop :=
  u ∈ S ∧ v ∈ S ∧ u ≠ v ∧ M.Adj u v ∧ M.degIn {u,v} u=1

omit [DecidableEq D] in
/-- Every path along actual single bonds survives arbitrary complete
removals of type-I vines. This transfers a literal backbone certificate
without requiring additional hypotheses on the surviving graph. -/
theorem typeI_removal_single_path (M : Molecule V D) (S : Finset V)
    (ps : List (RemovalPiece V D))
    (hI : ∀ P ∈ ps,M.IsVine .I P.atoms P.left P.right)
    (hD : ∀ P ∈ ps,P.darts=univ.filter (M.InGroup P.atoms))
    {u v : V} (hp : Relation.EqvGen (SingleGroupAdj M S) u v) :
    (removeBlocks M S ps).SameComponent u v := by
  induction hp with
  | rel u v huv =>
    obtain ⟨hu,hv,hne,⟨d,hdu,hdv⟩,hd⟩ := huv
    have hk := keepDart_of_typeI_removals_single_pair M S ps hI hD d
      (hdu.symm ▸ hu) (hdv.symm ▸ hv) (by simpa only [hdu,hdv] using hne)
      (by simpa only [hdu,hdv] using hd)
    exact Relation.EqvGen.rel _ _ ⟨⟨d,hk⟩,hdu,hdv⟩
  | refl u => exact Relation.EqvGen.refl _
  | symm u v _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans u v w _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

end WaveTurbulence.Vine
