/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineEmptyRungs
import Mathlib.Tactic

/-! # Empty double-pair propagation using only bonds and rail edges -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- A selected block atom with an external neighbor must be a joint. -/
theorem block_joint_of_external_neighbor (M : Molecule V D) (hM : M.IsMolecule)
    {A : Finset V} {a b x p : V} (hB : M.IsBlock A a b) (hx : x ∈ A)
    (hp : p ∉ A) (hAdj : M.Adj x p) : x=a ∨ x=b := by
  by_contra hh
  have hn : x ≠ a ∧ x ≠ b := not_or.mp hh
  have hd := hB.2.2.2.2.2.2.2.2.1 x hx hn.1 hn.2
  obtain ⟨d,hdx,hdp⟩ := hAdj
  have he := Mole.full_degree_no_exit M hM (hB.1 hx) hd hdx
  exact hp (hdp ▸ he)

/-- A double pair and a distinct external rail neighbor give three
external incidences, leaving at most one internal incidence. -/
theorem two_and_one_outside_degree_le_one (M : Molecule V D) (hM : M.IsMolecule)
    {A : Finset V} {x y p : V} (R : TwoIncidences M x y)
    (hy : y ∉ A) (hp : p ∉ A) (hne : p ≠ y) (hAdj : M.Adj x p) : M.degIn A x ≤ 1 := by
  obtain ⟨d,hdx,hdp⟩ := hAdj
  have hdnot : d ∉ univ.image R.dart := by
    intro hd
    obtain ⟨i,_hi,he⟩ := mem_image.mp hd
    have hh := R.neighbor_eq i
    rw [he] at hh
    exact hne (hdp.symm.trans hh)
  have hsub : insert d (univ.image R.dart) ⊆ outsideAt M A x := by
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact mem_filter.mpr ⟨(Mole.mem_dartsAt M x _).mpr hdx,fun hg => hp (hdp ▸ hg.2)⟩
    · obtain ⟨i,_hi,rfl⟩ := mem_image.mp hz
      exact mem_filter.mpr ⟨(Mole.mem_dartsAt M x _).mpr (R.atom_eq i),
        fun hg => hy (R.neighbor_eq i ▸ hg.2)⟩
  have hc := card_le_card hsub
  rw [card_insert_of_notMem hdnot,card_image_of_injective _ R.injective,
    card_univ,Fintype.card_fin] at hc
  have hsplit := outsideAt_card_add M A x
  have hxM : x ∈ M.atoms := R.atom_eq 0 ▸ M.atom_mem (R.dart 0)
  have hmax := Mole.deg_le_four M hM hxM
  omega

/-- Empty predecessor propagation needs only the double pair and its two
rail edges, rather than complete four-dart rows at the old core atoms. -/
theorem block_empty_double_pair (M : Molecule V D) (hM : M.IsMolecule)
    {A : Finset V} {a b x y p q : V} (hB : M.IsBlock A a b)
    (hC : GroupConnected M A) (hcard : 2<A.card) (R : TwoIncidences M x y)
    (hne : x ≠ y) (hp : p ∉ A) (hq : q ∉ A) (hpy : p ≠ y) (hqx : q ≠ x)
    (hxp : M.Adj x p) (hyq : M.Adj y q) : x ∉ A ∧ y ∉ A := by
  have hxnot : x ∉ A := by
    intro hx
    have hy : y ∈ A := by
      by_contra hy
      have hd := two_and_one_outside_degree_le_one M hM R hy hp hpy hxp
      have hmin := block_degree_ge_two M hB hx
      omega
    have hxj := block_joint_of_external_neighbor M hM hB hx hp hxp
    have hyj := block_joint_of_external_neighbor M hM hB hy hq hyq
    have he : A={x,y} := by
      rcases hxj with rfl | rfl <;> rcases hyj with rfl | rfl
      · exact False.elim (hne rfl)
      · exact connected_block_eq_double_pair M hB hC R
      · simpa only [pair_comm] using connected_block_eq_double_pair M hB hC R.mates
      · exact False.elim (hne rfl)
    have hc := congrArg Finset.card he
    rw [card_pair hne] at hc
    omega
  refine ⟨hxnot,?_⟩
  intro hy
  have hd := two_and_one_outside_degree_le_one M hM R.mates hxnot hq hqx hyq
  have hmin := block_degree_ge_two M hB hy
  omega

end WaveTurbulence.Vine
