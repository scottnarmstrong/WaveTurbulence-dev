/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.CellDeletionGeometry
public import WaveTurbulence.Foundations.FinalCount.MoleProp.GeneralCircuitDeletion
import Mathlib.Tactic

/-! # Actual circuit changes for removing a double-rung pair -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Relabeling the actual dart carrier preserves the actual circuit rank. -/
theorem numComponents_and_circuitRank_eq_of_dart_equiv {E : Type*} [Fintype E] [DecidableEq E]
    (M : Molecule V D) (N : Molecule V E) (f : D ≃ E)
    (hA : M.atoms = N.atoms) (ha : ∀ x, N.atom (f x) = M.atom x)
    (hm : ∀ x, N.mate (f x) = f (M.mate x)) (ho : ∀ x, N.out (f x) = M.out x) :
    M.numComponents = N.numComponents ∧ M.circuitRank = N.circuitRank := by
  classical
  have hE : M.bonds.card = N.bonds.card := by
    apply card_bij (fun x _ => f x)
    · intro x hx
      exact mem_filter.mpr ⟨mem_univ _,(ho x).trans (mem_filter.mp hx).2⟩
    · intro x _ y _ h
      exact f.injective h
    · intro y hy
      refine ⟨f.symm y,?_,f.apply_symm_apply y⟩
      apply mem_filter.mpr
      refine ⟨mem_univ _,?_⟩
      have hh := ho (f.symm y)
      rw [f.apply_symm_apply] at hh
      exact hh.symm.trans (mem_filter.mp hy).2
  have hAdj (a b : V) : M.Adj a b ↔ N.Adj a b := by
    constructor
    · rintro ⟨x,hx,hxm⟩
      refine ⟨f x,(ha x).trans hx,?_⟩
      rw [hm,ha]
      exact hxm
    · rintro ⟨y,hy,hym⟩
      obtain ⟨x,rfl⟩ := f.surjective y
      refine ⟨x,(ha x).symm.trans hy,?_⟩
      rw [hm,ha] at hym
      exact hym
  have hSame (a b : V) : M.SameComponent a b ↔ N.SameComponent a b :=
    ⟨fun h => Relation.EqvGen.mono (fun a b h => (hAdj a b).mp h) a b h,
      fun h => Relation.EqvGen.mono (fun a b h => (hAdj a b).mpr h) a b h⟩
  have hset : componentSet M = componentSet N := by
    funext a
    ext b
    simp only [mem_componentSet,hA,hSame]
  have hF : M.numComponents = N.numComponents := by
    rw [numComponents_eq_card_componentSets,numComponents_eq_card_componentSets]
    unfold componentSets
    rw [hA,hset]
  refine ⟨hF,?_⟩
  unfold Molecule.circuitRank
  rw [hE,hA,hF]

theorem circuitRank_eq_of_dart_equiv {E : Type*} [Fintype E] [DecidableEq E]
    (M : Molecule V D) (N : Molecule V E) (f : D ≃ E)
    (hA : M.atoms = N.atoms) (ha : ∀ x, N.atom (f x) = M.atom x)
    (hm : ∀ x, N.mate (f x) = f (M.mate x)) (ho : ∀ x, N.out (f x) = M.out x) :
    M.circuitRank = N.circuitRank :=
  (numComponents_and_circuitRank_eq_of_dart_equiv M N f hA ha hm ho).2

/-- Flattening two successive retained-dart subtypes is the literal
retained-dart carrier for erasing the union of the two atom sets. -/
def eraseDartUnionEquiv (M : Molecule V D) (Y Z : Finset V) :
    RetainedDart (eraseAtoms M Y) Z ≃ RetainedDart M (Y ∪ Z) where
  toFun x := ⟨x.val.val,by
    constructor
    · intro h
      rcases mem_union.mp h with h | h
      · exact x.val.property.1 h
      · exact x.property.1 h
    · intro h
      rcases mem_union.mp h with h | h
      · exact x.val.property.2 h
      · exact x.property.2 h⟩
  invFun x := ⟨⟨x.val,fun h => x.property.1 (mem_union_left _ h),
      fun h => x.property.2 (mem_union_left _ h)⟩,
    fun h => x.property.1 (mem_union_right _ h),fun h => x.property.2 (mem_union_right _ h)⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv x := Subtype.ext rfl

theorem circuitRank_erase_erase_eq_union (M : Molecule V D) (Y Z : Finset V) :
    (eraseAtoms (eraseAtoms M Y) Z).circuitRank = (eraseAtoms M (Y ∪ Z)).circuitRank := by
  apply circuitRank_eq_of_dart_equiv _ _ (eraseDartUnionEquiv M Y Z)
  · ext a
    change (a ∈ (M.atoms \ Y) \ Z) ↔ a ∈ M.atoms \ (Y ∪ Z)
    simp only [mem_sdiff,mem_union,not_or]
    tauto
  · intro x; rfl
  · intro x; exact Subtype.ext rfl
  · intro x; rfl

theorem circuitRank_erase_erase_singleton_eq (M : Molecule V D) (a b : V) :
    (eraseAtoms (eraseAtoms M {a}) {b}).circuitRank = (eraseAtoms M {a,b}).circuitRank := by
  have hU : ({a} : Finset V) ∪ {b} = {a,b} := by ext x; simp only [mem_union,mem_singleton,mem_insert]
  have hh := circuitRank_erase_erase_eq_union M {a} {b}
  rw [hU] at hh
  exact hh

private theorem selfBondsAt_eq_empty_of_loopless (M : Molecule V D)
    (hloop : ∀ x, M.atom x ≠ M.atom (M.mate x)) (v : V) : selfBondsAt M v = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hx,hy⟩ := mem_inter.mp hx
  have hxv := (mem_filter.mp hx).2
  have hyv := (mem_filter.mp hy).2
  exact hloop x (hxv.trans hyv.symm)

theorem incident_card_eq_deg_of_loopless (M : Molecule V D)
    (hloop : ∀ x, M.atom x ≠ M.atom (M.mate x)) (v : V) : (incidentBondsAt M v).card = M.deg v := by
  have h := card_incident_add_self_eq_deg M v
  simpa only [selfBondsAt_eq_empty_of_loopless M hloop,card_empty,Nat.add_zero] using h

theorem newComponents_card_pos_of_degree_pos (M : Molecule V D)
    (hloop : ∀ x, M.atom x ≠ M.atom (M.mate x)) {v : V} (hv : v ∈ M.atoms)
    (hdeg : 0 < M.deg v) : 0 < (newComponents M {v}).card := by
  change 0 < (M.dartsAt v).card at hdeg
  obtain ⟨x,hx⟩ := card_pos.mp hdeg
  have hxv := (Mole.mem_dartsAt M v x).mp hx
  have hne : M.atom (M.mate x) ≠ v := by intro h; exact hloop x (hxv.trans h.symm)
  have hp : M.SameComponent (M.atom (M.mate x)) v :=
    Relation.EqvGen.rel _ _ ⟨M.mate x,rfl,by rw [M.mate_mate]; exact hxv⟩
  exact card_pos.mpr ⟨_,residualComponent_mem_newComponents_of_sameComponent M hv (M.atom_mem _) hne hp⟩

theorem circuitRank_erase_degree_one_eq (M : Molecule V D)
    (hloop : ∀ x, M.atom x ≠ M.atom (M.mate x)) {v : V} (hv : v ∈ M.atoms)
    (hdeg : M.deg v = 1) : (eraseAtoms M {v}).circuitRank = M.circuitRank := by
  have hp := newComponents_card_pos_of_degree_pos M hloop hv (by omega)
  have hc := card_newComponents_le_boundary M {v}
  have hb := boundary_singleton_card_le_degree M v
  have hi := incident_card_eq_deg_of_loopless M hloop v
  have hr := circuitRank_erase_singleton_sub_general M hv
  omega

theorem circuitRank_erase_degree_two_cases (M : Molecule V D)
    (hloop : ∀ x, M.atom x ≠ M.atom (M.mate x)) {v : V} (hv : v ∈ M.atoms)
    (hdeg : M.deg v = 2) :
    (eraseAtoms M {v}).circuitRank = M.circuitRank ∨ (eraseAtoms M {v}).circuitRank = M.circuitRank - 1 := by
  have hp := newComponents_card_pos_of_degree_pos M hloop hv (by omega)
  have hc := card_newComponents_le_boundary M {v}
  have hb := boundary_singleton_card_le_degree M v
  have hi := incident_card_eq_deg_of_loopless M hloop v
  have hr := circuitRank_erase_singleton_sub_general M hv
  omega

/-- The actual local neighbor-detour rank bound also holds in disconnected molecules. -/
theorem circuitRank_drop_of_neighbor_detour_general (M : Molecule V D)
    {v a b : V} (hv : v ∈ M.atoms) (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hdouble : 2 ≤ M.bondsBetween v a) (hsingle : 1 ≤ M.bondsBetween v b)
    (hpath : Relation.EqvGen (ResidualAdj M {v}) a b) :
    (eraseAtoms M {v}).circuitRank ≤ M.circuitRank - 2 := by
  classical
  let A := neighborDarts M v a
  let B := neighborDarts M v b
  have hA : 2 ≤ A.card := by dsimp only [A]; rwa [card_neighborDarts M hva]
  have hB : 1 ≤ B.card := by dsimp only [B]; rwa [card_neighborDarts M hvb]
  have hdis : Disjoint A B := by
    apply disjoint_left.mpr
    intro x hx hy
    have hx' := (mem_neighborDarts M v a x).mp hx
    have hy' := (mem_neighborDarts M v b x).mp hy
    exact hab (hx'.2.symm.trans hy'.2)
  obtain ⟨xA,hxA⟩ := card_pos.mp (by omega : 0 < A.card)
  obtain ⟨xB,hxB⟩ := card_pos.mp (by omega : 0 < B.card)
  have hxA' := (mem_neighborDarts M v a xA).mp hxA
  have hxB' := (mem_neighborDarts M v b xB).mp hxB
  have haM : a ∈ M.atoms := hxA'.2 ▸ M.atom_mem (M.mate xA)
  have hbM : b ∈ M.atoms := hxB'.2 ▸ M.atom_mem (M.mate xB)
  let S := residualComponent M {v} a
  have haS : a ∈ S := (mem_residualComponent M {v} a a).mpr
    ⟨haM, by simpa only [mem_singleton] using hva.symm, Relation.EqvGen.refl a⟩
  have hbS : b ∈ S := (mem_residualComponent M {v} a b).mpr
    ⟨hbM, by simpa only [mem_singleton] using hvb.symm, hpath⟩
  have hvS : v ∉ S := by
    intro hh
    exact ((mem_residualComponent M {v} a v).mp hh).2.1 (mem_singleton_self v)
  have hsub : (A ∪ B).image M.mate ⊆ boundaryDarts M S := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    have hyv : M.atom y = v ∧ (M.atom (M.mate y) = a ∨ M.atom (M.mate y) = b) := by
      rcases mem_union.mp hy with hy | hy
      · have hh := (mem_neighborDarts M v a y).mp hy
        exact ⟨hh.1, Or.inl hh.2⟩
      · have hh := (mem_neighborDarts M v b y).mp hy
        exact ⟨hh.1, Or.inr hh.2⟩
    simp only [boundaryDarts, mem_filter, mem_univ, true_and, M.mate_mate, hyv.1]
    constructor
    · rcases hyv.2 with hya | hyb
      · exact hya.symm ▸ haS
      · exact hyb.symm ▸ hbS
    · exact hvS
  have hthree : 3 ≤ (boundaryDarts M S).card := by
    have hc := card_le_card hsub
    rw [card_image_of_injective _ (Mole.mate_injective M), card_union_of_disjoint hdis] at hc
    omega
  have hSC : S ∈ newComponents M {v} := by
    apply mem_filter.mpr
    constructor
    · exact mem_image.mpr ⟨a, mem_sdiff.mpr ⟨haM, by simpa only [mem_singleton] using hva.symm⟩, rfl⟩
    · exact card_pos.mp (by omega)
  have hc := card_newComponents_add_two_le_of_large_boundary M {v} S hSC hthree
  have hb := card_boundary_add_twice_self_eq_deg M v
  have hi := card_incident_add_self_eq_deg M v
  have hd := circuitRank_erase_singleton_sub_general M hv
  omega


private theorem doublePair_cell_start_at (M : Molecule V D) {S : Finset V}
    (hS : IsLadderCell M S) {a : V} (ha : a ∈ S) :
    ∃ u v : Fin 2 → V, SourceLadder M u v ∧ Molecule.ladderAtoms u v = S ∧ u 0 = a := by
  obtain ⟨u,v,hL,rfl⟩ := hS
  rcases mem_union.mp ha with ha | ha
  · obtain ⟨j,_,rfl⟩ := mem_image.mp ha
    fin_cases j
    · exact ⟨u,v,hL,rfl,rfl⟩
    · exact ⟨fun i => u i.rev,fun i => v i.rev,sourceLadder_reverse M hL,
        ladderAtoms_reverse u v,rfl⟩
  · obtain ⟨j,_,rfl⟩ := mem_image.mp ha
    fin_cases j
    · exact ⟨v,u,sourceLadder_swap M hL,ladderAtoms_swap u v,rfl⟩
    · refine ⟨fun i => v i.rev,fun i => u i.rev,sourceLadder_reverse M (sourceLadder_swap M hL),?_,rfl⟩
      rw [ladderAtoms_reverse,ladderAtoms_swap]

/-- A cell meeting the actual double pair supplies a surviving detour
from its partner to the degree-three endpoint's external rail neighbor. -/
theorem exists_double_pair_rail_detour (M : Molecule V D) (hM : M.IsMolecule)
    {a b : V} (hab : a ≠ b) (hdouble : M.bondsBetween a b = 2)
    {S : Finset V} (hS : IsLadderCell M S) (hmeet : ¬ Disjoint S {a,b}) :
    ∃ c, a ∈ M.atoms ∧ a ≠ c ∧ b ≠ c ∧ M.bondsBetween a c = 1 ∧
      Relation.EqvGen (ResidualAdj M {a}) b c := by
  classical
  have haS : a ∈ S := by
    by_contra ha
    exact hmeet ((cell_disjoint_double_pair_iff M hM hab hdouble hS).mpr ha)
  obtain ⟨u,v,hL,_hUS,hu0⟩ := doublePair_cell_start_at M hS haS
  obtain ⟨hu,hv,huv⟩ := Sum.elim_injective.mp hL.2.1
  have hb : b = v 0 := sourceLadder_double_partner_eq M
    (fun z hz => Mole.deg_le_four M hM hz) hL 0 (by rw [hu0]; exact hab)
    (by rw [hu0]; exact hdouble)
  subst b
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have haC : a ≠ u 1 := by rw [← hu0]; exact hu.ne h01
  have haD : a ≠ v 1 := by rw [← hu0]; exact huv 0 1
  have h1 : ResidualAdj M {a} (v 0) (v 1) :=
    ⟨by simpa only [mem_singleton] using hab.symm,
      by simpa only [mem_singleton] using haD.symm,
      adj_of_bondsBetween_pos M (hv.ne h01) (by have h := (hL.2.2.2.2 0).2.1; change M.bondsBetween (v 0) (v 1) = 1 at h; omega)⟩
  have h2 : ResidualAdj M {a} (v 1) (u 1) :=
    ⟨by simpa only [mem_singleton] using haD.symm,
      by simpa only [mem_singleton] using haC.symm,
      Mole.adj_symmetric M (adj_of_bondsBetween_pos M (huv 1 1) (by have h := hL.2.2.2.1 1; omega))⟩
  refine ⟨u 1,?_,haC,(huv 1 0).symm,?_,
    Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ h1) (Relation.EqvGen.rel _ _ h2)⟩
  · rw [← hu0]
    exact (hL.2.2.1 0).1
  · rw [← hu0]
    exact (hL.2.2.2.2 0).1

/-- The first atom in an affected operation-(b) cell loses exactly two
circuits, even when unrelated old components are present. -/
theorem circuitRank_erase_first_double_cell_eq (M : Molecule V D) (hM : M.IsMolecule)
    (hloop : ∀ x, M.atom x ≠ M.atom (M.mate x))
    {a b : V} (hab : a ≠ b) (hdeg : M.deg a = 3) (hdouble : M.bondsBetween a b = 2)
    {S : Finset V} (hS : IsLadderCell M S) (hmeet : ¬ Disjoint S {a,b}) :
    (eraseAtoms M {a}).circuitRank = M.circuitRank - 2 := by
  obtain ⟨c,ha,hac,hbc,hrail,hpath⟩ := exists_double_pair_rail_detour M hM hab hdouble hS hmeet
  have hdrop := circuitRank_drop_of_neighbor_detour_general M ha hab hac hbc
    (by omega) (by omega) hpath
  have hp := newComponents_card_pos_of_degree_pos M hloop ha (by omega)
  have hi := incident_card_eq_deg_of_loopless M hloop a
  have hr := circuitRank_erase_singleton_sub_general M ha
  omega

/-- Erasing one endpoint of a double bond removes exactly two darts at
its surviving partner, with no orientation assumption. -/
theorem degree_erase_double_endpoint (M : Molecule V D) {a b : V}
    (hab : a ≠ b) (hdouble : M.bondsBetween a b = 2) :
    (eraseAtoms M {a}).deg b + 2 = M.deg b := by
  have hb : b ∉ ({a} : Finset V) := by simpa only [mem_singleton] using hab.symm
  have hd := deg_eraseAtoms_add_removed M {a} hb
  have he : removedDartsAt M {a} b = neighborDarts M b a := by
    ext x
    simp only [removedDartsAt,neighborDarts,mem_filter,mem_singleton]
  rw [he,card_neighborDarts M hab.symm,bondsBetween_comm,hdouble] at hd
  exact hd

private theorem double_neighbor_mem (M : Molecule V D) {a b : V}
    (hab : a ≠ b) (hdouble : M.bondsBetween a b = 2) : a ∈ M.atoms ∧ b ∈ M.atoms := by
  obtain ⟨x,hxa,hxb⟩ := adj_of_bondsBetween_pos M hab (by omega)
  exact ⟨hxa ▸ M.atom_mem x,hxb ▸ M.atom_mem (M.mate x)⟩

/-- Both degree-three endpoints in an affected source cell lose exactly
two circuits upon actual simultaneous pair deletion. -/
theorem circuitRank_erase_double_cell_three_three_eq (M : Molecule V D) (hM : M.IsMolecule)
    (hloop : ∀ x, M.atom x ≠ M.atom (M.mate x))
    {a b : V} (hab : a ≠ b) (ha3 : M.deg a = 3) (hb3 : M.deg b = 3)
    (hdouble : M.bondsBetween a b = 2) {S : Finset V}
    (hS : IsLadderCell M S) (hmeet : ¬ Disjoint S {a,b}) :
    (eraseAtoms M {a,b}).circuitRank = M.circuitRank - 2 := by
  have hfirst := circuitRank_erase_first_double_cell_eq M hM hloop hab ha3 hdouble hS hmeet
  have hd := degree_erase_double_endpoint M hab hdouble
  have hdeg : (eraseAtoms M {a}).deg b = 1 := by omega
  have hbm : b ∈ (eraseAtoms M {a}).atoms :=
    mem_sdiff.mpr ⟨(double_neighbor_mem M hab hdouble).2,by simpa only [mem_singleton] using hab.symm⟩
  have hloop' : ∀ x : RetainedDart M {a}, (eraseAtoms M {a}).atom x ≠
      (eraseAtoms M {a}).atom ((eraseAtoms M {a}).mate x) := fun x => hloop x.val
  have hsecond := circuitRank_erase_degree_one_eq (eraseAtoms M {a}) hloop' hbm hdeg
  rw [circuitRank_erase_erase_singleton_eq] at hsecond
  omega

/-- A degree-three/four double pair in an affected source cell loses two
or three circuits, for the literal simultaneous atom erasure. -/
theorem circuitRank_erase_double_cell_three_four_cases (M : Molecule V D) (hM : M.IsMolecule)
    (hloop : ∀ x, M.atom x ≠ M.atom (M.mate x))
    {a b : V} (hab : a ≠ b) (ha3 : M.deg a = 3) (hb4 : M.deg b = 4)
    (hdouble : M.bondsBetween a b = 2) {S : Finset V}
    (hS : IsLadderCell M S) (hmeet : ¬ Disjoint S {a,b}) :
    (eraseAtoms M {a,b}).circuitRank = M.circuitRank - 2 ∨
      (eraseAtoms M {a,b}).circuitRank = M.circuitRank - 3 := by
  have hfirst := circuitRank_erase_first_double_cell_eq M hM hloop hab ha3 hdouble hS hmeet
  have hd := degree_erase_double_endpoint M hab hdouble
  have hdeg : (eraseAtoms M {a}).deg b = 2 := by omega
  have hbm : b ∈ (eraseAtoms M {a}).atoms :=
    mem_sdiff.mpr ⟨(double_neighbor_mem M hab hdouble).2,by simpa only [mem_singleton] using hab.symm⟩
  have hloop' : ∀ x : RetainedDart M {a}, (eraseAtoms M {a}).atom x ≠
      (eraseAtoms M {a}).atom ((eraseAtoms M {a}).mate x) := fun x => hloop x.val
  have hsecond := circuitRank_erase_degree_two_cases (eraseAtoms M {a}) hloop' hbm hdeg
  rw [circuitRank_erase_erase_singleton_eq] at hsecond
  omega


/-- A cell meeting an actual double pair has a genuine rung enumeration
whose first upper and lower atoms are exactly those two removed atoms. -/
theorem exists_double_cell_rung_representation (M : Molecule V D) (hM : M.IsMolecule)
    {a b : V} (hab : a ≠ b) (hdouble : M.bondsBetween a b = 2)
    {S : Finset V} (hS : IsLadderCell M S) (hmeet : ¬ Disjoint S {a,b}) :
    ∃ u v : Fin 2 → V, SourceLadder M u v ∧ Molecule.ladderAtoms u v = S ∧ u 0 = a ∧ v 0 = b := by
  classical
  have haS : a ∈ S := by
    by_contra ha
    exact hmeet ((cell_disjoint_double_pair_iff M hM hab hdouble hS).mpr ha)
  obtain ⟨u,v,hL,hUS,hu0⟩ := doublePair_cell_start_at M hS haS
  have hb : b = v 0 := sourceLadder_double_partner_eq M
    (fun z hz => Mole.deg_le_four M hM hz) hL 0 (by rw [hu0]; exact hab)
    (by rw [hu0]; exact hdouble)
  exact ⟨u,v,hL,hUS,hu0,hb.symm⟩

end WaveTurbulence.MoleProp
