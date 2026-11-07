/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103BridgeComponents
import Mathlib.Tactic

/-! # The three actual components after deleting two incident bridges -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Two actual B operations, with their actual nested surviving dart type. -/
def eraseTwoBonds (M : Molecule V D) (e f : D) (hf : f ≠ e ∧ f ≠ M.mate e) :
    Molecule V (WithoutBondDart (eraseBond M e) ⟨f,hf⟩) :=
  eraseBond (eraseBond M e) ⟨f,hf⟩

private theorem eraseBond_path_lift (M : Molecule V D) (e : D) {a b : V}
    (hp : (eraseBond M e).SameComponent a b) : M.SameComponent a b :=
  Relation.EqvGen.mono (fun _ _ ⟨z,hza,hzb⟩ => ⟨z.val,hza,hzb⟩) a b hp

/-- The joint and the two far endpoints lie in three distinct actual
components after both B operations. -/
theorem eraseTwoBonds_three_separated (M : Molecule V D) {e f : D}
    (hf : f ≠ e ∧ f ≠ M.mate e) (heB : IsBridge M e) (hfB : IsBridge M f)
    (hatom : M.atom f = M.atom e) :
    let P := eraseTwoBonds M e f hf
    ¬ P.SameComponent (M.atom e) (M.atom (M.mate e)) ∧
    ¬ P.SameComponent (M.atom e) (M.atom (M.mate f)) ∧
    ¬ P.SameComponent (M.atom (M.mate e)) (M.atom (M.mate f)) := by
  let N := eraseBond M e
  let f' : WithoutBondDart M e := ⟨f,hf⟩
  let P := eraseTwoBonds M e f hf
  have hfB' : IsBridge N f' := (isBridge_eraseBond_iff M e heB f').mpr hfB
  have hnot : ¬ N.SameComponent (M.atom e) (M.atom (M.mate e)) :=
    fun hp => heB ((eraseBond_sameComponent_iff M e _ _).mp hp)
  refine ⟨?_,?_,?_⟩
  · intro hp
    exact hnot (eraseBond_path_lift N f' hp)
  · intro hp
    apply hfB'
    apply (eraseBond_sameComponent_iff N f' _ _).mp
    change P.SameComponent (M.atom f) (M.atom (M.mate f))
    rw [hatom]
    exact hp
  · intro hp
    have hpath := eraseBond_path_lift N f' hp
    have hedge : N.SameComponent (M.atom e) (M.atom (M.mate f)) :=
      Relation.EqvGen.rel _ _ ⟨f',hatom,rfl⟩
    exact hnot (Relation.EqvGen.trans _ _ _ hedge (Relation.EqvGen.symm _ _ hpath))

/-- In a connected graph these three actual components exhaust the result.
The cardinal is derived by two genuine bridge component increments. -/
theorem componentSets_eraseTwoBonds_eq_three (M : Molecule V D) {e f : D}
    (hf : f ≠ e ∧ f ≠ M.mate e) (heB : IsBridge M e) (hfB : IsBridge M f)
    (hatom : M.atom f = M.atom e)
    (hconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) :
    let P := eraseTwoBonds M e f hf
    componentSets P = {componentSet P (M.atom e),componentSet P (M.atom (M.mate e)),
      componentSet P (M.atom (M.mate f))} := by
  classical
  let N := eraseBond M e
  let f' : WithoutBondDart M e := ⟨f,hf⟩
  let P := eraseTwoBonds M e f hf
  have hF := Mole.numComponents_eq_one M ⟨M.atom e,M.atom_mem e⟩ hconn
  have hF1 := numComponents_eraseBond_eq_add_one M e heB
  have hfB' := (isBridge_eraseBond_iff M e heB f').mpr hfB
  have hF2 := numComponents_eraseBond_eq_add_one N f' hfB'
  change N.numComponents = M.numComponents + 1 at hF1
  change P.numComponents = N.numComponents + 1 at hF2
  have hF3 : P.numComponents = 3 := by omega
  have hc : (componentSets P).card = 3 := by rw [← numComponents_eq_card_componentSets]; exact hF3
  have hsep := eraseTwoBonds_three_separated M hf heB hfB hatom
  have hb : M.atom e ∈ P.atoms := M.atom_mem e
  have hu : M.atom (M.mate e) ∈ P.atoms := M.atom_mem _
  have hw : M.atom (M.mate f) ∈ P.atoms := M.atom_mem _
  have h01 : componentSet P (M.atom e) ≠ componentSet P (M.atom (M.mate e)) :=
    fun h => hsep.1 ((componentSet_eq_iff P hb).mp h)
  have h02 : componentSet P (M.atom e) ≠ componentSet P (M.atom (M.mate f)) :=
    fun h => hsep.2.1 ((componentSet_eq_iff P hb).mp h)
  have h12 : componentSet P (M.atom (M.mate e)) ≠ componentSet P (M.atom (M.mate f)) :=
    fun h => hsep.2.2 ((componentSet_eq_iff P hu).mp h)
  have hsub : {componentSet P (M.atom e),componentSet P (M.atom (M.mate e)),componentSet P (M.atom (M.mate f))} ⊆
      componentSets P := by
    simp only [insert_subset_iff,singleton_subset_iff]
    exact ⟨mem_image.mpr ⟨_,hb,rfl⟩,mem_image.mpr ⟨_,hu,rfl⟩,mem_image.mpr ⟨_,hw,rfl⟩⟩
  change componentSets P = {componentSet P (M.atom e),componentSet P (M.atom (M.mate e)),
    componentSet P (M.atom (M.mate f))}
  symm
  apply Finset.eq_of_subset_of_card_le hsub
  rw [hc]
  simp [h01,h02,h12]

/-- An actual component of the twice-pruned graph can cross only the two
bonds that were actually deleted. -/
theorem boundary_component_eraseTwoBonds_subset (M : Molecule V D) (e f : D)
    (hf : f ≠ e ∧ f ≠ M.mate e) (a : V) :
    boundaryDarts M (componentSet (eraseTwoBonds M e f hf) a) ⊆
      {e,M.mate e,f,M.mate f} := by
  classical
  let N := eraseBond M e
  let f' : WithoutBondDart M e := ⟨f,hf⟩
  let P := eraseTwoBonds M e f hf
  intro z hz
  by_contra hn
  simp only [mem_insert,mem_singleton,not_or] at hn
  let z' : WithoutBondDart M e := ⟨z,hn.1,hn.2.1⟩
  have hzf : z' ≠ f' := fun h => hn.2.2.1 (congrArg Subtype.val h)
  have hzmf : z' ≠ N.mate f' := fun h => hn.2.2.2 (congrArg Subtype.val h)
  let z'' : WithoutBondDart N f' := ⟨z',hzf,hzmf⟩
  have hh := (mem_filter.mp hz).2
  have hp := ((mem_componentSet P a _).mp hh.1).2
  apply hh.2
  exact (mem_componentSet P a _).mpr ⟨M.atom_mem _,Relation.EqvGen.trans _ _ _ hp
    (Relation.EqvGen.rel _ _ ⟨z'',rfl,rfl⟩)⟩

/-- The three actual components have precisely the source case(3)
boundaries: two central bridges, and one bridge at each far component. -/
theorem boundary_three_eraseTwoBonds_components (M : Molecule V D) {e f : D}
    (hf : f ≠ e ∧ f ≠ M.mate e) (heB : IsBridge M e) (hfB : IsBridge M f)
    (hatom : M.atom f = M.atom e) :
    let P := eraseTwoBonds M e f hf
    boundaryDarts M (componentSet P (M.atom e)) = {e,f} ∧
    boundaryDarts M (componentSet P (M.atom (M.mate e))) = {M.mate e} ∧
    boundaryDarts M (componentSet P (M.atom (M.mate f))) = {M.mate f} := by
  classical
  let P := eraseTwoBonds M e f hf
  let b := M.atom e
  let u := M.atom (M.mate e)
  let w := M.atom (M.mate f)
  let C0 := componentSet P b
  let C1 := componentSet P u
  let C2 := componentSet P w
  have hsep := eraseTwoBonds_three_separated M hf heB hfB hatom
  have hb0 : b ∈ C0 := (mem_componentSet P b b).mpr ⟨M.atom_mem e,Relation.EqvGen.refl b⟩
  have hu1 : u ∈ C1 := (mem_componentSet P u u).mpr ⟨M.atom_mem _,Relation.EqvGen.refl u⟩
  have hw2 : w ∈ C2 := (mem_componentSet P w w).mpr ⟨M.atom_mem _,Relation.EqvGen.refl w⟩
  have hu0 : u ∉ C0 := fun h => hsep.1 ((mem_componentSet P b u).mp h).2
  have hw0 : w ∉ C0 := fun h => hsep.2.1 ((mem_componentSet P b w).mp h).2
  have hb1 : b ∉ C1 := fun h => hsep.1 (Relation.EqvGen.symm _ _ ((mem_componentSet P u b).mp h).2)
  have hw1 : w ∉ C1 := fun h => hsep.2.2 ((mem_componentSet P u w).mp h).2
  have hb2 : b ∉ C2 := fun h => hsep.2.1 (Relation.EqvGen.symm _ _ ((mem_componentSet P w b).mp h).2)
  have hu2 : u ∉ C2 := fun h => hsep.2.2 (Relation.EqvGen.symm _ _ ((mem_componentSet P w u).mp h).2)
  have hsub := boundary_component_eraseTwoBonds_subset M e f hf
  refine ⟨?_,?_,?_⟩
  · ext z
    simp only [mem_insert,mem_singleton]
    constructor
    · intro hz
      have hh := hsub b hz
      simp only [mem_insert,mem_singleton] at hh
      rcases hh with h | h | h | h
      · exact Or.inl h
      · have hh' : M.atom z ∈ C0 := (mem_filter.mp hz).2.1
        rw [h] at hh'
        exact False.elim (hu0 hh')
      · exact Or.inr h
      · have hh' : M.atom z ∈ C0 := (mem_filter.mp hz).2.1
        rw [h] at hh'
        exact False.elim (hw0 hh')
    · rintro (h | h)
      · subst z
        exact mem_filter.mpr ⟨mem_univ _,hb0,hu0⟩
      · subst z
        exact mem_filter.mpr ⟨mem_univ _,hatom.symm ▸ hb0,hw0⟩
  · ext z
    simp only [mem_singleton]
    constructor
    · intro hz
      have hh := hsub u hz
      simp only [mem_insert,mem_singleton] at hh
      rcases hh with h | h | h | h
      · have hh' : M.atom z ∈ C1 := (mem_filter.mp hz).2.1
        rw [h] at hh'
        exact False.elim (hb1 hh')
      · exact h
      · have hh' : M.atom z ∈ C1 := (mem_filter.mp hz).2.1
        rw [h,hatom] at hh'
        exact False.elim (hb1 hh')
      · have hh' : M.atom z ∈ C1 := (mem_filter.mp hz).2.1
        rw [h] at hh'
        exact False.elim (hw1 hh')
    · intro h
      subst z
      exact mem_filter.mpr ⟨mem_univ _,hu1,by simpa only [M.mate_mate] using hb1⟩
  · ext z
    simp only [mem_singleton]
    constructor
    · intro hz
      have hh := hsub w hz
      simp only [mem_insert,mem_singleton] at hh
      rcases hh with h | h | h | h
      · have hh' : M.atom z ∈ C2 := (mem_filter.mp hz).2.1
        rw [h] at hh'
        exact False.elim (hb2 hh')
      · have hh' : M.atom z ∈ C2 := (mem_filter.mp hz).2.1
        rw [h] at hh'
        exact False.elim (hu2 hh')
      · have hh' : M.atom z ∈ C2 := (mem_filter.mp hz).2.1
        rw [h,hatom] at hh'
        exact False.elim (hb2 hh')
      · exact h
    · intro h
      subst z
      exact mem_filter.mpr ⟨mem_univ _,hw2,by simpa only [M.mate_mate,hatom] using hb2⟩

end WaveTurbulence.MoleProp
