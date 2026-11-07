/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103BridgeDeletion
import Mathlib.Tactic

/-! # The exact component and circuit change of one source B operation -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

private theorem sameComponent_eraseBond_lift (M : Molecule V D) (e : D) {u v : V}
    (h : (eraseBond M e).SameComponent u v) : M.SameComponent u v :=
  Relation.EqvGen.mono (fun _ _ ⟨x,hx,hxm⟩ => ⟨x.val,hx,hxm⟩) u v h

/-- Adding the deleted bridge back merges exactly its two endpoint components. -/
theorem sameComponent_eraseBond_add_edge (M : Molecule V D) (e : D) (he : IsBridge M e)
    (u v : V) : M.SameComponent u v ↔
      (eraseBond M e).SameComponent u v ∨
      ((eraseBond M e).SameComponent u (M.atom e) ∧ (eraseBond M e).SameComponent (M.atom (M.mate e)) v) ∨
      ((eraseBond M e).SameComponent u (M.atom (M.mate e)) ∧ (eraseBond M e).SameComponent (M.atom e) v) := by
  let N := eraseBond M e
  let a := M.atom e
  let b := M.atom (M.mate e)
  let R := fun u v => N.SameComponent u v ∨
    (N.SameComponent u a ∧ N.SameComponent b v) ∨ (N.SameComponent u b ∧ N.SameComponent a v)
  have hnot : ¬ N.SameComponent a b := fun h => he ((eraseBond_sameComponent_iff M e a b).mp h)
  have hstep (u v : V) (h : M.Adj u v) : R u v := by
    obtain ⟨x,hx,hxm⟩ := h
    by_cases hxe : x = e
    · subst x
      refine Or.inr (Or.inl ⟨?_,?_⟩)
      · change N.SameComponent u (M.atom e)
        rw [hx]; exact Relation.EqvGen.refl _
      · change N.SameComponent (M.atom (M.mate e)) v
        rw [hxm]; exact Relation.EqvGen.refl _
    by_cases hxme : x = M.mate e
    · subst x
      rw [M.mate_mate] at hxm
      refine Or.inr (Or.inr ⟨?_,?_⟩)
      · change N.SameComponent u (M.atom (M.mate e))
        rw [hx]; exact Relation.EqvGen.refl _
      · change N.SameComponent (M.atom e) v
        rw [hxm]; exact Relation.EqvGen.refl _
    · exact Or.inl (Relation.EqvGen.rel _ _ ⟨⟨x,hxe,hxme⟩,hx,hxm⟩)
  have hsymm {u v : V} (h : R u v) : R v u := by
    rcases h with h | ⟨hua,hbv⟩ | ⟨hub,hav⟩
    · exact Or.inl (Relation.EqvGen.symm _ _ h)
    · exact Or.inr (Or.inr ⟨Relation.EqvGen.symm _ _ hbv,Relation.EqvGen.symm _ _ hua⟩)
    · exact Or.inr (Or.inl ⟨Relation.EqvGen.symm _ _ hav,Relation.EqvGen.symm _ _ hub⟩)
  have htrans {u v w : V} (h : R u v) (h' : R v w) : R u w := by
    rcases h with huv | ⟨hua,hbv⟩ | ⟨hub,hav⟩
    · rcases h' with hvw | ⟨hva,hbw⟩ | ⟨hvb,haw⟩
      · exact Or.inl (Relation.EqvGen.trans _ _ _ huv hvw)
      · exact Or.inr (Or.inl ⟨Relation.EqvGen.trans _ _ _ huv hva,hbw⟩)
      · exact Or.inr (Or.inr ⟨Relation.EqvGen.trans _ _ _ huv hvb,haw⟩)
    · rcases h' with hvw | ⟨hva,hbw⟩ | ⟨hvb,haw⟩
      · exact Or.inr (Or.inl ⟨hua,Relation.EqvGen.trans _ _ _ hbv hvw⟩)
      · exact False.elim (hnot (Relation.EqvGen.symm _ _ (Relation.EqvGen.trans _ _ _ hbv hva)))
      · exact Or.inl (Relation.EqvGen.trans _ _ _ hua haw)
    · rcases h' with hvw | ⟨hva,hbw⟩ | ⟨hvb,haw⟩
      · exact Or.inr (Or.inr ⟨hub,Relation.EqvGen.trans _ _ _ hav hvw⟩)
      · exact Or.inl (Relation.EqvGen.trans _ _ _ hub hbw)
      · exact False.elim (hnot (Relation.EqvGen.trans _ _ _ hav hvb))
  constructor
  · intro hp
    induction hp with
    | rel u v h => exact hstep u v h
    | refl u => exact Or.inl (Relation.EqvGen.refl u)
    | symm u v _ ih => exact hsymm ih
    | trans u v w _ _ ih ih' => exact htrans ih ih'
  · intro hp
    have hab : M.SameComponent a b := Relation.EqvGen.rel _ _ ⟨e,rfl,rfl⟩
    rcases hp with h | ⟨hua,hbv⟩ | ⟨hub,hav⟩
    · exact sameComponent_eraseBond_lift M e h
    · exact Relation.EqvGen.trans _ _ _ (sameComponent_eraseBond_lift M e hua)
        (Relation.EqvGen.trans _ _ _ hab (sameComponent_eraseBond_lift M e hbv))
    · exact Relation.EqvGen.trans _ _ _ (sameComponent_eraseBond_lift M e hub)
        (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hab) (sameComponent_eraseBond_lift M e hav))

/-- The old component of a bridge is the union of its two new components. -/
theorem componentSet_bridge_eq_union (M : Molecule V D) (e : D) (he : IsBridge M e) :
    componentSet M (M.atom e) = componentSet (eraseBond M e) (M.atom e) ∪
      componentSet (eraseBond M e) (M.atom (M.mate e)) := by
  have hnot : ¬ (eraseBond M e).SameComponent (M.atom e) (M.atom (M.mate e)) :=
    fun h => he ((eraseBond_sameComponent_iff M e _ _).mp h)
  have hrefl : (eraseBond M e).SameComponent (M.atom e) (M.atom e) := Relation.EqvGen.refl _
  ext z
  simp only [mem_componentSet,mem_union,sameComponent_eraseBond_add_edge M e he,
    hrefl,hnot,true_and,false_and,or_false]
  change (_ ∧ (_ ∨ _)) ↔ (_ ∧ _) ∨ (_ ∧ _)
  tauto

/-- An old component away from the bridge endpoints is unchanged. -/
theorem componentSet_eraseBond_of_not_sameComponent (M : Molecule V D) (e : D) (he : IsBridge M e)
    {u : V} (hu : ¬ M.SameComponent u (M.atom e)) :
    componentSet M u = componentSet (eraseBond M e) u := by
  have hna : ¬ (eraseBond M e).SameComponent u (M.atom e) :=
    fun h => hu (sameComponent_eraseBond_lift M e h)
  have hnb : ¬ (eraseBond M e).SameComponent u (M.atom (M.mate e)) := by
    intro h
    exact hu (Relation.EqvGen.trans _ _ _ (sameComponent_eraseBond_lift M e h)
      (Relation.EqvGen.rel _ _ ⟨M.mate e,rfl,by rw [M.mate_mate]⟩))
  ext z
  simp only [mem_componentSet,sameComponent_eraseBond_add_edge M e he,hna,hnb,false_and,or_false]
  rfl

/-- The finite component family changes by replacing one old component
with exactly the two disjoint actual endpoint components. -/
theorem componentSets_eraseBond_merge (M : Molecule V D) (e : D) (he : IsBridge M e) :
    componentSets M =
      (((componentSets (eraseBond M e)).erase (componentSet (eraseBond M e) (M.atom e))).erase
        (componentSet (eraseBond M e) (M.atom (M.mate e)))) ∪
      {componentSet (eraseBond M e) (M.atom e) ∪ componentSet (eraseBond M e) (M.atom (M.mate e))} := by
  classical
  let N := eraseBond M e
  let a := M.atom e
  let b := M.atom (M.mate e)
  have ham : a ∈ N.atoms := M.atom_mem e
  have hbm : b ∈ N.atoms := M.atom_mem (M.mate e)
  have hnot : ¬ N.SameComponent a b := fun h => he ((eraseBond_sameComponent_iff M e a b).mp h)
  have hba : ¬ N.SameComponent b a := fun h => hnot (Relation.EqvGen.symm _ _ h)
  have haa : N.SameComponent a a := Relation.EqvGen.refl _
  have hroot := componentSet_bridge_eq_union M e he
  ext S
  constructor
  · intro hS
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hS
    by_cases hua : M.SameComponent u a
    · apply mem_union_right
      apply mem_singleton.mpr
      exact ((componentSet_eq_iff M hu).mpr hua).trans hroot
    · apply mem_union_left
      have hset := componentSet_eraseBond_of_not_sameComponent M e he hua
      have hCa : componentSet M u ≠ componentSet N a := by
        intro hh
        have hNu : N.SameComponent u a := (componentSet_eq_iff N hu).mp (hset.symm.trans hh)
        exact hua (sameComponent_eraseBond_lift M e hNu)
      have hCb : componentSet M u ≠ componentSet N b := by
        intro hh
        have hNu : N.SameComponent u b := (componentSet_eq_iff N hu).mp (hset.symm.trans hh)
        exact hua (Relation.EqvGen.trans _ _ _ (sameComponent_eraseBond_lift M e hNu)
          (Relation.EqvGen.rel _ _ ⟨M.mate e,rfl,by rw [M.mate_mate]⟩))
      exact mem_erase.mpr ⟨hCb,mem_erase.mpr ⟨hCa,mem_image.mpr ⟨u,hu,hset.symm⟩⟩⟩
  · intro hS
    rcases mem_union.mp hS with hS | hS
    · obtain ⟨hSb,hS⟩ := mem_erase.mp hS
      obtain ⟨hSa,hS⟩ := mem_erase.mp hS
      obtain ⟨u,hu,hUS⟩ := mem_image.mp hS
      have hna : ¬ N.SameComponent u a := fun h => hSa (hUS.symm.trans ((componentSet_eq_iff N hu).mpr h))
      have hnb : ¬ N.SameComponent u b := fun h => hSb (hUS.symm.trans ((componentSet_eq_iff N hu).mpr h))
      have hua : ¬ M.SameComponent u a := by
        intro h
        have hh := (sameComponent_eraseBond_add_edge M e he u a).mp h
        rcases hh with hh | ⟨hh,_⟩ | ⟨hh,_⟩
        · exact hna hh
        · exact hna hh
        · exact hnb hh
      exact mem_image.mpr ⟨u,hu,(componentSet_eraseBond_of_not_sameComponent M e he hua).trans hUS⟩
    · have hS' := mem_singleton.mp hS
      exact mem_image.mpr ⟨a,ham,hroot.trans hS'.symm⟩

/-- Deleting an actual bridge increases the actual quotient component count by one. -/
theorem numComponents_eraseBond_eq_add_one (M : Molecule V D) (e : D) (he : IsBridge M e) :
    (eraseBond M e).numComponents = M.numComponents + 1 := by
  classical
  let N := eraseBond M e
  let A := componentSet N (M.atom e)
  let B := componentSet N (M.atom (M.mate e))
  let K := componentSets N
  have hA : A ∈ K := mem_image.mpr ⟨M.atom e,M.atom_mem e,rfl⟩
  have hB : B ∈ K := mem_image.mpr ⟨M.atom (M.mate e),M.atom_mem _,rfl⟩
  have hnot : ¬ N.SameComponent (M.atom e) (M.atom (M.mate e)) :=
    fun h => he ((eraseBond_sameComponent_iff M e _ _).mp h)
  have hAB : A ≠ B := fun h => hnot ((componentSet_eq_iff N (M.atom_mem e)).mp h)
  have hBk : B ∈ K.erase A := mem_erase.mpr ⟨hAB.symm,hB⟩
  have h1 := card_erase_add_one hA
  have h2 := card_erase_add_one hBk
  have haA : M.atom e ∈ A := (mem_componentSet N _ _).mpr ⟨M.atom_mem _,Relation.EqvGen.refl _⟩
  have hbB : M.atom (M.mate e) ∈ B := (mem_componentSet N _ _).mpr ⟨M.atom_mem _,Relation.EqvGen.refl _⟩
  have hUnionNot : A ∪ B ∉ K := by
    intro hU
    obtain ⟨u,_hu,hUS⟩ := mem_image.mp hU
    have hau : M.atom e ∈ componentSet N u := by rw [hUS]; exact mem_union_left _ haA
    have hbu : M.atom (M.mate e) ∈ componentSet N u := by rw [hUS]; exact mem_union_right _ hbB
    exact hnot (Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ ((mem_componentSet N _ _).mp hau).2)
      ((mem_componentSet N _ _).mp hbu).2)
  have hDis : Disjoint ((K.erase A).erase B) {A ∪ B} := by
    apply disjoint_left.mpr
    intro S hS hSU
    have hS' : S ∈ K := (mem_erase.mp (mem_erase.mp hS).2).2
    exact hUnionNot (mem_singleton.mp hSU ▸ hS')
  have hF := componentSets_eraseBond_merge M e he
  have hcard := congrArg Finset.card hF
  change (componentSets M).card = (((K.erase A).erase B) ∪ {A ∪ B}).card at hcard
  rw [card_union_of_disjoint hDis,card_singleton] at hcard
  rw [numComponents_eq_card_componentSets,numComponents_eq_card_componentSets]
  change K.card = (componentSets M).card + 1
  omega


/-- The retained outgoing darts are precisely the old bonds avoiding the deleted pair. -/
theorem card_bonds_eraseBond (M : Molecule V D) (e : D) :
    (eraseBond M e).bonds.card = (M.bonds.filter (fun x => x ≠ e ∧ x ≠ M.mate e)).card := by
  apply card_bij (fun x _ => x.val)
  · intro x hx
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩,x.property⟩
  · intro x _ y _ h
    exact Subtype.ext h
  · intro x hx
    obtain ⟨hxB,hxe,hxm⟩ := mem_filter.mp hx
    exact ⟨⟨x,hxe,hxm⟩,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hxB).2⟩,rfl⟩

/-- Removing both darts removes exactly one actual bond. -/
theorem card_bonds_eraseBond_add_one (M : Molecule V D) (e : D) :
    (eraseBond M e).bonds.card + 1 = M.bonds.card := by
  rw [card_bonds_eraseBond]
  cases ho : M.out e
  · have hm : M.mate e ∈ M.bonds := mem_filter.mpr ⟨mem_univ _,by rw [M.out_mate,ho]; rfl⟩
    have hF : M.bonds.filter (fun x => x ≠ e ∧ x ≠ M.mate e) = M.bonds.erase (M.mate e) := by
      ext x
      simp only [mem_filter,mem_erase]
      constructor
      · rintro ⟨hx,hxe,hxm⟩
        exact ⟨hxm,hx⟩
      · rintro ⟨hxm,hx⟩
        refine ⟨hx,?_,hxm⟩
        intro hxe
        have hh := (mem_filter.mp hx).2
        rw [hxe,ho] at hh
        cases hh
    rw [hF]
    exact card_erase_add_one hm
  · have hm : e ∈ M.bonds := mem_filter.mpr ⟨mem_univ _,ho⟩
    have hF : M.bonds.filter (fun x => x ≠ e ∧ x ≠ M.mate e) = M.bonds.erase e := by
      ext x
      simp only [mem_filter,mem_erase]
      constructor
      · rintro ⟨hx,hxe,_hxm⟩
        exact ⟨hxe,hx⟩
      · rintro ⟨hxe,hx⟩
        refine ⟨hx,hxe,?_⟩
        intro hxm
        have hh := (mem_filter.mp hx).2
        rw [hxm,M.out_mate,ho] at hh
        cases hh
    rw [hF]
    exact card_erase_add_one hm

/-- Source B has exactly zero circuit change, with the actual quotient F. -/
theorem circuitRank_eraseBond_eq (M : Molecule V D) (e : D) (he : IsBridge M e) :
    (eraseBond M e).circuitRank = M.circuitRank := by
  have hE := card_bonds_eraseBond_add_one M e
  have hF := numComponents_eraseBond_eq_add_one M e he
  unfold Molecule.circuitRank
  change ((eraseBond M e).bonds.card : ℤ) - M.atoms.card + (eraseBond M e).numComponents =
    (M.bonds.card : ℤ) - M.atoms.card + M.numComponents
  omega

end WaveTurbulence.MoleProp
