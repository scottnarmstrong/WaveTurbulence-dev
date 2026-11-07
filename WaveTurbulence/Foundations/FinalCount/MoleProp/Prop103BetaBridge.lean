/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103BetaState
import Mathlib.Tactic

/-! # A bridge deletion cannot newly enable a source beta operation -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A vertex still of degree four after B has lost no old incidence. -/
theorem old_star_eq_image_of_eraseBond_four (M : Molecule V D) (hM : M.IsMolecule)
    (e : D) {v : V} (hv : v ∈ M.atoms) (h4 : (eraseBond M e).deg v = 4) :
    ((eraseBond M e).dartsAt v).image (fun z => z.val) = M.dartsAt v := by
  classical
  have hs : ((eraseBond M e).dartsAt v).image (fun z => z.val) ⊆ M.dartsAt v := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hx
    exact (Mole.mem_dartsAt M v z.val).mpr ((Mole.mem_dartsAt _ v z).mp hz)
  apply Finset.eq_of_subset_of_card_le hs
  rw [card_image_of_injective _ Subtype.val_injective]
  change M.deg v ≤ (eraseBond M e).deg v
  rw [h4]
  exact Mole.deg_le_four M hM hv

/-- Every oriented star only shrinks under B. -/
theorem card_filtered_dartsAt_eraseBond_le (M : Molecule V D) (e : D) (v : V)
    (p : D → Prop) [DecidablePred p] :
    (((eraseBond M e).dartsAt v).filter (fun z => p z.val)).card ≤
      ((M.dartsAt v).filter p).card := by
  classical
  have hs : ((((eraseBond M e).dartsAt v).filter (fun z => p z.val)).image
      (fun z => z.val)) ⊆ (M.dartsAt v).filter p := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hx
    have hh := mem_filter.mp hz
    exact mem_filter.mpr ⟨(Mole.mem_dartsAt M v z.val).mpr
      ((Mole.mem_dartsAt _ v z).mp hh.1),hh.2⟩
  have hc := card_le_card hs
  rw [card_image_of_injective _ Subtype.val_injective] at hc
  exact hc

/-- Deleting a bond preserves the actual molecule axioms, whether or not
that bond is a bridge. Nonsaturation is proved component by component. -/
theorem eraseBond_isMolecule (M : Molecule V D) (hM : M.IsMolecule) (e : D) :
    (eraseBond M e).IsMolecule := by
  classical
  constructor
  · intro v hv
    exact ⟨(card_filtered_dartsAt_eraseBond_le M e v (fun z => M.out z = true)).trans (hM.1 v hv).1,
      (card_filtered_dartsAt_eraseBond_le M e v (fun z => M.out z = false)).trans (hM.1 v hv).2⟩
  · intro v hv
    by_contra hn
    have hsat (a : V) (ha : a ∈ M.atoms) (hp : (eraseBond M e).SameComponent v a) :
        (eraseBond M e).deg a = 4 := by
      by_contra hne
      exact hn ⟨a,ha,hp,hne⟩
    let C := fun a => a ∈ M.atoms ∧ (eraseBond M e).SameComponent v a
    have hclosed (a b : V) (hab : M.Adj a b) (ha : C a) : C b := by
      obtain ⟨z,hza,hzb⟩ := hab
      have hz : z ∈ M.dartsAt a := (Mole.mem_dartsAt M a z).mpr hza
      rw [← old_star_eq_image_of_eraseBond_four M hM e ha.1 (hsat a ha.1 ha.2)] at hz
      obtain ⟨w,hw,hwz⟩ := mem_image.mp hz
      have hwa : (eraseBond M e).atom w = a := (Mole.mem_dartsAt _ a w).mp hw
      have hwb : (eraseBond M e).atom ((eraseBond M e).mate w) = b := by
        change M.atom (M.mate w.val) = b
        rw [hwz]
        exact hzb
      exact ⟨hzb ▸ M.atom_mem (M.mate z),Relation.EqvGen.trans _ _ _ ha.2
        (Relation.EqvGen.rel _ _ ⟨w,hwa,hwb⟩)⟩
    have hpath (a b : V) (hp : M.SameComponent a b) : C a ↔ C b := by
      induction hp with
      | rel a b h => exact ⟨hclosed a b h,hclosed b a (Mole.adj_symmetric M h)⟩
      | refl a => rfl
      | symm a b _ ih => exact ih.symm
      | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
    obtain ⟨a,ha,hva,hne⟩ := hM.2 v hv
    have haC := (hpath v a hva).mp ⟨hv,Relation.EqvGen.refl v⟩
    have h4 := hsat a haC.1 haC.2
    have heq := congrArg Finset.card (old_star_eq_image_of_eraseBond_four M hM e ha h4)
    rw [card_image_of_injective _ Subtype.val_injective] at heq
    apply hne
    change (eraseBond M e).deg a = M.deg a at heq
    omega

/-- Both the old degree-four star and its incident nonbridge condition are
recovered from actual post-B degree-four data. -/
theorem degree_four_and_nonbridges_before_eraseBond (M : Molecule V D) (hM : M.IsMolecule)
    (e : D) (he : IsBridge M e) {v : V} (hv : v ∈ M.atoms)
    (h4 : (eraseBond M e).deg v = 4)
    (hnb : ∀ z, (eraseBond M e).atom z = v → ¬ IsBridge (eraseBond M e) z) :
    M.deg v = 4 ∧ (∀ z, M.atom z = v → ¬ IsBridge M z) := by
  classical
  have hstar := old_star_eq_image_of_eraseBond_four M hM e hv h4
  constructor
  · have hh := congrArg Finset.card hstar
    rw [card_image_of_injective _ Subtype.val_injective] at hh
    change (eraseBond M e).deg v = M.deg v at hh
    omega
  · intro z hz hb
    have hzm : z ∈ M.dartsAt v := (Mole.mem_dartsAt M v z).mpr hz
    rw [← hstar] at hzm
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hzm
    exact hnb w hz ((isBridge_eraseBond_iff M e he w).mpr hb)

/-- The literal permitted source beta operation cannot be created by B.
All its old premises are derived from the actual post graph. -/
theorem admitsBetaSplit_before_eraseBond (M : Molecule V D) (hM : M.IsMolecule)
    (e : D) (he : IsBridge M e) : AdmitsBetaSplit (eraseBond M e) → AdmitsBetaSplit M := by
  rintro ⟨v,x,y,hd,h4,hnb,hdisc⟩
  have hd0 : (withFreshAtom M).IsCutData (some v) none x.val y.val := by
    refine ⟨hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1,?_,hd.2.2.2.2.2.1,hd.2.2.2.2.2.2⟩
    intro h
    apply hd.2.2.2.2.1
    exact Subtype.ext h
  have hv : v ∈ M.atoms := by
    obtain ⟨a,ha,hav⟩ := mem_map.mp hd0.1
    change some a = some v at hav
    exact Option.some.inj hav ▸ ha
  obtain ⟨hv4,hvnb⟩ := degree_four_and_nonbridges_before_eraseBond M hM e he hv h4 hnb
  refine ⟨v,x.val,y.val,hd0,hv4,hvnb,?_⟩
  intro hp
  have hef : IsBridge (withFreshAtom M) e :=
    (mapAtoms_isBridge_iff M (someAtomEmbedding V) e).mpr he
  have hp' := (cut_joints_sameComponent_eraseBond_iff (withFreshAtom M) hd0 hef).mp hp
  have hp'' := (sameComponent_eraseBond_cut_iff (withFreshAtom M) x.property y.property (some v) none).mp hp'
  exact hdisc hp''

end WaveTurbulence.MoleProp
