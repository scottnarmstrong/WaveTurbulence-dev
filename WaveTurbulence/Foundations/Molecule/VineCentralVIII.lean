/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineStemStarts
public import WaveTurbulence.Foundations.Molecule.VineSlotPropagation
public import WaveTurbulence.Foundations.Molecule.VineUntouchedCoreEdges
public import WaveTurbulence.Foundations.Molecule.VineCoreLabelExclusion
import Mathlib.Tactic

/-! # Arbitrary-rung type-VIII stem exclusion leaves its side triple -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Source stem propagation in type VIII leaves only labels 8,9,10 for
any connected inner block larger than a double bond avoiding outer joints. -/
theorem typeVIII_inner_card_le_three (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (R : VineRealization M .VIII S a b) (hS : M.IsBlock S a b)
    {A : Finset V} {x y : V} (hA : M.IsBlock A x y) (hC : GroupConnected M A)
    (hAS : A ⊆ S) (hcard : 2<A.card) (ha : a ∉ A) (hb : b ∉ A) : A.card ≤ 3 := by
  have hlen : R.k.length=2 := R.length_eq
  obtain ⟨kr,kc,hks⟩ := List.length_eq_two.mp hlen
  have hfirst := stemStarts_absent M hM R hS hA hC hcard ha hb ⟨1,1,4,5⟩ (by exact List.mem_cons_self)
  have hredStart := block_slot_double_start_absent_all M hM R hA hC hcard [] [(((6,8),(7,9)),kc)]
    ((2,4),(3,5)) kr (by rw [hks]; rfl) (by decide) (by decide) hfirst
  have hzero : (R.coreAtom ⟨0,by decide⟩).1 ∉ A := by
    rcases R.core_joint_eq hS ⟨0,by decide⟩ (by decide) with he | he
    · simpa only [he] using ha
    · simpa only [he] using hb
  have hthree : (R.coreAtom ⟨3,by decide⟩).1 ∉ A :=
    hredStart _ (R.coreAtom ⟨3,by decide⟩).2 (Or.inr (R.label_coreAtom ⟨3,by decide⟩))
  have hdist (i j : Fin VineType.VIII.template.n) (hne : i.1 ≠ j.1) :
      (R.coreAtom i).1 ≠ (R.coreAtom j).1 := fun he => hne (congrArg Fin.val (R.coreAtom_injective he))
  obtain ⟨Rd⟩ := R.core_twoIncidences ⟨6,by decide⟩ ⟨7,by decide⟩ (by decide)
  have hpair := block_empty_double_pair M hM hA hC hcard Rd
    (hdist ⟨6,by decide⟩ ⟨7,by decide⟩ (by decide)) hzero hthree
    (hdist ⟨0,by decide⟩ ⟨7,by decide⟩ (by decide))
    (hdist ⟨3,by decide⟩ ⟨6,by decide⟩ (by decide))
    (Mole.adj_symmetric M (R.core_joint_adj ⟨0,by decide⟩ ⟨6,by decide⟩ (by decide) (by decide)))
    (Mole.adj_symmetric M (R.core_untouched_adj ⟨3,by decide⟩ ⟨7,by decide⟩ (by decide) (by decide)))
  have hnext := R.exclude_core_pair ⟨6,by decide⟩ ⟨7,by decide⟩ hpair.1 hpair.2
  have hred := block_empty_slot_from_end M hM R hA hC hcard [] [(((6,8),(7,9)),kc)]
    ((2,4),(3,5)) kr (by rw [hks]; rfl) hfirst
  have hcyan := block_empty_slot_from_start M hM R hA hC hcard [(((2,4),(3,5)),kr)] []
    ((6,8),(7,9)) kc (by rw [hks]; rfl) hnext
  have hred' : ∀ v ∈ S,11 ≤ R.f v → R.f v<11+2*kr → v ∉ A := by
    simpa only [List.foldl_nil,VineType.template] using hred
  have hcyan' : ∀ v ∈ S,11+2*kr ≤ R.f v → R.f v<11+2*kr+2*kc → v ∉ A := by
    simpa only [List.foldl_cons,List.foldl_nil,insertRungs_atoms,VineType.template] using hcyan
  have himage : A.image R.f ⊆ ({8,9,10} : Finset ℕ) := by
    intro z hz
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hz
    have hvS := hAS hv
    have hbound := mem_range.mp (R.image_eq ▸ mem_image_of_mem R.f hvS)
    rw [hks,expand_atoms] at hbound
    norm_num [VineType.template] at hbound
    have hlo : 2 ≤ R.f v := by
      by_contra hh
      have hlt : R.f v<2 := by omega
      rcases (realization_index_lt_two_iff R hS hvS).mp hlt with he | he
      · exact ha (he ▸ hv)
      · exact hb (he ▸ hv)
    have hn2 : R.f v ≠ 2 := fun he => hredStart v hvS (Or.inl he) hv
    have hn3 : R.f v ≠ 3 := fun he => hredStart v hvS (Or.inr he) hv
    have hn4 : R.f v ≠ 4 := fun he => hfirst v hvS (Or.inl he) hv
    have hn5 : R.f v ≠ 5 := fun he => hfirst v hvS (Or.inr he) hv
    have hn6 : R.f v ≠ 6 := fun he => hnext v hvS (Or.inl he) hv
    have hn7 : R.f v ≠ 7 := fun he => hnext v hvS (Or.inr he) hv
    have hnred : ¬(11 ≤ R.f v ∧ R.f v<11+2*kr) := fun h => hred' v hvS h.1 h.2 hv
    have hncyan : ¬(11+2*kr ≤ R.f v ∧ R.f v<11+2*kr+2*kc) := fun h => hcyan' v hvS h.1 h.2 hv
    simp only [mem_insert,mem_singleton]
    omega
  have hc := card_le_card himage
  rw [card_image_of_injOn (fun _ hx _ hy he => R.injOn (hAS hx) (hAS hy) he)] at hc
  exact hc

end WaveTurbulence.Vine
