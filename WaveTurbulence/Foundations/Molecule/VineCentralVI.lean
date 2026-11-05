/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineStemStarts
public import WaveTurbulence.Foundations.Molecule.VineSlotPropagation
public import WaveTurbulence.Foundations.Molecule.VineUntouchedCoreEdges
public import WaveTurbulence.Foundations.Molecule.VineCoreLabelExclusion
import Mathlib.Tactic

/-! # Arbitrary-rung type-VI stem exclusion leaves its side triple -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- In type VI, propagation from both outer joints excludes the red and
cyan stems, then the middle pair 8,9 and the green stem. Only labels10,11,12
remain for a connected inner block larger than a double bond. -/
theorem typeVI_inner_card_le_three (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (R : VineRealization M .VI S a b) (hS : M.IsBlock S a b)
    {A : Finset V} {x y : V} (hA : M.IsBlock A x y) (hC : GroupConnected M A)
    (hAS : A ⊆ S) (hcard : 2<A.card) (ha : a ∉ A) (hb : b ∉ A) : A.card ≤ 3 := by
  have hlen : R.k.length=3 := R.length_eq
  obtain ⟨kr,kg,kc,hks⟩ := List.length_eq_three.mp hlen
  have hleft := stemStarts_absent M hM R hS hA hC hcard ha hb ⟨0,0,2,3⟩ (by exact List.mem_cons_self)
  have hright := stemStarts_absent M hM R hS hA hC hcard ha hb ⟨1,1,13,14⟩
    (by exact List.mem_cons_of_mem _ List.mem_cons_self)
  have hredEnd := block_slot_double_end_absent_all M hM R hA hC hcard []
    [(((8,10),(9,11)),kg),(((6,13),(7,14)),kc)] ((2,4),(3,5)) kr
    (by rw [hks]; rfl) (by decide) (by decide) hleft
  have hcyanStart := block_slot_double_start_absent_all M hM R hA hC hcard
    [(((2,4),(3,5)),kr),(((8,10),(9,11)),kg)] [] ((6,13),(7,14)) kc
    (by rw [hks]; rfl) (by decide) (by decide) hright
  have hfive : (R.coreAtom ⟨5,by decide⟩).1 ∉ A :=
    hredEnd _ (R.coreAtom ⟨5,by decide⟩).2 (Or.inr (R.label_coreAtom ⟨5,by decide⟩))
  have hseven : (R.coreAtom ⟨7,by decide⟩).1 ∉ A :=
    hcyanStart _ (R.coreAtom ⟨7,by decide⟩).2 (Or.inr (R.label_coreAtom ⟨7,by decide⟩))
  have hdist (i j : Fin VineType.VI.template.n) (hne : i.1 ≠ j.1) :
      (R.coreAtom i).1 ≠ (R.coreAtom j).1 := fun he => hne (congrArg Fin.val (R.coreAtom_injective he))
  obtain ⟨Rd⟩ := R.core_twoIncidences ⟨8,by decide⟩ ⟨9,by decide⟩ (by decide)
  have hpair := block_empty_double_pair M hM hA hC hcard Rd
    (hdist ⟨8,by decide⟩ ⟨9,by decide⟩ (by decide)) hfive hseven
    (hdist ⟨5,by decide⟩ ⟨9,by decide⟩ (by decide))
    (hdist ⟨7,by decide⟩ ⟨8,by decide⟩ (by decide))
    (Mole.adj_symmetric M (R.core_untouched_adj ⟨5,by decide⟩ ⟨8,by decide⟩ (by decide) (by decide)))
    (Mole.adj_symmetric M (R.core_untouched_adj ⟨7,by decide⟩ ⟨9,by decide⟩ (by decide) (by decide)))
  have hmiddle := R.exclude_core_pair ⟨8,by decide⟩ ⟨9,by decide⟩ hpair.1 hpair.2
  have hred := block_empty_slot_from_start M hM R hA hC hcard []
    [(((8,10),(9,11)),kg),(((6,13),(7,14)),kc)] ((2,4),(3,5)) kr (by rw [hks]; rfl) hleft
  have hgreen := block_empty_slot_from_start M hM R hA hC hcard [(((2,4),(3,5)),kr)]
    [(((6,13),(7,14)),kc)] ((8,10),(9,11)) kg (by rw [hks]; rfl) hmiddle
  have hcyan := block_empty_slot_from_end M hM R hA hC hcard
    [(((2,4),(3,5)),kr),(((8,10),(9,11)),kg)] [] ((6,13),(7,14)) kc (by rw [hks]; rfl) hright
  have hred' : ∀ v ∈ S,15 ≤ R.f v → R.f v<15+2*kr → v ∉ A := by
    simpa only [List.foldl_nil,VineType.template] using hred
  have hgreen' : ∀ v ∈ S,15+2*kr ≤ R.f v → R.f v<15+2*kr+2*kg → v ∉ A := by
    simpa only [List.foldl_cons,List.foldl_nil,insertRungs_atoms,VineType.template] using hgreen
  have hcyan' : ∀ v ∈ S,15+2*kr+2*kg ≤ R.f v → R.f v<15+2*kr+2*kg+2*kc → v ∉ A := by
    simpa only [List.foldl_cons,List.foldl_nil,insertRungs_atoms,VineType.template] using hcyan
  have himage : A.image R.f ⊆ ({10,11,12} : Finset ℕ) := by
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
    have hn2 : R.f v ≠ 2 := fun he => hleft v hvS (Or.inl he) hv
    have hn3 : R.f v ≠ 3 := fun he => hleft v hvS (Or.inr he) hv
    have hn4 : R.f v ≠ 4 := fun he => hredEnd v hvS (Or.inl he) hv
    have hn5 : R.f v ≠ 5 := fun he => hredEnd v hvS (Or.inr he) hv
    have hn6 : R.f v ≠ 6 := fun he => hcyanStart v hvS (Or.inl he) hv
    have hn7 : R.f v ≠ 7 := fun he => hcyanStart v hvS (Or.inr he) hv
    have hn8 : R.f v ≠ 8 := fun he => hmiddle v hvS (Or.inl he) hv
    have hn9 : R.f v ≠ 9 := fun he => hmiddle v hvS (Or.inr he) hv
    have hn13 : R.f v ≠ 13 := fun he => hright v hvS (Or.inl he) hv
    have hn14 : R.f v ≠ 14 := fun he => hright v hvS (Or.inr he) hv
    have hnred : ¬(15 ≤ R.f v ∧ R.f v<15+2*kr) := fun h => hred' v hvS h.1 h.2 hv
    have hngreen : ¬(15+2*kr ≤ R.f v ∧ R.f v<15+2*kr+2*kg) := fun h => hgreen' v hvS h.1 h.2 hv
    have hncyan : ¬(15+2*kr+2*kg ≤ R.f v ∧ R.f v<15+2*kr+2*kg+2*kc) := fun h => hcyan' v hvS h.1 h.2 hv
    simp only [mem_insert,mem_singleton]
    omega
  have hc := card_le_card himage
  rw [card_image_of_injOn (fun _ hx _ hy he => R.injOn (hAS hx) (hAS hy) he)] at hc
  exact hc

end WaveTurbulence.Vine
