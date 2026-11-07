/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.LowDegreeConnectivity
public import WaveTurbulence.Foundations.FinalCount.MoleProp.BridgeSeparation
public import WaveTurbulence.Foundations.FinalCount.Degen.CircuitDeletion
import Mathlib.Tactic

/-! # Low-degree residual boundary patterns for DH23 Proposition 10.1

The zero-loss branch fixes every incident label. The intermediate
three-valent branch has a singleton crossing cut and fixes one label.
Both conclusions come from actual components and conservation equations.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- If the number of newly bounded components equals the removed degree,
every one of their boundaries is a singleton. No loop exclusion is needed
for this implication. -/
theorem boundary_card_eq_one_of_card_newComponents_eq_degree (M : Molecule V D)
    {v : V} (hc : (newComponents M {v}).card = M.deg v)
    {S : Finset V} (hS : S ∈ newComponents M {v}) :
    (boundaryDarts M S).card = 1 := by
  classical
  have hpos : ∀ T ∈ newComponents M {v}, 1 ≤ (boundaryDarts M T).card :=
    fun T hT => card_pos.mpr (mem_filter.mp hT).2
  have hsum := sum_newComponents_boundary_card_le M {v}
  have hbound := boundary_singleton_card_le_degree M v
  by_contra hn
  have hstrict : (∑ _T ∈ newComponents M {v}, (1 : ℕ)) <
      ∑ T ∈ newComponents M {v}, (boundaryDarts M T).card := by
    apply Finset.sum_lt_sum hpos
    exact ⟨S,hS,by have := hpos S hS; omega⟩
  rw [Finset.sum_const_nat (fun _ _ => rfl),Nat.mul_one] at hstrict
  omega

/-- Two residual boundary components at a degree-three atom force at
least one actual single-crossing-bond component. -/
theorem exists_single_boundary_of_degree_three_card_two (M : Molecule V D)
    {v : V} (hdeg : M.deg v = 3) (hc : (newComponents M {v}).card = 2) :
    ∃ S ∈ newComponents M {v}, (boundaryDarts M S).card = 1 := by
  classical
  by_contra hn
  push Not at hn
  have htwo := two_mul_card_newComponents_le_of_no_single M {v} hn
  have hb := boundary_singleton_card_le_degree M v
  omega

/-- The unique crossing bond of a residual component has its other dart
at the removed atom, providing a structural choice of incident label. -/
theorem exists_incident_dart_of_single_boundary (M : Molecule V D)
    {v : V} {S : Finset V} (hS : S ∈ newComponents M {v})
    (hc : (boundaryDarts M S).card = 1) :
    ∃ e : D, M.atom e = v ∧ boundaryDarts M S = {M.mate e} := by
  classical
  obtain ⟨x,hx⟩ := card_eq_one.mp hc
  have hxm : x ∈ boundaryDarts M S := by rw [hx]; exact mem_singleton_self x
  obtain ⟨hrep,_⟩ := mem_filter.mp hS
  obtain ⟨u,_hu,huS⟩ := mem_image.mp hrep
  have hat : M.atom (M.mate x) ∈ ({v} : Finset V) := by
    rw [← huS] at hxm
    exact residual_boundary_ends_in_removed M {v} u hxm
  exact ⟨M.mate x,mem_singleton.mp hat,by simpa only [M.mate_mate] using hx⟩

/-- An incident label selected by a singleton residual boundary is fixed
by the old conservation data, even when degree-four charges are nonzero. -/
theorem incident_label_unique_of_single_boundary (M : Molecule V D)
    {d : ℕ} {L : ℝ} (hL : L ≠ 0) {w : Mom d} {c : V → Mom d}
    {κ κ' : D → (Fin d → ℤ)} (hd : M.IsDecoration L w c κ)
    (hd' : M.IsDecoration L w c κ') {e : D} {S : Finset V}
    (hb : boundaryDarts M S = {M.mate e}) : κ e = κ' e := by
  have he := bridge_label_unique M hL hd hd' (M.mate e) (isBridge_of_single_boundary M S hb)
  simpa only [hd.1 e,hd'.1 e] using he

/-- Every incident dart crosses into an actual bounded residual component
when loops are absent. -/
theorem incident_dart_residual_boundary (M : Molecule V D)
    (hloop : ∀ x, M.atom x ≠ M.atom (M.mate x)) {v : V} {e : D}
    (he : M.atom e = v) :
    ∃ S ∈ newComponents M {v}, M.mate e ∈ boundaryDarts M S := by
  classical
  let u := M.atom (M.mate e)
  have huv : u ≠ v := by simpa only [u,← he] using (hloop e).symm
  have hu : u ∈ residualComponent M {v} u :=
    (mem_residualComponent M {v} u u).mpr
      ⟨M.atom_mem _,by simpa only [mem_singleton] using huv,Relation.EqvGen.refl u⟩
  have hvnot : v ∉ residualComponent M {v} u := by
    intro hv
    exact ((mem_residualComponent M {v} u v).mp hv).2.1 (mem_singleton_self v)
  have hb : M.mate e ∈ boundaryDarts M (residualComponent M {v} u) := by
    apply mem_filter.mpr
    exact ⟨mem_univ _,hu,by simpa only [M.mate_mate,he] using hvnot⟩
  refine ⟨residualComponent M {v} u,mem_filter.mpr ⟨?_,⟨M.mate e,hb⟩⟩,hb⟩
  exact mem_image.mpr ⟨u,mem_sdiff.mpr ⟨M.atom_mem _,by simpa only [mem_singleton] using huv⟩,rfl⟩

/-- Zero circuit loss at a loopless r-valent removal fixes every incident
label when there are r newly bounded components. -/
theorem incident_labels_unique_of_card_newComponents_eq_degree (M : Molecule V D)
    (hloop : ∀ x, M.atom x ≠ M.atom (M.mate x)) {v : V}
    (hc : (newComponents M {v}).card = M.deg v)
    {d : ℕ} {L : ℝ} (hL : L ≠ 0) {w : Mom d} {c : V → Mom d}
    {κ κ' : D → (Fin d → ℤ)} (hd : M.IsDecoration L w c κ)
    (hd' : M.IsDecoration L w c κ') :
    ∀ e, M.atom e = v → κ e = κ' e := by
  intro e he
  obtain ⟨S,hS,heS⟩ := incident_dart_residual_boundary M hloop he
  have hcard := boundary_card_eq_one_of_card_newComponents_eq_degree M hc hS
  have hb' : boundaryDarts M S = {M.mate e} := by
    obtain ⟨x,hx⟩ := card_eq_one.mp hcard
    have hxe : M.mate e = x := by rw [hx] at heS; exact mem_singleton.mp heS
    simpa only [← hxe] using hx
  exact incident_label_unique_of_single_boundary M hL hd hd' hb'

end WaveTurbulence.MoleProp
