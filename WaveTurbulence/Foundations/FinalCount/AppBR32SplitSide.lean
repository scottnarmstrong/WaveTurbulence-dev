/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBR3SidePartition
public import WaveTurbulence.Foundations.FinalCount.AppBSpecialSplitSide
public import WaveTurbulence.Foundations.FinalCount.AppBGoodReinsertionEffects
import Mathlib.Tactic

/-! # The actual two-bond old cut in the four-circuit branch of 3R-2G -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def AppbR32SideLabels {E : Type*} [Fintype E] [DecidableEq E] {N : Molecule V E}
    (s : AppbRealization N AppbPatternKind.s33new3.pattern) (S : Finset V) : Prop :=
  (s.vertex 1 ∈ S ∧ s.vertex 2 ∉ S ∧ s.vertex 3 ∈ S ∧ s.vertex 4 ∉ S) ∨
    (s.vertex 2 ∈ S ∧ s.vertex 1 ∉ S ∧ s.vertex 4 ∈ S ∧ s.vertex 3 ∉ S)

theorem appb_r32_split_side_exists (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.r3.pattern)
    (s : AppbRealization r.post AppbPatternKind.s33new3.pattern)
    (hc : ∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v)
    (hb : ∀ e : D,¬Degen.IsBridge M e) (hF : s.post.numComponents = 2) :
    ∃ S : Finset V, ∃ j : Fin AppbPatternKind.r3.pattern.edges.length,
      S ⊆ r.post.atoms ∧ AppbR32SideLabels s S ∧
      appbCrossingBonds M S = {(r.edge j).val,(s.edge ⟨0,by decide⟩).val.val} := by
  classical
  have hN := r.post_numComponents_eq_one_of_small_boundary hc hb (by decide) (by decide) (by decide)
  have hcN : ∀ u ∈ r.post.atoms,∀ v ∈ r.post.atoms,r.post.SameComponent u v := by
    intro u hu v hv
    exact appb_connected_of_numComponents_eq_one r.post hN hu hv
  let S0 := appbSpecialSplitSide s
  let T0 := r.post.atoms \ S0
  have hS0 : S0 ⊆ r.post.atoms := union_subset (by
    intro v hv
    exact ((Degen.mem_residualComponent r.post s.removedAtoms (s.vertex 3) v).mp hv).1)
    (singleton_subset_iff.mpr (s.vertex_mem 1 (by decide)))
  have hT0 : T0 ⊆ r.post.atoms := sdiff_subset
  have hcrossS : appbCrossingBonds r.post S0 = {(s.edge ⟨0,by decide⟩).val} :=
    appb_special_split_side_crossing r.post s hcN hF
  have hcrossT : appbCrossingBonds r.post T0 = {(s.edge ⟨0,by decide⟩).val} :=
    (appb_crossing_complement r.post S0).trans hcrossS
  have hposS := appb_deleted_crossing_card_pos_of_singleton M r.removedAtoms S0
    (s.edge ⟨0,by decide⟩).val hcrossS hb
  have hposT := appb_deleted_crossing_card_pos_of_singleton M r.removedAtoms T0
    (s.edge ⟨0,by decide⟩).val hcrossT hb
  have hsum := appb_r3_side_crossing_card_sum r S0 hS0
  change (appbCrossingBonds M S0 ∩ appbRemovedBonds M r.removedAtoms).card+
    (appbCrossingBonds M T0 ∩ appbRemovedBonds M r.removedAtoms).card = 3 at hsum
  have hcases : (appbCrossingBonds M S0 ∩ appbRemovedBonds M r.removedAtoms).card = 1 ∨
      (appbCrossingBonds M T0 ∩ appbRemovedBonds M r.removedAtoms).card = 1 := by omega
  have hlabelsS : AppbR32SideLabels s S0 := Or.inl (appb_special_split_side_labels r.post s hcN hF)
  have hlabelsT : AppbR32SideLabels s T0 := by
    obtain ⟨h1,h2,h3,h4⟩ := appb_special_split_side_labels r.post s hcN hF
    apply Or.inr
    exact ⟨mem_sdiff.mpr ⟨s.vertex_mem 2 (by decide),h2⟩,
      fun h => (mem_sdiff.mp h).2 h1,mem_sdiff.mpr ⟨s.vertex_mem 4 (by decide),h4⟩,
      fun h => (mem_sdiff.mp h).2 h3⟩
  have select (S : Finset V) (hS : S ⊆ r.post.atoms) (hlabels : AppbR32SideLabels s S)
      (hcross : appbCrossingBonds r.post S = {(s.edge ⟨0,by decide⟩).val})
      (hcard : (appbCrossingBonds M S ∩ appbRemovedBonds M r.removedAtoms).card = 1) :
      ∃ j : Fin AppbPatternKind.r3.pattern.edges.length,
        S ⊆ r.post.atoms ∧ AppbR32SideLabels s S ∧
        appbCrossingBonds M S = {(r.edge j).val,(s.edge ⟨0,by decide⟩).val.val} := by
    obtain ⟨x,hx⟩ := card_eq_one.mp hcard
    have hxm : x ∈ appbCrossingBonds M S ∩ appbRemovedBonds M r.removedAtoms := hx.symm ▸ mem_singleton_self x
    obtain ⟨j,hj⟩ := r.edge.surjective ⟨x,(mem_inter.mp hxm).2⟩
    have he : (r.edge j).val = x := congrArg Subtype.val hj
    have hA : appbCrossingBonds M S ∩ appbRemovedBonds M r.removedAtoms = {(r.edge j).val} := by rw [hx,he]
    have hd := appb_crossing_eraseAtoms_decomposition M r.removedAtoms S
    change appbCrossingBonds (Degen.eraseAtoms M r.removedAtoms) S = {(s.edge ⟨0,by decide⟩).val} at hcross
    rw [hcross,image_singleton,hA,singleton_union] at hd
    exact ⟨j,hS,hlabels,hd⟩
  rcases hcases with h | h
  · obtain ⟨j,hj⟩ := select S0 hS0 hlabelsS hcrossS h
    exact ⟨S0,j,hj⟩
  · obtain ⟨j,hj⟩ := select T0 hT0 hlabelsT hcrossT h
    exact ⟨T0,j,hj⟩

end WaveTurbulence.Mole
