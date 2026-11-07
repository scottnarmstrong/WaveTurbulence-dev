/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.FlowUnion
public import WaveTurbulence.Foundations.VineEst.VineEstS2.FlowCancellation

/-! # Actual chain flow restrictions retain the full source gap -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract Finset RegRed
variable {V D : Type*} [DecidableEq V] [Fintype D] {M : Molecule V D}
variable {S T : Finset V} {a b c : V}

theorem block_concat_outer_not_mem (hS : M.IsBlock S a b) (hT : M.IsBlock T b c)
    (hi : S ∩ T = {b}) : a ∉ T ∧ c ∉ S := by
  have hS' := hS
  have hT' := hT
  constructor
  · intro ha
    have he := mem_singleton.mp (hi ▸ mem_inter.mpr ⟨hS'.2.1,ha⟩)
    exact hS'.2.2.2.1 he
  · intro hc
    have he := mem_singleton.mp (hi ▸ mem_inter.mpr ⟨hc,hT'.2.2.1⟩)
    exact hT'.2.2.2.1 he.symm

/-- A finite incidence sum with only its two joint values remaining is zero.
This is an algebra helper; interior zero values are supplied by the actual
restricted full-chain fiber below. -/
theorem flow_joints_add_eq_zero {E : Type*} [AddCommGroup E]
    (M : Molecule V D) (S : Finset V) (a b : V) (ha : a ∈ S) (hb : b ∈ S) (hne : a ≠ b)
    (k : Bond M S → E) (hzero : ∀ v ∈ S, v ≠ a → v ≠ b → flow M S k v = 0) :
    flow M S k a+flow M S k b = 0 := by
  classical
  have hsub : ({a,b} : Finset V) ⊆ S := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact ha
    · exact (mem_singleton.mp hv) ▸ hb
  have he : (∑ v ∈ ({a,b} : Finset V), flow M S k v) = ∑ v ∈ S, flow M S k v := by
    apply Finset.sum_subset hsub
    intro v hv hn
    have hne : v ≠ a ∧ v ≠ b := by simpa only [mem_insert,mem_singleton,not_or] using hn
    exact hzero v hv hne.1 hne.2
  rw [Finset.sum_pair hne] at he
  exact he.trans (sum_flow_zero M S k)

noncomputable def restrictFlowFiber_left {E : Type*} [AddCommGroup E] {r : E}
    (hM : M.IsMolecule) (hS : M.IsBlock S a b) (hT : M.IsBlock T b c)
    (hi : S ∩ T = {b}) (hU : M.IsBlock (S ∪ T) a c)
    (k : FlowFiber M (S ∪ T) a c E r) : FlowFiber M S a b E r := by
  let kS := restrictBondLabels Finset.subset_union_left k.1
  have hS' := hS
  have hout := block_concat_outer_not_mem hS hT hi
  have hleft : flow M S kS a = -r := by
    have he := flow_union hM hS hT hi hU k.1 a
    rw [flow_eq_zero_of_not_mem M T _ hout.1,add_zero] at he
    exact he.symm.trans k.2.1
  have hz : ∀ v ∈ S, v ≠ a → v ≠ b → flow M S kS v = 0 := by
    intro v hv hva hvb
    have hvT : v ∉ T := by
      intro ht
      exact hvb (mem_singleton.mp (hi ▸ mem_inter.mpr ⟨hv,ht⟩))
    have hvc : v ≠ c := fun he => hout.2 (he ▸ hv)
    have he := flow_union hM hS hT hi hU k.1 v
    rw [flow_eq_zero_of_not_mem M T _ hvT,add_zero] at he
    exact he.symm.trans (k.2.2.2 v (mem_union_left _ hv) hva hvc)
  have hsum := flow_joints_add_eq_zero M S a b hS'.2.1 hS'.2.2.1 hS'.2.2.2.1 kS hz
  have hright := eq_neg_of_add_eq_zero_right hsum
  rw [hleft,neg_neg] at hright
  exact ⟨kS,hleft,hright,hz⟩

noncomputable def restrictFlowFiber_right {E : Type*} [AddCommGroup E] {r : E}
    (hM : M.IsMolecule) (hS : M.IsBlock S a b) (hT : M.IsBlock T b c)
    (hi : S ∩ T = {b}) (hU : M.IsBlock (S ∪ T) a c)
    (k : FlowFiber M (S ∪ T) a c E r) : FlowFiber M T b c E r := by
  let kT := restrictBondLabels Finset.subset_union_right k.1
  have hT' := hT
  have hout := block_concat_outer_not_mem hS hT hi
  have hright : flow M T kT c = r := by
    have he := flow_union hM hS hT hi hU k.1 c
    rw [flow_eq_zero_of_not_mem M S _ hout.2,zero_add] at he
    exact he.symm.trans k.2.2.1
  have hz : ∀ v ∈ T, v ≠ b → v ≠ c → flow M T kT v = 0 := by
    intro v hv hvb hvc
    have hvS : v ∉ S := by
      intro hs
      exact hvb (mem_singleton.mp (hi ▸ mem_inter.mpr ⟨hs,hv⟩))
    have hva : v ≠ a := fun he => hout.1 (he ▸ hv)
    have he := flow_union hM hS hT hi hU k.1 v
    rw [flow_eq_zero_of_not_mem M S _ hvS,zero_add] at he
    exact he.symm.trans (k.2.2.2 v (mem_union_right _ hv) hva hvc)
  have hsum := flow_joints_add_eq_zero M T b c hT'.2.1 hT'.2.2.1 hT'.2.2.2.1 kT hz
  have hleft := eq_neg_of_add_eq_zero_left hsum
  rw [hright] at hleft
  exact ⟨kT,hleft,hright,hz⟩

theorem restrictFlowFiber_left_val {E : Type*} [AddCommGroup E] {r : E}
    (hM : M.IsMolecule) (hS : M.IsBlock S a b) (hT : M.IsBlock T b c)
    (hi : S ∩ T = {b}) (hU : M.IsBlock (S ∪ T) a c) (k : FlowFiber M (S ∪ T) a c E r) :
    (restrictFlowFiber_left hM hS hT hi hU k).1 = restrictBondLabels Finset.subset_union_left k.1 := by
  dsimp only [restrictFlowFiber_left]

theorem restrictFlowFiber_right_val {E : Type*} [AddCommGroup E] {r : E}
    (hM : M.IsMolecule) (hS : M.IsBlock S a b) (hT : M.IsBlock T b c)
    (hi : S ∩ T = {b}) (hU : M.IsBlock (S ∪ T) a c) (k : FlowFiber M (S ∪ T) a c E r) :
    (restrictFlowFiber_right hM hS hT hi hU k).1 = restrictBondLabels Finset.subset_union_right k.1 := by
  dsimp only [restrictFlowFiber_right]

end WaveTurbulence.VineEstS2
