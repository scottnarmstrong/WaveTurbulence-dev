/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineGroupDegreeUnion
public import WaveTurbulence.Foundations.Molecule.VineChainEnds
import Mathlib.Tactic

/-! # Source chain prefixes are blocks inside an actual block -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- The two endpoint atoms of an ordered vine chain differ. -/
theorem chain_joints_ne {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Chain M S a b n) : a ≠ b := by
  cases h with
  | single h => obtain ⟨X,hX⟩ := h; exact hX.1.2.2.2.1
  | append _ _ _ hne => exact hne

/-- Every chain atom belongs to the molecule's declared atom set. -/
theorem chain_atoms_subset {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Chain M S a b n) : S ⊆ M.atoms := by
  induction h with
  | single h => obtain ⟨X,hX⟩ := h; exact hX.1.1
  | append _ hT _ _ ih =>
    obtain ⟨X,hX⟩ := hT
    exact union_subset ih hX.1.1

/-- Both endpoints of a chain retain at least one incidence in each direction. -/
theorem chain_endpoint_lower {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Chain M S a b n) :
    1 ≤ M.outIn S a ∧ 1 ≤ M.inIn S a ∧ 1 ≤ M.outIn S b ∧ 1 ≤ M.inIn S b := by
  induction h with
  | single h =>
    obtain ⟨X,hX⟩ := h
    obtain ⟨_hS,_ha,_hb,_hne,hoa,hia,hob,hib,_hint⟩ := hX.1
    omega
  | @append S T a b c n _hS hT _hi _hne ih =>
    obtain ⟨X,hX⟩ := hT
    obtain ⟨_hT,_hb,_hc,_hbc,_hob,_hib,hoc,hic,_hint⟩ := hX.1
    have hl := oriented_degree_mono (M := M) (show S ⊆ S ∪ T from subset_union_left) a
    have hr := oriented_degree_mono (M := M) (show T ⊆ S ∪ T from subset_union_right) c
    omega

/-- Every interior chain atom already uses all four ambient incidences,
regardless of possible extra bonds between the two endpoints. -/
theorem chain_interior_degree (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} {n : ℕ} (h : Chain M S a b n) :
    ∀ v ∈ S,v ≠ a → v ≠ b → M.degIn S v=4 := by
  induction h with
  | single h =>
    obtain ⟨X,hX⟩ := h
    exact hX.1.2.2.2.2.2.2.2.2.1
  | @append S T a b c n hS hT hi _hne ih =>
    obtain ⟨X,hX⟩ := hT
    have hloop := connected_degree_two_no_loop M (isVine_connected hX)
      hX.1.2.1 hX.1.2.2.1 hX.1.2.2.2.1 (Mole.block_joint_degrees M hX.1).1
    intro v hv hva hvc
    have hvM : v ∈ M.atoms := (union_subset (chain_atoms_subset hS) hX.1.1) hv
    have hbound := (Mole.degIn_le_deg M (S ∪ T) v).trans (Mole.deg_le_four M hM hvM)
    by_cases hvb : v=b
    · subst v
      have hlo := chain_endpoint_lower hS
      have hsum := Mole.outIn_add_inIn M S b
      have hTdeg := (Mole.block_joint_degrees M hX.1).1
      have hle := degIn_add_le_union M hi hloop b
      omega
    · rcases mem_union.mp hv with hv | hv
      · have hd := ih v hv hva hvb
        have hle := degIn_mono M (show S ⊆ S ∪ T from subset_union_left) v
        omega
      · have hd := hX.1.2.2.2.2.2.2.2.2.1 v hv hvb hvc
        have hle := degIn_mono M (show T ⊆ S ∪ T from subset_union_right) v
        omega

/-- In an actual block, removing its terminal vine ingredient leaves an
actual prefix block. The shared joint is saturated by the two incidence
families, so no extra premise about prefix degrees is needed. -/
theorem chain_prefix_isBlock (M : Molecule V D) (hM : M.IsMolecule)
    {S T : Finset V} {a b c : V} {n : ℕ} (hS : Chain M S a b n)
    {X : VineType} (hT : M.IsVine X T b c) (hi : S ∩ T={b})
    (hU : M.IsBlock (S ∪ T) a c) : M.IsBlock S a b := by
  have hmem := chain_joints_mem hS
  have hlo := chain_endpoint_lower hS
  have hla := oriented_degree_mono M (show S ⊆ S ∪ T from subset_union_left) a
  have hloop := connected_degree_two_no_loop M (isVine_connected hT)
    hT.1.2.1 hT.1.2.2.1 hT.1.2.2.2.1 (Mole.block_joint_degrees M hT.1).1
  have hob := group_filtered_card_union_le M hi hloop b (fun d => M.out d=true)
  have hib := group_filtered_card_union_le M hi hloop b (fun d => M.out d=false)
  change M.outIn S b+M.outIn T b ≤ M.outIn (S ∪ T) b at hob
  change M.inIn S b+M.inIn T b ≤ M.inIn (S ∪ T) b at hib
  have hbo := (outIn_le_outdeg M (S ∪ T) b).trans (hM.1 b (hT.1.1 hT.1.2.1)).1
  have hbi := (inIn_le_indeg M (S ∪ T) b).trans (hM.1 b (hT.1.1 hT.1.2.1)).2
  obtain ⟨_hTU,_ha,_hc,_hac,hoa,hia,_hoc,_hic,_hint⟩ := hU
  obtain ⟨_hT,_hb,_hc,_hbc,hot,hit,_hot',_hit',_hint'⟩ := hT.1
  refine ⟨chain_atoms_subset hS,hmem.1,hmem.2,chain_joints_ne hS,
    by omega,by omega,by omega,by omega,chain_interior_degree M hM hS, ?_⟩
  intro u hu v hv
  have hmono : (Mole.induced M S).Adj ≤
      fun x y => ∃ z, M.InGroup S z ∧ M.atom z = x ∧ M.atom (M.mate z) = y := by
    intro x y hxy
    obtain ⟨z, hx, hy⟩ := hxy
    exact ⟨z.1, z.2, hx, hy⟩
  exact Relation.EqvGen.mono hmono u v (chain_connected hS u hu v hv)

end WaveTurbulence.Vine
