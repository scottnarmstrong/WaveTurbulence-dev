/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineChainFlows
public import WaveTurbulence.Foundations.Molecule.VineSGJointExclusion
import Mathlib.Tactic

/-! # A contained VC meeting an outer chain junction has the same gap norm -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] {d : ℕ}

/-- A nested block containing a specified outer joint has the same initial
flow norm as the outer flow at that joint. No gap witnesses need be chosen. -/
theorem nested_block_at_joint_flow_norm (M : Molecule V D) (hM : M.IsMolecule)
    {A S : Finset V} {x y a b v : V} (hA : M.IsBlock A x y) (hS : M.IsBlock S a b)
    (hAS : A ⊆ S) (hv : v ∈ A) (hvj : v=a ∨ v=b)
    (k : D → Mom d) (hk : ∀ z,k (M.mate z)=k z)
    (hc : ∀ v ∈ M.atoms,M.deg v=4 → ∑ z ∈ M.dartsAt v,M.dartSign z • k z=0) :
    ‖groupFlow M A k x‖=‖groupFlow M S k v‖ := by
  have hdS : M.degIn S v=2 := hvj.elim
    (fun h => h.symm ▸ (Mole.block_joint_degrees M hS).1)
    (fun h => h.symm ▸ (Mole.block_joint_degrees M hS).2)
  have hlo := block_degree_ge_two M hA hv
  have hle := degIn_mono M hAS v
  have hdA : M.degIn A v=2 := by omega
  have hvxy := block_degree_two_joint M hA hv hdA
  have he := nested_groupFlow_eq M hAS v (hdA.trans hdS.symm) k
  calc
    ‖groupFlow M A k x‖ = ‖groupFlow M A k v‖ := by
      rcases hvxy with hvx | hvy
      · rw [hvx]
      · rw [hvy,block_jointFlow_neg M hM hA k hk hc,norm_neg]
    _ = ‖groupFlow M S k v‖ := congrArg norm he

/-- TARGET subsetvc's junction test: if an inner VC contains a junction
of an outer chain split, conservation forces their actual gap norms to agree.
The inner ingredient at the junction is localized geometrically first. -/
theorem VC_at_chain_split_joint_norm (M : Molecule V D) (hM : M.IsMolecule)
    {S T A : Finset V} {a b c x y : V} {n : ℕ}
    (hS : Chain M S a b n) {X : VineType} (hT : M.IsVine X T b c)
    (hi : S ∩ T={b}) (hU : M.IsBlock (S ∪ T) a c)
    (hA : IsVC M A x y) (hAU : A ⊆ S ∪ T) (hbA : b ∈ A)
    (k : D → Mom d) (hk : ∀ z,k (M.mate z)=k z)
    (hc : ∀ v ∈ M.atoms,M.deg v=4 → ∑ z ∈ M.dartsAt v,M.dartSign z • k z=0) :
    ‖groupFlow M A k x‖=‖groupFlow M (S ∪ T) k a‖ := by
  obtain ⟨hAB,m,hchain⟩ := hA
  obtain ⟨B,p,q,hI,hbB⟩ := chain_atom_ingredient hchain hbA
  obtain ⟨_hIB,⟨Y,hY⟩,hBA⟩ := chainIngredient_spec hI
  have hBY := hBA.trans hAU
  have hflow := (chainIngredient_flow_eq M hM k hk hc hI hAB).1
  have hprefix := chain_prefix_isBlock M hM hS hT hi hU
  rcases vine_in_terminal_split M hM hT.1 hU (chain_joints_mem hS).2 hY hBY with hBS | hBT
  · have hn := nested_block_at_joint_flow_norm M hM hY.1 hprefix hBS hbB (Or.inr rfl) k hk hc
    have hfirst := nested_groupFlow_eq M (show S ⊆ S ∪ T from Finset.subset_union_left) a
      ((Mole.block_joint_degrees M hprefix).1.trans (Mole.block_joint_degrees M hU).1.symm) k
    calc
      ‖groupFlow M A k x‖ = ‖groupFlow M B k p‖ := congrArg norm hflow.symm
      _ = ‖groupFlow M S k b‖ := hn
      _ = ‖groupFlow M S k a‖ := by rw [block_jointFlow_neg M hM hprefix k hk hc,norm_neg]
      _ = ‖groupFlow M (S ∪ T) k a‖ := congrArg norm hfirst
  · have hn := nested_block_at_joint_flow_norm M hM hY.1 hT.1 hBT hbB (Or.inl rfl) k hk hc
    calc
      ‖groupFlow M A k x‖ = ‖groupFlow M B k p‖ := congrArg norm hflow.symm
      _ = ‖groupFlow M T k b‖ := hn
      _ = ‖groupFlow M (S ∪ T) k a‖ := congrArg norm
        (terminal_block_initialFlow M hM hT.1 hU Finset.subset_union_right k hk hc)

end WaveTurbulence.Vine
