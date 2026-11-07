/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.ChainPrefixBlocks

/-! # Actual source-chain suffixes are current connected blocks

The mirror of `chain_prefix_currentBlock`: if `S` is a block from `a` to `b`, `T` a vine chain from `b` to `c`, `S ∩ T = {b}` and
`S ∪ T` is a block, then `T` is a block (V5 Step 4b: the lower block `U^{<p}` of TARGET (tildeJ2)).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open Finset RegRed WaveTurbulence.VineEstS2
variable {V D : Type*} [DecidableEq V] [Fintype D]

theorem chain_suffix_currentBlock (M : Molecule V D) (hM : M.IsMolecule)
    {S T : Finset V} {a b c : V} {n : ℕ} (hS : M.IsBlock S a b) (hT : Vine.Chain M T b c n) (hi : S ∩ T = {b})
    (hU : M.IsBlock (S ∪ T) a c) : M.IsBlock T b c := by
  have hlo := chain_endpoint_lower hT
  have hmem := Vine.chain_joints_mem hT
  have hdegS := ((isBlock_iff_degree_connected _ _ _ _).mp hS).1
  have hdegU := ((isBlock_iff_degree_connected _ _ _ _).mp hU).1
  have hbc := chain_joints_ne hT
  have hbU : b ∈ S ∪ T := mem_union_left _ hdegS.2.2.1
  have hb4 := hdegU.2.2.2.2.2.2.2.2 b hbU (Ne.symm hdegS.2.2.2.1) hbc
  have hadd := Mole.degIn_union_add_inter M S T hdegS.2.2.1 hmem.1
  have hloop : M.degIn (S ∩ T) b = 0 := by
    rw [hi]
    apply Mole.degIn_singleton_eq_zero M
    intro x hx
    have := Mole.connected_block_no_joint_loop M hS ((isBlock_iff_degree_connected _ _ _ _).mp hS).2 (Or.inr hx)
    rwa [hx] at this
  rw [hloop] at hadd
  have hucout := hdegU.2.2.2.2.2.2.1
  have hucin := hdegU.2.2.2.2.2.2.2.1
  have hb2 := (Mole.block_joint_degrees M hS).2
  have hsumT := Mole.outIn_add_inIn M T b
  have hoc := Mole.outIn_mono M (show T ⊆ S ∪ T from subset_union_right) c
  have hic := Mole.inIn_mono M (show T ⊆ S ∪ T from subset_union_right) c
  refine (isBlock_iff_degree_connected M T b c).mpr ⟨?_, ?_⟩
  · refine ⟨chain_atoms_subset hT, hmem.1, hmem.2, hbc, ?_, ?_, ?_, ?_, chain_interior_degree M hM hT⟩ <;> omega
  · exact (groupConnected_iff_mole M T ⟨b, hmem.1⟩).mp (chain_current_connected hT)

end WaveTurbulence.VineEstS4
