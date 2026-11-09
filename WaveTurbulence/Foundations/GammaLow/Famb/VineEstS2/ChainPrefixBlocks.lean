/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.ChainPrefixBlocks
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.ChainPrefixBlocks` and of `Vine.chain_joints_mem`
-- (`Molecule/VineChainConnected`) for L6's chains over 𝒱_γ (`FinalCount.Src.Chain`); see COPIED-SHA256SUMS.
-- The proofs use only that every ingredient is a block (`memBlock`).

/-! # Source chains over `𝒱_γ`: joints, atoms, connectivity, and their prefixes are current connected blocks -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2
open Finset RegRed
variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {γF : ℝ}

/-- Both declared chain joints belong to its atom set. -/
theorem chain_joints_memΓ {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : FinalCount.Src.Chain γF M S a b n) : a ∈ S ∧ b ∈ S := by
  induction h with
  | single h => exact ⟨(memBlock h).2.1, (memBlock h).2.2.1⟩
  | append _ hT _ _ ih => exact ⟨mem_union_left _ ih.1, mem_union_right _ (memBlock hT).2.2.1⟩

theorem chain_posΓ {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : FinalCount.Src.Chain γF M S a b n) : 1 ≤ n := by
  cases h <;> omega

theorem chain_joints_neΓ {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : FinalCount.Src.Chain γF M S a b n) : a ≠ b := by
  cases h with
  | single h => exact (memBlock h).2.2.2.1
  | append _ _ _ hne => exact hne

theorem chain_atoms_subsetΓ {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : FinalCount.Src.Chain γF M S a b n) : S ⊆ M.atoms := by
  induction h with
  | single h => exact (memBlock h).1
  | append _ hT _ _ ih => exact union_subset ih (memBlock hT).1

theorem chain_current_connectedΓ {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : FinalCount.Src.Chain γF M S a b n) : M.GroupConnected S := by
  induction h with
  | single h =>
    obtain ⟨_,_,_,_,_,_,_,_,_,hc⟩ := memBlock h
    exact hc
  | @append S T a b c n hS hT _ _ ih =>
    have hcT : M.GroupConnected T := by
      obtain ⟨_,_,_,_,_,_,_,_,_,hc⟩ := memBlock hT
      exact hc
    exact currentGroupConnected_union M ih hcT (chain_joints_memΓ hS).2 (memBlock hT).2.1

theorem chain_endpoint_lowerΓ {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : FinalCount.Src.Chain γF M S a b n) :
    1 ≤ M.outIn S a ∧ 1 ≤ M.inIn S a ∧ 1 ≤ M.outIn S b ∧ 1 ≤ M.inIn S b := by
  induction h with
  | single h =>
    obtain ⟨_,_,_,_,hoa,hia,hob,hib,_,_⟩ := memBlock h
    omega
  | @append S T a b c n _ hT _ _ ih =>
    have ho := Mole.outIn_mono M (show S ⊆ S ∪ T from subset_union_left) a
    have hi := Mole.inIn_mono M (show S ⊆ S ∪ T from subset_union_left) a
    have hoc := Mole.outIn_mono M (show T ⊆ S ∪ T from subset_union_right) c
    have hic := Mole.inIn_mono M (show T ⊆ S ∪ T from subset_union_right) c
    obtain ⟨_,_,_,_,_,_,hot,hit,_,_⟩ := memBlock hT
    omega

/-- The shared singleton contains no bond, because a connected block has no loop at either joint. -/
theorem chain_append_intersection_degreeΓ {M : Molecule V D} {S T : Finset V} {b c : V}
    (hT : FinalCount.Src.IsSomeVine γF M T b c) (hi : S ∩ T = {b}) : M.degIn (S ∩ T) b = 0 := by
  have hd := (isBlock_iff_degree_connected _ _ _ _).mp (memBlock hT)
  rw [hi]
  apply Mole.degIn_singleton_eq_zero M
  intro x hx
  have h := Mole.connected_block_no_joint_loop M (memBlock hT) hd.2 (Or.inl hx)
  simpa only [hx] using h

/-- Every non-endpoint of the actual chain saturates its four ambient incidences. -/
theorem chain_interior_degreeΓ (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} {n : ℕ} (h : FinalCount.Src.Chain γF M S a b n) :
    ∀ v ∈ S, v ≠ a → v ≠ b → M.degIn S v = 4 := by
  induction h with
  | single h =>
    exact ((isBlock_iff_degree_connected _ _ _ _).mp (memBlock h)).1.2.2.2.2.2.2.2.2
  | @append S T a b c n hS hT hi _ ih =>
    have hdT := ((isBlock_iff_degree_connected _ _ _ _).mp (memBlock hT)).1
    intro v hv hva hvc
    have hvM := (union_subset (chain_atoms_subsetΓ hS) hdT.1) hv
    have hbound := (Mole.degIn_le_deg M (S ∪ T) v).trans (Mole.deg_le_four M hM hvM)
    by_cases hvb : v = b
    · subst v
      have hlo := chain_endpoint_lowerΓ hS
      have hsum := Mole.outIn_add_inIn M S b
      have hdegT := (Mole.block_joint_degrees M (memBlock hT)).1
      have hadd := Mole.degIn_union_add_inter M S T (chain_joints_memΓ hS).2 hdT.2.1
      rw [chain_append_intersection_degreeΓ hT hi] at hadd
      omega
    · rcases mem_union.mp hv with hv | hv
      · have hd := ih v hv hva hvb
        have hm := Mole.degIn_mono M (show S ⊆ S ∪ T from subset_union_left) v
        omega
      · have hd := hdT.2.2.2.2.2.2.2.2 v hv hvb hvc
        have hm := Mole.degIn_mono M (show T ⊆ S ∪ T from subset_union_right) v
        omega

/-- The defining source VC block premise gives a current connected prefix block. -/
theorem chain_prefix_currentBlockΓ (M : Molecule V D) (hM : M.IsMolecule)
    {S T : Finset V} {a b c : V} {n : ℕ} (hS : FinalCount.Src.Chain γF M S a b n)
    (hT : FinalCount.Src.IsSomeVine γF M T b c) (hi : S ∩ T = {b})
    (hU : M.IsBlock (S ∪ T) a c) : M.IsBlock S a b := by
  have hlo := chain_endpoint_lowerΓ hS
  have hmem := chain_joints_memΓ hS
  have hdegT := ((isBlock_iff_degree_connected _ _ _ _).mp (memBlock hT)).1
  have hdegU := ((isBlock_iff_degree_connected _ _ _ _).mp hU).1
  have huaout := hdegU.2.2.2.2.1
  have huain := hdegU.2.2.2.2.2.1
  have hbU : b ∈ S ∪ T := mem_union_left _ hmem.2
  have hb4 := hdegU.2.2.2.2.2.2.2.2 b hbU (Ne.symm (chain_joints_neΓ hS)) hdegT.2.2.2.1
  have hadd := Mole.degIn_union_add_inter M S T hmem.2 hdegT.2.1
  rw [chain_append_intersection_degreeΓ hT hi] at hadd
  have hb2 := (Mole.block_joint_degrees M (memBlock hT)).1
  have hsum := Mole.outIn_add_inIn M S b
  have hoa := Mole.outIn_mono M (show S ⊆ S ∪ T from subset_union_left) a
  have hia := Mole.inIn_mono M (show S ⊆ S ∪ T from subset_union_left) a
  refine (isBlock_iff_degree_connected M S a b).mpr ⟨?_,?_⟩
  · refine ⟨chain_atoms_subsetΓ hS,hmem.1,hmem.2,chain_joints_neΓ hS,?_,?_,?_,?_,
      chain_interior_degreeΓ M hM hS⟩ <;> omega
  · exact (groupConnected_iff_mole M S ⟨a,hmem.1⟩).mp (chain_current_connectedΓ hS)

/-- A suffix chain of a block over a prefix block is a current connected block (main's
`VineEstS4.chain_suffix_currentBlock`, `VineEstS4/Sp17Suffix.lean`). -/
theorem chain_suffix_currentBlockΓ (M : Molecule V D) (hM : M.IsMolecule)
    {S T : Finset V} {a b c : V} {n : ℕ} (hS : M.IsBlock S a b) (hT : FinalCount.Src.Chain γF M T b c n)
    (hi : S ∩ T = {b}) (hU : M.IsBlock (S ∪ T) a c) : M.IsBlock T b c := by
  have hlo := chain_endpoint_lowerΓ hT
  have hmem := chain_joints_memΓ hT
  have hdegS := ((isBlock_iff_degree_connected _ _ _ _).mp hS).1
  have hdegU := ((isBlock_iff_degree_connected _ _ _ _).mp hU).1
  have hbc := chain_joints_neΓ hT
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
  · refine ⟨chain_atoms_subsetΓ hT, hmem.1, hmem.2, hbc, ?_, ?_, ?_, ?_, chain_interior_degreeΓ M hM hT⟩ <;> omega
  · exact (groupConnected_iff_mole M T ⟨b, hmem.1⟩).mp (chain_current_connectedΓ hT)

end WaveTurbulence.GammaLow.Famb.VineEstS2
