/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.RS.Base
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainBlock
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
import Mathlib.Tactic
/-! # H-RS: facts about the low family used by the H-RS layer (L6-HRS, hand-written)

Re-exports `RS/Base.lean` (no cut atom, size, `vine_in_terminal_split` for a family member) and adds
* `chain_prefix_isBlock`: main's `Vine.chain_prefix_isBlock` with the terminal ingredient a family member (any `γ`),
  from the H-MS chain lemmas (sha256 of main's source in `H/RS/COPIED-SHA256SUMS`). No named input is used. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H.RS
open Finset WaveTurbulence

universe u v

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Main's `Vine.chain_prefix_isBlock` with the terminal ingredient a member of the family: in an actual block,
removing the terminal ingredient of a chain leaves an actual prefix block. -/
theorem chain_prefix_isBlock {γ : ℝ} (M : Molecule V D) (hM : M.IsMolecule)
    {S T : Finset V} {a b c : V} {n : ℕ} (hS : Src.Chain Src.γL M S a b n)
    (hT : Src.IsSomeVine γ M T b c) (hi : S ∩ T = {b})
    (hU : M.IsBlock (S ∪ T) a c) : M.IsBlock S a b := by
  have hTB := hT.block
  have hmem := H.chain_joints_mem hS
  have hlo := H.chain_endpoint_lower hS
  have hla := Vine.oriented_degree_mono M (show S ⊆ S ∪ T from subset_union_left) a
  have hloop := Vine.connected_degree_two_no_loop M (vconnected hT)
    hTB.2.1 hTB.2.2.1 hTB.2.2.2.1 (Mole.block_joint_degrees M hTB).1
  have hob := Vine.group_filtered_card_union_le M hi hloop b (fun d => M.out d = true)
  have hib := Vine.group_filtered_card_union_le M hi hloop b (fun d => M.out d = false)
  change M.outIn S b + M.outIn T b ≤ M.outIn (S ∪ T) b at hob
  change M.inIn S b + M.inIn T b ≤ M.inIn (S ∪ T) b at hib
  have hbo := (Vine.outIn_le_outdeg M (S ∪ T) b).trans (hM.1 b (hTB.1 hTB.2.1)).1
  have hbi := (Vine.inIn_le_indeg M (S ∪ T) b).trans (hM.1 b (hTB.1 hTB.2.1)).2
  obtain ⟨_hTU, _ha, _hc, _hac, hoa, hia, _hoc, _hic, _hint⟩ := hU
  obtain ⟨_hT, _hb, _hc, _hbc, hot, hit, _hot', _hit', _hint'⟩ := hTB
  refine ⟨H.chain_atoms_subset hS, hmem.1, hmem.2, H.chain_joints_ne hS,
    by omega, by omega, by omega, by omega, H.chain_interior_degree M hM hS, ?_⟩
  intro p hp q hq
  have hmono : (Mole.induced M S).Adj ≤
      fun x y => ∃ z, M.InGroup S z ∧ M.atom z = x ∧ M.atom (M.mate z) = y := by
    intro x y hxy
    obtain ⟨z, hx, hy⟩ := hxy
    exact ⟨z.1, z.2, hx, hy⟩
  exact Relation.EqvGen.mono hmono p q (H.chain_connected hS p hp q hq)

end WaveTurbulence.GammaLow.FinalCount.H.RS
