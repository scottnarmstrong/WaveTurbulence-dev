/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.ChainNoCross
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLRegionData

/-! # Actual CL parent patterns of a source-chain split -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree Finset RegRed
variable {w : ℕ} {G : Garden w} {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}

/-- A prefix and terminal vine inherit their ordered CL geometry from the
actual whole CL block. This does not assume ingredient parent patterns. -/
theorem clBlockConcat_parentPatterns (hS : G.molecule.IsBlock S a b)
    (hT : G.molecule.IsBlock T b c) (hi : S ∩ T = {b})
    (hU : G.molecule.IsBlock (S ∪ T) a c) (R : CLRegionData G (S ∪ T) a c) :
    Mole.CLParentPattern G S a b ∧ Mole.CLParentPattern G T b c := by
  have hS' := hS
  have hT' := hT
  have hU' := hU
  have hcS : c ∉ S := by
    intro hc
    have he := mem_inter.mpr ⟨hc,hT'.2.2.1⟩
    rw [hi,mem_singleton] at he
    exact hT'.2.2.2.1 he.symm
  have hcT : Mole.InternalParent G T c := by
    obtain ⟨hn,hp⟩ := R.parentPattern.2
    refine ⟨hn,?_⟩
    rcases mem_union.mp hp with hp | hp
    · by_cases ht : GNode.parent c.toNode hn ∈ T
      · exact ht
      · exact (block_concat_noCross G.molecule (Mole.garden_isMolecule G) hS hT hi hU
          _ hp ht c hT'.2.2.1 hcS ⟨.inl (⟨c,hn⟩,true),rfl,rfl⟩).elim
    · exact hp
  have hbT : ¬ Mole.InternalParent G T b := by
    rcases Mole.block_parent_dichotomy G hT' with h | h | h
    · exact (h.2 hcT).elim
    · exact h.1
    · exact h.1
  have hbS : Mole.InternalParent G S b := by
    have hbU : b ∈ S ∪ T := mem_union_left _ hS'.2.2.1
    obtain ⟨hn,hp⟩ := Mole.block_interior_has_parent G hU' hbU (Ne.symm hS'.2.2.2.1) hT'.2.2.2.1
    refine ⟨hn,?_⟩
    rcases mem_union.mp hp with hp | hp
    · exact hp
    · exact (hbT ⟨hn,hp⟩).elim
  have haS : ¬ Mole.InternalParent G S a := by
    rintro ⟨hn,hp⟩
    exact R.parentPattern.1 ⟨hn,mem_union_left _ hp⟩
  exact ⟨⟨haS,hbS⟩,⟨hbT,hcT⟩⟩

/-- Current source-chain prefix data are constructed from the actual
connected block and the proved split parent pattern. -/
noncomputable def clChainPrefixRegion {n : ℕ} (hS : Vine.Chain G.molecule S a b n)
    {X : VineType} (hT : G.molecule.IsVine X T b c) (hi : S ∩ T = {b})
    (hU : G.molecule.IsBlock (S ∪ T) a c) (R : CLRegionData G (S ∪ T) a c) :
    CLRegionData G S a b := by
  let hB := chain_prefix_currentBlock G.molecule (Mole.garden_isMolecule G) hS hT hi hU
  exact clRegionData G hB (clBlockConcat_parentPatterns hB hT.1 hi hU R).1

end WaveTurbulence.VineEstS2
