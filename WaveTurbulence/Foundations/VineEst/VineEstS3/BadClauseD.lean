/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.BadClauseA
public import WaveTurbulence.Foundations.VineEst.VineEstS3.BadPlacement
public import WaveTurbulence.Foundations.VineEst.VineEstS3.RowAlignRows
public import WaveTurbulence.Foundations.VineEst.VineEstS3.IncohDict
public import WaveTurbulence.Foundations.Molecule.LFTwist.SourceExpandedUnit
public import WaveTurbulence.Foundations.Molecule.VineTemplates

/-! # BadClause, part D: clause (d) of `sumint` from the failure of the twist assumptions (TARGET L1841-L1847)

`CoreVinesNoTwist` is the case premise of TARGET Step 3 (L1841): no core vine piece satisfies the assumptions of
Definition `lftwist` (source layer eligibility with both `T_{u2}` and `Q_{(u23,u0)}` coherent).
`bad_d`: for a bad vine `i` with `¬ AClause i`, some row of block `i` has `max (g, g') ≥ 1`: the vine is core and
layer-eligible (else `aClause_typeII`), so one of the two objects is incoherent, and the aligned rows
(`RowAlignRows`) carry the tree at the lower joint and the anchor pair in block `i`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.Twist WaveTurbulence.LFTwist VineParamContract TTree RegRed
  WaveTurbulence.Reg.Skeleton Reg Links
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}
variable (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
variable (RD : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
variable (hLayer : IsLayering (RD.garden hG) layer)

omit hM9 in
theorem lower_mem_interior (i : Fin n) : (assemblyPieceAt B i).lower ∈ clInteriorBranches R := by
  have hU : (assemblyPieceAt B i).lower ∈ U := assemblyPiece_subset B i (assemblyPieceAt B i).vine.1.2.2.1
  refine Finset.mem_erase.mpr ⟨?_, hU⟩
  intro hba
  have hupU : (assemblyPieceAt B i).upper ∈ U := assemblyPiece_subset B i (assemblyPieceAt B i).vine.1.2.1
  have h1 := Mole.block_one_root_descendants G B.isBlock R.parentPattern.1 R.parentPattern.2 hupU
  have h2 := piece_upper_len_lt B i
  have h3 := h1.2.length_le
  rw [hba] at h2
  change a.1.2.length ≤ (assemblyPieceAt B i).upper.1.2.length at h3
  omega

theorem vineOf_lower (i : Fin n) : vineOf hM9 B ⟨(assemblyPieceAt B i).lower, lower_mem_interior B i⟩ = i := by
  have hy : (assemblyPieceAt B i).lower ∈ (assemblyPieceAt B i).atoms := (assemblyPieceAt B i).vine.1.2.2.1
  rcases vineOf_of_mem_atoms hM9 B i ⟨(assemblyPieceAt B i).lower, lower_mem_interior B i⟩ hy with
    ⟨_, h⟩ | ⟨h, _⟩
  · exact h
  · exact absurd h.symm (assemblyPieceAt B i).vine.1.2.2.2.1

theorem exists_tree_row (i : Fin n) :
    ∃ v : (assemblyShape hM9 B).VIdx, v.1 = i ∧
      (assemblyBranchOf hM9 B v).1 = (assemblyPieceAt B i).lower := by
  let z : ↥(clInteriorBranches R) := ⟨(assemblyPieceAt B i).lower, lower_mem_interior B i⟩
  refine ⟨assemblyBranchBij hM9 B z, Fin.ext ?_, ?_⟩
  · rw [assemblyBranchBij_fst]
    exact congrArg Fin.val (vineOf_lower hM9 B i)
  · have : assemblyBranchOf hM9 B (assemblyBranchBij hM9 B z) = z := by
      apply (assemblyBranchBij hM9 B).injective
      rw [assemblyBranchBij_assemblyBranchOf]
    rw [this]

theorem firstLeaf_pairOfLeaf (ℓ : GLeaf G.tree) :
    (pairOfLeaf G hG ℓ).firstLeaf hG = ℓ ∨ (pairOfLeaf G hG ℓ).firstLeaf hG = G.pair ℓ := by
  unfold pairOfLeaf SourcePair.firstLeaf sourcePairAt
  by_cases h : nodeSign G.sig ℓ.1 = 1
  · left; simp only [h, if_true]; rfl
  · right; simp only [h, if_false]; rfl

omit hM9 in
theorem pairOfLeaf_mem_regional (i : Fin n) (ℓ : GLeaf G.tree)
    (h : Mole.IsInternalLeaf G (assemblyPieceAt B i).atoms ℓ) : pairOfLeaf G hG ℓ ∈ clRegionalPairs hG U := by
  classical
  have h1 : Mole.IsInternalLeaf G U ℓ := internalLeaf_mono (assemblyPiece_subset B i) ℓ h
  unfold clRegionalPairs
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  rcases firstLeaf_pairOfLeaf hG ℓ with e | e
  · rw [e]; exact h1
  · rw [e]; exact (Mole.internal_leaf_pair_iff G U ℓ).mpr h1

omit hM9 in
theorem vineAnchor_isSome (i : Fin n)
    (hcore : IsCoreCLVine G (assemblyPieceAt B i).vineType (assemblyPieceAt B i).atoms (assemblyPieceAt B i).upper
      (assemblyPieceAt B i).lower) : (vineAnchor hG B i).isSome = true := by
  classical
  obtain ⟨P0, hP0, hint⟩ := core_placement_internal G hcore
  unfold vineAnchor
  rw [dif_pos ⟨P0, hP0, pairOfLeaf_mem_regional B hG i P0.retained hint⟩]
  rfl

end WaveTurbulence.VineEstS3
