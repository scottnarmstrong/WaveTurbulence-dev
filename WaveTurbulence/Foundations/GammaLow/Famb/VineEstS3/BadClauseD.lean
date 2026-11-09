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
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS3.BadClauseD
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.BadClauseA
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.IncohDict
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS3.BadClauseD` (sha256 f3fc2a0e2b155a26…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

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
namespace WaveTurbulence.GammaLow.Famb.VineEstS3
open WaveTurbulence.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS3
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.Twist WaveTurbulence.LFTwist VineParamContract TTree RegRed WaveTurbulence.GammaLow.Famb.VineEstS2
  WaveTurbulence.Reg.Skeleton Reg Links
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}
variable (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)
variable (RD : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
variable (hLayer : IsLayering (RD.garden hG) layer)

omit hM9 in
theorem lower_mem_interiorΓ (i : Fin n) : (assemblyPieceAtΓ B i).lower ∈ clInteriorBranches R := by
  have hU : (assemblyPieceAtΓ B i).lower ∈ U := assemblyPiece_subsetΓ B i (assemblyPieceAtΓ B i).isBlock.2.2.1
  refine Finset.mem_erase.mpr ⟨?_, hU⟩
  intro hba
  have hupU : (assemblyPieceAtΓ B i).upper ∈ U := assemblyPiece_subsetΓ B i (assemblyPieceAtΓ B i).isBlock.2.1
  have h1 := Mole.block_one_root_descendants G B.isBlock R.parentPattern.1 R.parentPattern.2 hupU
  have h2 := piece_upper_len_ltΓ B i
  have h3 := h1.2.length_le
  rw [hba] at h2
  change a.1.2.length ≤ (assemblyPieceAtΓ B i).upper.1.2.length at h3
  omega

theorem vineOf_lowerΓ (i : Fin n) : vineOfΓ hM9 B ⟨(assemblyPieceAtΓ B i).lower, lower_mem_interiorΓ B i⟩ = i := by
  have hy : (assemblyPieceAtΓ B i).lower ∈ (assemblyPieceAtΓ B i).atoms := (assemblyPieceAtΓ B i).isBlock.2.2.1
  rcases vineOf_of_mem_atomsΓ hM9 B i ⟨(assemblyPieceAtΓ B i).lower, lower_mem_interiorΓ B i⟩ hy with
    ⟨_, h⟩ | ⟨h, _⟩
  · exact h
  · exact absurd h.symm (assemblyPieceAtΓ B i).isBlock.2.2.2.1

theorem exists_tree_rowΓ (i : Fin n) :
    ∃ v : (assemblyShapeΓ hM9 B).VIdx, v.1 = i ∧
      (assemblyBranchOfΓ hM9 B v).1 = (assemblyPieceAtΓ B i).lower := by
  let z : ↥(clInteriorBranches R) := ⟨(assemblyPieceAtΓ B i).lower, lower_mem_interiorΓ B i⟩
  refine ⟨assemblyBranchBijΓ hM9 B z, Fin.ext ?_, ?_⟩
  · rw [assemblyBranchBij_fstΓ]
    exact congrArg Fin.val (vineOf_lowerΓ hM9 B i)
  · have : assemblyBranchOfΓ hM9 B (assemblyBranchBijΓ hM9 B z) = z := by
      apply (assemblyBranchBijΓ hM9 B).injective
      rw [assemblyBranchBij_assemblyBranchOfΓ]
    rw [this]

omit hM9 in
theorem pairOfLeaf_mem_regionalΓ (i : Fin n) (ℓ : GLeaf G.tree)
    (h : Mole.IsInternalLeaf G (assemblyPieceAtΓ B i).atoms ℓ) : pairOfLeaf G hG ℓ ∈ clRegionalPairs hG U := by
  classical
  have h1 : Mole.IsInternalLeaf G U ℓ := internalLeaf_mono (assemblyPiece_subsetΓ B i) ℓ h
  unfold clRegionalPairs
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  rcases firstLeaf_pairOfLeaf hG ℓ with e | e
  · rw [e]; exact h1
  · rw [e]; exact (Mole.internal_leaf_pair_iff G U ℓ).mpr h1

omit hM9 in
theorem vineAnchor_isSomeΓ (i : Fin n)
    (hcore : IsCoreCLVine G (assemblyPieceAtΓ B i).label (assemblyPieceAtΓ B i).atoms (assemblyPieceAtΓ B i).upper
      (assemblyPieceAtΓ B i).lower) : (vineAnchorΓ hG B i).isSome = true := by
  classical
  obtain ⟨P0, hP0, hint⟩ := core_placement_internal G hcore
  unfold vineAnchorΓ
  rw [dif_pos ⟨P0, hP0, pairOfLeaf_mem_regionalΓ B hG i P0.retained hint⟩]
  rfl

end WaveTurbulence.GammaLow.Famb.VineEstS3
