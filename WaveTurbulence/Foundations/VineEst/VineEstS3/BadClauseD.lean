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

/-- **TARGET Step 3, case premise (L1841).**  No core vine of the chain satisfies the assumptions of Definition
`lftwist`: for every core vine piece and every selected placement at it, the layer eligibility and the coherence of
`T_{u2}` and `Q_{(u23,u0)}` do not all hold. -/
def CoreVinesNoTwist : Prop :=
  ∀ (i : Fin n) (P : CorePlacement G),
    IsCoreCLVine G (assemblyPieceAt B i).vineType (assemblyPieceAt B i).atoms (assemblyPieceAt B i).upper
      (assemblyPieceAt B i).lower →
    IsPlacementAt G (assemblyPieceAt B i).atoms (assemblyPieceAt B i).lower P →
    ¬ (SourceLayerEligible (layeredReconstruction RD hG layer hLayer) RD hG (RD.garden_decodes hG) P
        (assemblyPieceAt B i).vineType (assemblyPieceAt B i).atoms (assemblyPieceAt B i).upper ∧
      CohOn (layeredReconstruction RD hG layer hLayer)
        ((RD.tree P.lower).linksAt (nodeSign G.sig P.lower.1) (inflatedPosition G RD.tree P.lower.toNode)) ∧
      CohOn (layeredReconstruction RD hG layer hLayer)
        ((RD.couple (pairOfLeaf G hG P.retained)).linksAt
          (inflatedPosition G RD.tree ((pairOfLeaf G hG P.retained).firstLeaf hG).toNode)
          (inflatedPosition G RD.tree ((pairOfLeaf G hG P.retained).secondLeaf hG).toNode)))

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

include hLayer in
/-- **Clause (d).**  A bad vine failing clause (a) has a row of its block with `max (g, g') ≥ 1`. -/
theorem bad_d (hno : CoreVinesNoTwist B RD hG layer hLayer) (i : Fin n)
    (hbad : (assemblyPieceAt B i).vineType.IsBad = true) (hnA : ¬ AClause hM9 B RD hG layer i) :
    ∃ v : (assemblyShape hM9 B).VIdx, v.1 = i ∧
      1 ≤ max (rowCoupleG hM9 B RD hG layer hLayer v) (rowTreeG hM9 B RD hG layer hLayer v) := by
  have hCL := assemblyPiece_cl B i
  have hV := (assemblyPieceAt B i).vine
  have key : IsCoreCLVine G (assemblyPieceAt B i).vineType (assemblyPieceAt B i).atoms (assemblyPieceAt B i).upper
        (assemblyPieceAt B i).lower ∧
      ∀ P' : CorePlacement G, IsPlacementAt G (assemblyPieceAt B i).atoms (assemblyPieceAt B i).lower P' →
        SourceLayerEligible (layeredReconstruction RD hG layer hLayer) RD hG (RD.garden_decodes hG) P'
          (assemblyPieceAt B i).vineType (assemblyPieceAt B i).atoms (assemblyPieceAt B i).upper := by
    rcases (Vine.isBad_iff _).mp hbad with hI | hII
    · exact ⟨⟨hV, hCL, Or.inl hI⟩, fun _ _ => Or.inl hI⟩
    · have hcore : ¬ ∃ p ∈ (assemblyPieceAt B i).atoms, ∃ q ∈ (assemblyPieceAt B i).atoms,
          Molecpl.IsTypeIIE G (assemblyPieceAt B i).upper (assemblyPieceAt B i).lower p q :=
        fun h => hnA (aClause_typeII hM9 B RD hG layer hLayer i hII (Or.inl h))
      have helig : ∃ R' : Molecpl.EndRungData G.molecule (assemblyPieceAt B i).atoms (assemblyPieceAt B i).upper
          (assemblyPieceAt B i).lower,
          atomLayer RD hG layer (assemblyPieceAt B i).lower ≤
            min (atomLayer RD hG layer R'.left) (atomLayer RD hG layer R'.right) := by
        by_contra h
        exact hnA (aClause_typeII hM9 B RD hG layer hLayer i hII (Or.inr h))
      refine ⟨⟨hV, hCL, Or.inr ⟨hII, hcore⟩⟩, fun P' hP' => Or.inr ⟨hII, ?_⟩⟩
      obtain ⟨R', hR'⟩ := helig
      have trans : ∀ b' : GBranch G.tree, b' = (assemblyPieceAt B i).lower →
          ∃ R3 : Molecpl.EndRungData G.molecule (assemblyPieceAt B i).atoms (assemblyPieceAt B i).upper b',
            atomLayer RD hG layer b' ≤ min (atomLayer RD hG layer R3.left) (atomLayer RD hG layer R3.right) := by
        intro b' h; subst h; exact ⟨R', hR'⟩
      exact trans P'.lower hP'.1
  obtain ⟨hcore, helig⟩ := key
  have hsome := vineAnchor_isSome B hG i hcore
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨P', hP', hpair⟩ := vineAnchor_spec hG B i p hp
  have hnn := hno i P' hcore hP'
  have hel := helig P' hP'
  by_cases hT : CohOn (layeredReconstruction RD hG layer hLayer)
      ((RD.tree P'.lower).linksAt (nodeSign G.sig P'.lower.1) (inflatedPosition G RD.tree P'.lower.toNode))
  · have hQ : ¬ CohOn (layeredReconstruction RD hG layer hLayer)
        ((RD.couple (pairOfLeaf G hG P'.retained)).linksAt
          (inflatedPosition G RD.tree ((pairOfLeaf G hG P'.retained).firstLeaf hG).toNode)
          (inflatedPosition G RD.tree ((pairOfLeaf G hG P'.retained).secondLeaf hG).toNode)) :=
      fun hQ => hnn ⟨hel, hT, hQ⟩
    obtain ⟨v, hv1, hv⟩ := assemblyPairOf_anchor hM9 B hG i p hp
    refine ⟨v, hv1, le_max_of_le_left ?_⟩
    apply one_le_rowCoupleG_of_not_cohOn hM9 B RD hG layer hLayer v
    rw [hv, hpair]
    exact hQ
  · obtain ⟨v, hv1, hv2⟩ := exists_tree_row hM9 B i
    refine ⟨v, hv1, le_max_of_le_right ?_⟩
    apply one_le_rowTreeG_of_not_cohOn hM9 B RD hG layer hLayer v
    have e : (assemblyBranchOf hM9 B v).1 = P'.lower := hv2.trans hP'.1.symm
    rw [e]
    exact hT

end WaveTurbulence.VineEstS3
