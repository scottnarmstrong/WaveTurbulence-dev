/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.HFree

/-! # W2-HFREE (2): clause (d) per vine

`bad_d_vine` is the proof of `VineEstS3.bad_d` (BadClauseD.lean, sha256 in COPIED-SHA256SUMS) with the premise `CoreVinesNoTwist`
(used only at the vine `i` and its anchor placement) replaced by the instance for the single vine `i`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  VineParamContract TTree RegRed WaveTurbulence.Reg.Skeleton Reg Links
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}
variable (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
variable (RD : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
variable (hLayer : IsLayering (RD.garden hG) layer)

include hLayer in
/-- **Clause (d), per vine** (`VineEstS3.bad_d` with the global premise `CoreVinesNoTwist` replaced by its instance at the vine `i`).  A bad vine failing clause (a) has a row of its block with `max (g, g') ≥ 1`. -/
theorem bad_d_vine (i : Fin n)
    (hno : ∀ P : CorePlacement G, IsPlacementAt G (assemblyPieceAt B i).atoms (assemblyPieceAt B i).lower P →
      ¬ (SourceLayerEligible (layeredReconstruction RD hG layer hLayer) RD hG (RD.garden_decodes hG) P
        (assemblyPieceAt B i).vineType (assemblyPieceAt B i).atoms (assemblyPieceAt B i).upper ∧
      CohOn (layeredReconstruction RD hG layer hLayer)
        ((RD.tree P.lower).linksAt (nodeSign G.sig P.lower.1) (inflatedPosition G RD.tree P.lower.toNode)) ∧
      CohOn (layeredReconstruction RD hG layer hLayer)
        ((RD.couple (pairOfLeaf G hG P.retained)).linksAt
          (inflatedPosition G RD.tree ((pairOfLeaf G hG P.retained).firstLeaf hG).toNode)
          (inflatedPosition G RD.tree ((pairOfLeaf G hG P.retained).secondLeaf hG).toNode))))
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
  have hnn := hno P' hP'
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


end WaveTurbulence.VineEstS5C.P4.W2
