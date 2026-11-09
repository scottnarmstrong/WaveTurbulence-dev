/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.HFree
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.HFree.BadVine
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.HFree
-- L5b port of `WaveTurbulence.Foundations.VineEst.HFree.BadVine` (sha256 d82096eb4c719f07…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # W2-HFREE (2): clause (d) per vine

`bad_d_vine` is the proof of `VineEstS3.bad_d` (BadClauseD.lean, sha256 in COPIED-SHA256SUMS) with the premise `CoreVinesNoTwist`
(used only at the vine `i` and its anchor placement) replaced by the instance for the single vine `i`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W2 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS4
  VineParamContract TTree RegRed WaveTurbulence.Reg.Skeleton Reg Links
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}
variable (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)
variable (RD : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
variable (hLayer : IsLayering (RD.garden hG) layer)

include hLayer in
/-- **Clause (d), per vine** (`VineEstS3.bad_d` with the global premise `CoreVinesNoTwist` replaced by its instance at the vine `i`).  A bad vine failing clause (a) has a row of its block with `max (g, g') ≥ 1`. -/
theorem bad_d_vineΓ (i : Fin n)
    (hno : ∀ P : CorePlacement G, IsPlacementAt G (assemblyPieceAtΓ B i).atoms (assemblyPieceAtΓ B i).lower P →
      ¬ (SourceLayerEligible (layeredReconstruction RD hG layer hLayer) RD hG (RD.garden_decodes hG) P
        (assemblyPieceAtΓ B i).label (assemblyPieceAtΓ B i).atoms (assemblyPieceAtΓ B i).upper ∧
      CohOn (layeredReconstruction RD hG layer hLayer)
        ((RD.tree P.lower).linksAt (nodeSign G.sig P.lower.1) (inflatedPosition G RD.tree P.lower.toNode)) ∧
      CohOn (layeredReconstruction RD hG layer hLayer)
        ((RD.couple (pairOfLeaf G hG P.retained)).linksAt
          (inflatedPosition G RD.tree ((pairOfLeaf G hG P.retained).firstLeaf hG).toNode)
          (inflatedPosition G RD.tree ((pairOfLeaf G hG P.retained).secondLeaf hG).toNode))))
    (hbad : (assemblyPieceAtΓ B i).label.IsBad = true) (hnA : ¬ AClauseΓ hM9 B RD hG layer i) :
    ∃ v : (assemblyShapeΓ hM9 B).VIdx, v.1 = i ∧
      1 ≤ max (rowCoupleGΓ hM9 B RD hG layer hLayer v) (rowTreeGΓ hM9 B RD hG layer hLayer v) := by
  have hCL := assemblyPiece_clΓ B i
  have hV := (assemblyPieceAtΓ B i).isVine_label_of_bad hM9 (Mole.garden_isMolecule G) hbad
  have key : IsCoreCLVine G (assemblyPieceAtΓ B i).label (assemblyPieceAtΓ B i).atoms (assemblyPieceAtΓ B i).upper
        (assemblyPieceAtΓ B i).lower ∧
      ∀ P' : CorePlacement G, IsPlacementAt G (assemblyPieceAtΓ B i).atoms (assemblyPieceAtΓ B i).lower P' →
        SourceLayerEligible (layeredReconstruction RD hG layer hLayer) RD hG (RD.garden_decodes hG) P'
          (assemblyPieceAtΓ B i).label (assemblyPieceAtΓ B i).atoms (assemblyPieceAtΓ B i).upper := by
    rcases (Vine.isBad_iff _).mp hbad with hI | hII
    · exact ⟨⟨hV, hCL, Or.inl hI⟩, fun _ _ => Or.inl hI⟩
    · have hcore : ¬ ∃ p ∈ (assemblyPieceAtΓ B i).atoms, ∃ q ∈ (assemblyPieceAtΓ B i).atoms,
          Molecpl.IsTypeIIE G (assemblyPieceAtΓ B i).upper (assemblyPieceAtΓ B i).lower p q :=
        fun h => hnA (aClause_typeIIΓ hM9 B RD hG layer hLayer i hII (Or.inl h))
      have helig : ∃ R' : Molecpl.EndRungData G.molecule (assemblyPieceAtΓ B i).atoms (assemblyPieceAtΓ B i).upper
          (assemblyPieceAtΓ B i).lower,
          atomLayer RD hG layer (assemblyPieceAtΓ B i).lower ≤
            min (atomLayer RD hG layer R'.left) (atomLayer RD hG layer R'.right) := by
        by_contra h
        exact hnA (aClause_typeIIΓ hM9 B RD hG layer hLayer i hII (Or.inr h))
      refine ⟨⟨hV, hCL, Or.inr ⟨hII, hcore⟩⟩, fun P' hP' => Or.inr ⟨hII, ?_⟩⟩
      obtain ⟨R', hR'⟩ := helig
      have trans : ∀ b' : GBranch G.tree, b' = (assemblyPieceAtΓ B i).lower →
          ∃ R3 : Molecpl.EndRungData G.molecule (assemblyPieceAtΓ B i).atoms (assemblyPieceAtΓ B i).upper b',
            atomLayer RD hG layer b' ≤ min (atomLayer RD hG layer R3.left) (atomLayer RD hG layer R3.right) := by
        intro b' h; subst h; exact ⟨R', hR'⟩
      exact trans P'.lower hP'.1
  obtain ⟨hcore, helig⟩ := key
  have hsome := vineAnchor_isSomeΓ B hG i hcore
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨P', hP', hpair⟩ := vineAnchor_specΓ hG B i p hp
  have hnn := hno P' hP'
  have hel := helig P' hP'
  by_cases hT : CohOn (layeredReconstruction RD hG layer hLayer)
      ((RD.tree P'.lower).linksAt (nodeSign G.sig P'.lower.1) (inflatedPosition G RD.tree P'.lower.toNode))
  · have hQ : ¬ CohOn (layeredReconstruction RD hG layer hLayer)
        ((RD.couple (pairOfLeaf G hG P'.retained)).linksAt
          (inflatedPosition G RD.tree ((pairOfLeaf G hG P'.retained).firstLeaf hG).toNode)
          (inflatedPosition G RD.tree ((pairOfLeaf G hG P'.retained).secondLeaf hG).toNode)) :=
      fun hQ => hnn ⟨hel, hT, hQ⟩
    obtain ⟨v, hv1, hv⟩ := assemblyPairOf_anchorΓ hM9 B hG i p hp
    refine ⟨v, hv1, le_max_of_le_left ?_⟩
    apply one_le_rowCoupleG_of_not_cohOnΓ hM9 B RD hG layer hLayer v
    rw [hv, hpair]
    exact hQ
  · obtain ⟨v, hv1, hv2⟩ := exists_tree_rowΓ hM9 B i
    refine ⟨v, hv1, le_max_of_le_right ?_⟩
    apply one_le_rowTreeG_of_not_cohOnΓ hM9 B RD hG layer hLayer v
    have e : (assemblyBranchOfΓ hM9 B v).1 = P'.lower := hv2.trans hP'.1.symm
    rw [e]
    exact hT

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
