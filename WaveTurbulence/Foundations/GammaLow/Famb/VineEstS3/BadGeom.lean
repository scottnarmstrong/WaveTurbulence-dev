/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.ChartNormal
public import WaveTurbulence.Foundations.VineEst.VineEstS2.ChainChartIndexing
public import WaveTurbulence.Foundations.Molecule.TypeIIScenarios
public import WaveTurbulence.Foundations.Molecule.CoreVine
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS3.BadGeom
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.ChainChartIndexing
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS3.BadGeom` (sha256 9373c667cb398a58…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # BadClause geometry: the normalized rung `0` of a type-II piece is the end rung

For a CL type-II vine piece `⟨.II, S, a, b, hv⟩` the chosen (normalized) chart has rung `0` equal to the end rung
`{R.left, R.right}` of an `EndRungData R` with `parent b = R.left` (`rung0_typeII`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS3
open WaveTurbulence.VineEstS3
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.Twist VineParamContract TTree RegRed WaveTurbulence.GammaLow.Famb.VineEstS2
variable {w : ℕ} {G : Garden w}

/-- For a CL type-II vine, the normalization of any chart labelled `II` has rung `0` equal to the end rung. -/
theorem rung0_chartΓ {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} {X : VineType} (hX : X = .II)
    (hv : G.molecule.IsVine .II S a b) (hCL : Mole.CLParentPattern G S a b) (C0 : FullVineChart G.molecule X S a b) :
    ∃ (R : Molecpl.EndRungData G.molecule S a b) (hn : b.1.2 ≠ []), GNode.parent b.toNode hn = R.left ∧
      ∃ h0 : 0 < (normalizeChart C0).indexing.shape.m,
        (((normalizeChart C0).indexing.atom ((normalizeChart C0).indexing.shape.xSlot ⟨0, h0⟩)).1 = R.left ∧
          ((normalizeChart C0).indexing.atom ((normalizeChart C0).indexing.shape.ySlot ⟨0, h0⟩)).1 = R.right) ∨
        (((normalizeChart C0).indexing.atom ((normalizeChart C0).indexing.shape.xSlot ⟨0, h0⟩)).1 = R.right ∧
          ((normalizeChart C0).indexing.atom ((normalizeChart C0).indexing.shape.ySlot ⟨0, h0⟩)).1 = R.left) := by
  subst hX
  obtain ⟨R, hn, hp, _⟩ := Molecpl.garden_typeII_local_cases G hv hCL
  refine ⟨R, hn, hp, ?_⟩
  have hadj := exists_adjacent_rung (Mole.garden_isMolecule G) hv.1 R C0
  obtain ⟨h0, hj⟩ := normalizeChart_adj C0 hadj
  exact ⟨h0, adj_pair hv.1 R (normalizeChart C0) ⟨0, h0⟩ hj (xSlot_ne_x0 _ _) (ySlot_ne_x0 _ _)⟩

/-- Piece form of `rung0_typeII` (main): an ingredient labelled `II` is a type-II vine (`isVine_label_of_bad`). -/
theorem rung0_pieceΓ (hM9 : NormalChartSupply γF) (P : ChainPieceΓ γF G.molecule) (hII : P.label = .II)
    (hCL : Mole.CLParentPattern G P.atoms P.upper P.lower) :
    ∃ (R : Molecpl.EndRungData G.molecule P.atoms P.upper P.lower) (hn : P.lower.1.2 ≠ []),
      GNode.parent P.lower.toNode hn = R.left ∧
      ∃ h0 : 0 < (chainPieceChartΓ hM9 (Mole.garden_isMolecule G) P).indexing.shape.m,
        (((chainPieceChartΓ hM9 (Mole.garden_isMolecule G) P).indexing.atom
            ((chainPieceChartΓ hM9 (Mole.garden_isMolecule G) P).indexing.shape.xSlot ⟨0, h0⟩)).1 = R.left ∧
          ((chainPieceChartΓ hM9 (Mole.garden_isMolecule G) P).indexing.atom
            ((chainPieceChartΓ hM9 (Mole.garden_isMolecule G) P).indexing.shape.ySlot ⟨0, h0⟩)).1 = R.right) ∨
        (((chainPieceChartΓ hM9 (Mole.garden_isMolecule G) P).indexing.atom
            ((chainPieceChartΓ hM9 (Mole.garden_isMolecule G) P).indexing.shape.xSlot ⟨0, h0⟩)).1 = R.right ∧
          ((chainPieceChartΓ hM9 (Mole.garden_isMolecule G) P).indexing.atom
            ((chainPieceChartΓ hM9 (Mole.garden_isMolecule G) P).indexing.shape.ySlot ⟨0, h0⟩)).1 = R.left) := by
  have hv := P.isVine_label_of_bad hM9 (Mole.garden_isMolecule G) (by rw [hII]; rfl)
  rw [hII] at hv
  exact rung0_chartΓ hII hv hCL _

end WaveTurbulence.GammaLow.Famb.VineEstS3
