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

/-! # BadClause geometry: the normalized rung `0` of a type-II piece is the end rung

For a CL type-II vine piece `⟨.II, S, a, b, hv⟩` the chosen (normalized) chart has rung `0` equal to the end rung
`{R.left, R.right}` of an `EndRungData R` with `parent b = R.left` (`rung0_typeII`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.Twist VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w}

theorem rung0_typeII (hM9 : VINEPARAM) {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hv : G.molecule.IsVine .II S a b) (hCL : Mole.CLParentPattern G S a b) :
    ∃ (R : Molecpl.EndRungData G.molecule S a b) (hn : b.1.2 ≠ []), GNode.parent b.toNode hn = R.left ∧
      ∃ h0 : 0 < (chainPieceChart hM9 (Mole.garden_isMolecule G) ⟨.II, S, a, b, hv⟩).indexing.shape.m,
        (((chainPieceChart hM9 (Mole.garden_isMolecule G) ⟨.II, S, a, b, hv⟩).indexing.atom
            ((chainPieceChart hM9 (Mole.garden_isMolecule G) ⟨.II, S, a, b, hv⟩).indexing.shape.xSlot ⟨0, h0⟩)).1 = R.left ∧
          ((chainPieceChart hM9 (Mole.garden_isMolecule G) ⟨.II, S, a, b, hv⟩).indexing.atom
            ((chainPieceChart hM9 (Mole.garden_isMolecule G) ⟨.II, S, a, b, hv⟩).indexing.shape.ySlot ⟨0, h0⟩)).1 = R.right) ∨
        (((chainPieceChart hM9 (Mole.garden_isMolecule G) ⟨.II, S, a, b, hv⟩).indexing.atom
            ((chainPieceChart hM9 (Mole.garden_isMolecule G) ⟨.II, S, a, b, hv⟩).indexing.shape.xSlot ⟨0, h0⟩)).1 = R.right ∧
          ((chainPieceChart hM9 (Mole.garden_isMolecule G) ⟨.II, S, a, b, hv⟩).indexing.atom
            ((chainPieceChart hM9 (Mole.garden_isMolecule G) ⟨.II, S, a, b, hv⟩).indexing.shape.ySlot ⟨0, h0⟩)).1 = R.left) := by
  obtain ⟨R, hn, hp, _⟩ := Molecpl.garden_typeII_local_cases G hv hCL
  refine ⟨R, hn, hp, ?_⟩
  set C0 := Classical.choose (WaveTurbulence.Vine.Param.vineparam_grouped _ _ G.molecule (Mole.garden_isMolecule G)
    .II S a b hv (Classical.choice (WaveTurbulence.Vine.isVine_iff_realization.mp hv).2)) with hC0
  have hch : chainPieceChart hM9 (Mole.garden_isMolecule G) ⟨.II, S, a, b, hv⟩ = normalizeChart C0 := rfl
  rw [hch]
  have hadj := exists_adjacent_rung (Mole.garden_isMolecule G) hv.1 R C0
  obtain ⟨h0, hj⟩ := normalizeChart_adj C0 hadj
  refine ⟨h0, ?_⟩
  have hshape := normalizeChart_shape C0
  exact adj_pair hv.1 R (normalizeChart C0) ⟨0, h0⟩ hj (xSlot_ne_x0 _ _) (ySlot_ne_x0 _ _)

/-- Piece form of `rung0_typeII`. -/
theorem rung0_piece (hM9 : VINEPARAM) (P : ChainPiece G.molecule) (hII : P.vineType = .II)
    (hCL : Mole.CLParentPattern G P.atoms P.upper P.lower) :
    ∃ (R : Molecpl.EndRungData G.molecule P.atoms P.upper P.lower) (hn : P.lower.1.2 ≠ []),
      GNode.parent P.lower.toNode hn = R.left ∧
      ∃ h0 : 0 < (chainPieceChart hM9 (Mole.garden_isMolecule G) P).indexing.shape.m,
        (((chainPieceChart hM9 (Mole.garden_isMolecule G) P).indexing.atom
            ((chainPieceChart hM9 (Mole.garden_isMolecule G) P).indexing.shape.xSlot ⟨0, h0⟩)).1 = R.left ∧
          ((chainPieceChart hM9 (Mole.garden_isMolecule G) P).indexing.atom
            ((chainPieceChart hM9 (Mole.garden_isMolecule G) P).indexing.shape.ySlot ⟨0, h0⟩)).1 = R.right) ∨
        (((chainPieceChart hM9 (Mole.garden_isMolecule G) P).indexing.atom
            ((chainPieceChart hM9 (Mole.garden_isMolecule G) P).indexing.shape.xSlot ⟨0, h0⟩)).1 = R.right ∧
          ((chainPieceChart hM9 (Mole.garden_isMolecule G) P).indexing.atom
            ((chainPieceChart hM9 (Mole.garden_isMolecule G) P).indexing.shape.ySlot ⟨0, h0⟩)).1 = R.left) := by
  obtain ⟨X, S, a, b, hv⟩ := P
  dsimp only at hII hCL ⊢
  subst hII
  exact rung0_typeII hM9 hv hCL

end WaveTurbulence.VineEstS3
