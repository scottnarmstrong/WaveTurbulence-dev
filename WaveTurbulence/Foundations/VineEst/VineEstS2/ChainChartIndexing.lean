/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.ChainPieceCoding
public import WaveTurbulence.Foundations.VineEst.VineEstS2.M9ShapeSlots
public import WaveTurbulence.Foundations.VineEst.VineEstS2.ChartNormalize
public import WaveTurbulence.Foundations.VineEst.VineEstS2.ChartNormalizeGroups
public import WaveTurbulenceVineParam.VineParamGrouped

/-! # Exact sumint vector and clock indices for an actual source chain -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract
variable {V D : Type} [DecidableEq V] [Fintype D] {M : Molecule V D}

noncomputable def chainPieceChart (_hM9 : VINEPARAM) (hM : M.IsMolecule) (P : ChainPiece M) :
    FullVineChart M P.vineType P.atoms P.upper P.lower :=
  normalizeChart (Classical.choose (WaveTurbulence.Vine.Param.vineparam_grouped _ _ M hM P.vineType P.atoms P.upper
    P.lower P.vine (Classical.choice (WaveTurbulence.Vine.isVine_iff_realization.mp P.vine).2)))

theorem chainPieceChart_groups (hM9 : VINEPARAM) (hM : M.IsMolecule) (P : ChainPiece M) :
    WaveTurbulence.Vine.Param.chartAtomGroups (chainPieceChart hM9 hM P) =
      WaveTurbulence.Vine.Param.realizedGroupSet
        (Classical.choice (WaveTurbulence.Vine.isVine_iff_realization.mp P.vine).2) := by
  unfold chainPieceChart
  rw [chartAtomGroups_normalizeChart]
  exact Classical.choose_spec (WaveTurbulence.Vine.Param.vineparam_grouped _ _ M hM P.vineType P.atoms P.upper
    P.lower P.vine (Classical.choice (WaveTurbulence.Vine.isVine_iff_realization.mp P.vine).2))

abbrev ChainCharts (L : List (ChainPiece M)) :=
  ∀ i : Fin L.length, FullVineChart M (L.get i).vineType (L.get i).atoms (L.get i).upper (L.get i).lower

def chainChartShape (L : List (ChainPiece M)) (C : ChainCharts L) : SumintShape :=
  shapeFamily (fun i => (L.get i).vineType) (fun i => (C i).indexing.shape)

/-- The vector slots go through M9's actual atom indexing and then the
proved source-chain partition. No unidentified leaf or clock permutation. -/
noncomputable def chainChartNodeEquiv (L : List (ChainPiece M))
    (hL : L.Pairwise (fun P Q => Disjoint P.interior Q.interior)) (C : ChainCharts L) :
    (chainChartShape L C).VIdx ≃ ↥(chainPieceUnion L) :=
  (Equiv.sigmaCongrRight (familySlotEquiv (fun i => (L.get i).vineType)
    (fun i => (C i).indexing.shape))).symm |>.trans
    ((Equiv.sigmaCongrRight (fun i => (C i).indexing.atom)).trans (chainPieceNodeEquiv L hL))

noncomputable def chainChartTimeEquiv (L : List (ChainPiece M))
    (hL : L.Pairwise (fun P Q => Disjoint P.interior Q.interior)) (C : ChainCharts L) :
    (chainChartShape L C).TVar ≃ ↥(chainPieceUnion L) :=
  (Sumint.timeVectorEquiv (chainChartShape L C)).trans (chainChartNodeEquiv L hL C)

theorem chainChartShape_M (L : List (ChainPiece M))
    (hL : L.Pairwise (fun P Q => Disjoint P.interior Q.interior)) (C : ChainCharts L) :
    (chainChartShape L C).M = (chainPieceUnion L).card :=
  (Sumint.card_vector_index _).symm.trans
    ((Fintype.card_congr (chainChartNodeEquiv L hL C)).trans (Fintype.card_coe _))

/-- The named M9 obligation supplies charts for the actual ingredients of
a source VC, and the resulting shape has the exact source dimension. -/
theorem exists_chainChartIndexing (hM9 : VINEPARAM) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} {n : ℕ} (h : Vine.Chain M S a b n) :
    ∃ (L : List (ChainPiece M)) (_hL : L.Pairwise (fun P Q => Disjoint P.interior Q.interior))
      (C : ChainCharts L), L.length = n ∧ chainPieceUnion L = S.erase a ∧
      (chainChartShape L C).M = (S.erase a).card := by
  obtain ⟨L,hlen,hU,hL,_⟩ := exists_chainInteriorPieces h
  let C : ChainCharts L := fun i => chainPieceChart hM9 hM (L.get i)
  exact ⟨L,hL,C,hlen,hU,(chainChartShape_M L hL C).trans (congrArg Finset.card hU)⟩

end WaveTurbulence.VineEstS2
