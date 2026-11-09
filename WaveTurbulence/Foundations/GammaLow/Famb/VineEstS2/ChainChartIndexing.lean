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
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.ChainChartIndexing
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.ChainPieces
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.ChainChartIndexing` (sha256 07fd84e04868811a…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Exact sumint vector and clock indices for an actual source chain -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open VineParamContract
variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

/-- The chart of an ingredient: a grouped chart of its label (`ChainPieceΓ.labelCharted`), normalized as in main. -/
noncomputable def chainPieceChartΓ (hM9 : NormalChartSupply γF) (hM : M.IsMolecule) (P : ChainPieceΓ γF M) :
    FullVineChart M P.label P.atoms P.upper P.lower :=
  normalizeChart (Classical.choose (P.labelCharted hM9 hM))

/-- The groups of the chart of an ingredient are its cohmol groups (`famGroups`). -/
theorem chainPieceChart_groupsΓ (hM9 : NormalChartSupply γF) (hM : M.IsMolecule) (P : ChainPieceΓ γF M) :
    WaveTurbulence.Vine.Param.chartAtomGroups (chainPieceChartΓ hM9 hM P) = famGroups γF M P.atoms P.upper P.lower := by
  unfold chainPieceChartΓ
  rw [chartAtomGroups_normalizeChart]
  exact Classical.choose_spec (P.labelCharted hM9 hM)

section garden

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- The chart of one ingredient of a garden chain (main's `chosenVineChart`): the chart of its piece. -/
noncomputable def chosenVineChartΓ (hM9 : NormalChartSupply γF) (hV : FinalCount.Src.IsSomeVine γF G.molecule U a b) :
    FullVineChart G.molecule (ChainPieceΓ.label ⟨U, a, b, hV⟩) U a b :=
  chainPieceChartΓ hM9 (Mole.garden_isMolecule G) ⟨U, a, b, hV⟩

end garden

end WaveTurbulence.GammaLow.Famb.VineEstS2
