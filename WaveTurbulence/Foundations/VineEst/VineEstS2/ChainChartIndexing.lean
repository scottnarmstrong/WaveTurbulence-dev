/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.ChainPieces
public import Mathlib.Data.List.Pairwise
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

end WaveTurbulence.VineEstS2
