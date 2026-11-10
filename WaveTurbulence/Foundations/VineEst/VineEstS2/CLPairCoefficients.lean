/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLPairLeaves
public import WaveTurbulence.Foundations.VineEst.VineEstS2.PhysicalPredecessor
public import WaveTurbulence.Frozen.Defs.SumintDatum
public import WaveTurbulence.Frozen.Defs.SumintDatumAdmissible
public import WaveTurbulence.Frozen.Defs.SumintDatumEllVec
public import WaveTurbulence.Frozen.Defs.SumintDatumExpr
public import WaveTurbulence.Frozen.Defs.SumintDatumKVec
public import WaveTurbulence.Frozen.Defs.SumintDatumM0
public import WaveTurbulence.Frozen.Defs.SumintDatumM1
public import WaveTurbulence.Frozen.Defs.SumintDatumPhase
public import WaveTurbulence.Frozen.Defs.SumintDatumTimeDom
public import WaveTurbulence.Frozen.Defs.SumintShape
public import WaveTurbulence.Frozen.Defs.SumintShapeLexLt
public import WaveTurbulence.Frozen.Defs.SumintShapeM
public import WaveTurbulence.Frozen.Defs.SumintShapeN
public import WaveTurbulence.Frozen.Defs.SumintShapeTVar
public import WaveTurbulence.Frozen.Defs.SumintShapeUSlot
public import WaveTurbulence.Frozen.Defs.SumintShapeVIdx
public import WaveTurbulence.Frozen.Defs.SumintShapeX0Slot
public import WaveTurbulence.Frozen.Defs.SumintShapeXSlot
public import WaveTurbulence.Frozen.Defs.SumintShapeYSlot
public import WaveTurbulence.Frozen.Defs.WTPrefixA
public import WaveTurbulence.Frozen.Defs.EpsCoef
public import WaveTurbulence.Foundations.WaveB.FrozenB1

/-! # Unit coefficients after cancellation of the actual paired leaves -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree Reg Reg.Skeleton RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

noncomputable def clPairCoefficient (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (S : Finset (GLeaf (CLTreeForest R))) (v : GBranch (CLTreeForest R))
    (p : ↥(clRegionalPairs hG U)) : ℤ := by
  classical
  exact (nodeSign (fun _ : Fin 1 => G.sign a.toNode) v.1 : ℤ)*
    ((if clPairFirstLeaf hU R hG p ∈ S then 1 else 0)-(if clPairSecondLeaf hU R hG p ∈ S then 1 else 0))

/-- Pair cancellation gives0/±1, even when both leaves lie in the predecessor
support. This does not assume a bound on a proposed coefficient. -/
theorem clPairCoefficient_unit (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (S : Finset (GLeaf (CLTreeForest R))) (v : GBranch (CLTreeForest R))
    (p : ↥(clRegionalPairs hG U)) : IsUnitCoeff (clPairCoefficient hU R hG S v p) := by
  classical
  rcases Int.units_eq_one_or (nodeSign (fun _ : Fin 1 => G.sign a.toNode) v.1) with hv | hv <;>
    by_cases hfirst : clPairFirstLeaf hU R hG p ∈ S <;>
    by_cases hsecond : clPairSecondLeaf hU R hG p ∈ S <;>
    simp only [clPairCoefficient,hv,hfirst,hsecond,ite_true,ite_false,IsUnitCoeff] <;> norm_num

end WaveTurbulence.VineEstS2
