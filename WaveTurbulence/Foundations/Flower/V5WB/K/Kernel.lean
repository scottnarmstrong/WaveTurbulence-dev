/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5WB.Common
public import WaveTurbulence.Foundations.VineEst.VineSpaceK.StatementDefs
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ModStatement
public import WaveTurbulence.Foundations.Cut2A.SpatialMeasure
/-! Literal V5 member and class kernels with a spatial multiplier inside each lattice sum. -/
/-! Copied by source (V5W-B-WORLD) from V5W-A's port `Flower/V5WA/VineSpaceK/Kernel.lean` (see `COPIED-SHA256SUMS`): namespace `WaveTurbulence.Flower.V5WB`, every row selector (`variable [RowSel]`), the bond weight `bW` replaced by the masked, normalized `bWN` (`ψ : WD d`, bound `bWNB`). -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.Flower.V5WB
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open MeasureTheory VineEstS5C VineEstS5C.Cont VineEstS4 LFTwist RegRed Reg.Skeleton
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem memberMX_one (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (lam t0 t1 t2 : ℝ) (e f g h : Mom d) :
    memberMX D hG R L γ δ F layer hLayer base lam (fun _ => 1) t0 t1 t2 e f g h =
      clLocalKernelModC D hG R L γ δ F layer hLayer base lam t0 t1 t2 e f g h := by
  simp only [memberMX, one_mul, clLocalKernelModC]

theorem twistedRecenteredModCX_one {ι : Type*} (G : Garden w) (a : GBranch G.tree)
    (Z : Finset (ClassMember w ι)) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d)
    (lam t0 t1 t2 : ℝ) (e f g h : Mom d) :
    twistedRecenteredModCX G a Z (fun _ _ => 1) L γ δ F base lam t0 t1 t2 e f g h =
      twistedRecenteredModC G a Z L γ δ F base lam t0 t1 t2 e f g h := by
  simp only [twistedRecenteredModCX, memberMX_one, twistedRecenteredModC]
end WaveTurbulence.Flower.V5WB
