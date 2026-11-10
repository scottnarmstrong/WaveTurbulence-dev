/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5WB.K.Defs
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceB.Pullback
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceB.Weight
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceK.WeightedMerge
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.LevelNest
/-! Common spatial weights through the actual coherent-family sum in the
native S chart. The multiplier remains inside the lattice sum. -/
/-! Copied by source (V5W-B-WORLD) from V5W-A's port `Flower/V5WA/VineSpaceK/WeightedBundle.lean` (see `COPIED-SHA256SUMS`): namespace `WaveTurbulence.Flower.V5WB`, every row selector (`variable [RowSel]`), the bond weight `bW` replaced by the masked, normalized `bWN` (`ψ : WD d`, bound `bWNB`). -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.Flower.V5WB
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
variable {kind : Bool}
open MeasureTheory Finset

theorem summable_weighted_integrals {X Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (f : X → Y → ℂ)
    (hf : Summable fun x => ∫ y, ‖f x y‖ ∂μ)
    (m : X → ℂ) (M : ℝ) (hM : 0 ≤ M) (hm : ∀ x, ‖m x‖ ≤ M) :
    Summable fun x => ∫ y, m x * f x y ∂μ := by
  apply Summable.of_norm_bounded (hf.mul_left M)
  intro x
  rw [integral_const_mul, norm_mul]
  exact mul_le_mul (hm x) (norm_integral_le_integral_norm _) (norm_nonneg _) hM

open VineEstS5C VineEstS5C.FlatMod VineEstS5B VineEstS4 Twist LFTwist RegRed Reg.Skeleton
variable {w d p : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {pstar : ι} {J : Set ι}

end WaveTurbulence.Flower.V5WB
