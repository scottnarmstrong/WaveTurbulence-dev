/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.V5W.T1
public import WaveTurbulence.Foundations.Flower.V5WT.FlatT
public import WaveTurbulence.Foundations.Flower.V5WT.TopFilter
public import WaveTurbulence.Foundations.Flower.V5WT.Final
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyShape
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainAssembly
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLNormalizedCoordinates
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.Class
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelAbs2
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelAbs3
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelFlat
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelLoc2
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelRec
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelRecurse
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelTop
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.FlatMod.Flat
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.WinChain

/-! # FLOWER-LOW (packet L8), item I3 (T2): the weighted vine estimate (V5W) over `𝒱_γ`

Main's `Flower.V5W*` declarations that depend on the chain assembly or the chart obligation (the cone of
`V5WT.v5FrontierClassBound` through `VineEstS2.CLChainAssembly`, `VINEPARAM`, `ChainPiece`), copied by source
(sha256 in `COPIED-SHA256SUMS`) onto L5b's `𝒱_γ` port of the vine estimate (`GammaLow.Famb`, names suffixed `Γ`),
with L5b's rules: `CLChainAssembly` ↦ `Famb.VineEstS2.CLChainAssemblyΓ γF`, `ChainPiece` ↦ `ChainPieceΓ γF`,
`VINEPARAM` ↦ `Famb.NormalChartSupply γF`, `.vineType` ↦ `.label`; copied names get the suffix `Γ`. Everything else
(weights, frontier filters, flat estimates, kernels) is main's, by import. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace WaveTurbulence.GammaLow.Flower

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WT
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory WaveTurbulence.VineEstS5C.FlatMod WaveTurbulence.VineEstS5C.Cont VineEstS5C
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open TTree Twist LFTwist RegRed Reg.Skeleton MeasureTheory VineEstS2 VineEstS3 VineEstS4 VineEstS5C VineEstS5C.Cont VineEstS5C.P4.Final VineEstS5C.P4
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS4 Links
open WaveTurbulence.VineSpaceK (ClassMember nodeWeight)
open WaveTurbulence.Flower.V5W (nodeRowIncoh regionWeightFW stateCoreLayer topFilterWeight clLocalKernelFW clLocalSummandFW twistedLocalKernelFW twistedRecenteredFW clLocalStarProductFW)
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {kind : Bool}
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The top-weighted bond weight of a level region, on the representative chart. -/
noncomputable def lvWTΓ (ψ : WD d) (W : (Fin 4 → Mom d) → ℂ) (κ0 : KPar d) (lv : Famb.VineEstS5C.LvlΓ B) :
    (GNode G.tree → Fin d → ℤ) → ℂ :=
  bWT ψ W κ0 (lv.state B RD hG layer hLayer) lv.c.U lv.c.a

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WT
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory WaveTurbulence.VineEstS5C.FlatMod WaveTurbulence.VineEstS5C.Cont VineEstS5C
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open TTree Twist LFTwist RegRed Reg.Skeleton MeasureTheory VineEstS2 VineEstS3 VineEstS4 VineEstS5C VineEstS5C.Cont VineEstS5C.P4.Final VineEstS5C.P4
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS4 Links
open WaveTurbulence.VineSpaceK (ClassMember nodeWeight)
open WaveTurbulence.Flower.V5W (nodeRowIncoh regionWeightFW stateCoreLayer topFilterWeight clLocalKernelFW clLocalSummandFW twistedLocalKernelFW twistedRecenteredFW clLocalStarProductFW)
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {kind : Bool}
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The base case: no operative member. -/
theorem classSumBT_baseΓ (lam : ℝ) (ψ : WD d) (W : (Fin 4 → Mom d) → ℂ) (κ0 : KPar d) (hprime : IsPrimeGarden G) (lv : Famb.VineEstS5C.LvlΓ B)
    (hno : ∀ j, IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j))
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    classSumBTΓ (p := p) (kind := kind) B RD hG layer hLayer lam ψ W lv κ0 t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
        lkRaw lv.region κ0.L κ0.base (spatialMul (lvWTΓ B RD hG layer hLayer ψ W κ0 lv)
          (modPsi b lam (lv.psiBase B RD hG layer hLayer κ0))) ![t0, t1, t2] ![e, f, g, h] := by
  classical
  have hp' : IsPrimeGarden (lv.state B RD hG layer hLayer).skeleton := hprime
  unfold classSumBTΓ
  rw [canonFinset_of_noop (lv.state B RD hG layer hLayer) hp' lv.c hno, Finset.sum_singleton]
  unfold memberBT
  have hh := memberMX_eq_lkRaw (lv.state B RD hG layer hLayer).data
    (lv.state B RD hG layer hLayer).plain lv.region lam κ0.L κ0.γ κ0.δ κ0.F
    (stateLayer (lv.state B RD hG layer hLayer)) (stateLayer_isLayering _) κ0.base
    (lvWTΓ B RD hG layer hLayer ψ W κ0 lv) t0 t1 t2 e f g h
  have hb : modPsi lv.c.b lam (lv.psiBase B RD hG layer hLayer κ0) =
      modPsi b lam (lv.psiBase B RD hG layer hLayer κ0) := by rw [lv.hcb]
  exact hh.trans (congrArg (fun Ψ => (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
    lkRaw lv.region κ0.L κ0.base (spatialMul (lvWTΓ B RD hG layer hLayer ψ W κ0 lv) Ψ) ![t0,t1,t2] ![e,f,g,h]) hb)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WT
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory WaveTurbulence.VineEstS5C.FlatMod WaveTurbulence.VineEstS5C.Cont VineEstS5C
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open TTree Twist LFTwist RegRed Reg.Skeleton MeasureTheory VineEstS2 VineEstS3 VineEstS4 VineEstS5C VineEstS5C.Cont VineEstS5C.P4.Final VineEstS5C.P4
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS4 Links
open WaveTurbulence.VineSpaceK (ClassMember nodeWeight)
open WaveTurbulence.Flower.V5W (nodeRowIncoh regionWeightFW stateCoreLayer topFilterWeight clLocalKernelFW clLocalSummandFW twistedLocalKernelFW twistedRecenteredFW clLocalStarProductFW)
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {kind : Bool}
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The bottom case: one operative bottom vine. -/
theorem classSumBT_bottomΓ (lam : ℝ) (ψ : WD d) (C : ℝ) (hC : 0 ≤ C) (hψ : ∀ q q' k, ‖ψ.ψ q q' k‖ ≤ C)
    (W : (Fin 4 → Mom d) → ℂ) (CW : ℝ) (hCW : 0 ≤ CW) (hW : ∀ z, ‖W z‖ ≤ CW)
    (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|)
    (hprime : IsPrimeGarden G) (lv : Famb.VineEstS5C.LvlΓ B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0)
    (hup : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j))
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    classSumBTΓ (p := p) (kind := kind) B RD hG layer hLayer lam ψ W lv κ0 t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
        lkRaw lv.region κ0.L κ0.base
          (spatialMul (lvWTΓ B RD hG layer hLayer ψ W κ0 lv)
            (modPsi b lam (WaveTurbulence.VineEstS5B2.psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c pstar)))
          ![t0, t1, t2] ![e, f, g, h] := by
  let κ : KPar d := {κ0 with t0 := t0, t1 := t1, t2 := t2, e := e, f := f, g := g, h := h}
  have hh := sum_memberBT_bottom_eq_flat (p := p) (kind := kind) κ lam ψ C hC hψ W CW hCW hW
    (lv.state B RD hG layer hLayer) lv.c hprime
    (Famb.VineEstS5C.LvlΓ.bottom_hb0 B RD hG layer hLayer lv pstar h0) hup hL hF
  have hb : modPsi lv.c.b lam (WaveTurbulence.VineEstS5B2.psiBot p kind κ (lv.state B RD hG layer hLayer) lv.c pstar) =
      modPsi b lam (WaveTurbulence.VineEstS5B2.psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c pstar) := by
    rw [lv.hcb]
    rfl
  exact hh.trans (congrArg (fun Ψ => (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
    lkRaw lv.region κ0.L κ0.base (spatialMul (lvWTΓ B RD hG layer hLayer ψ W κ0 lv) Ψ) ![t0,t1,t2] ![e,f,g,h]) hb)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WT
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory WaveTurbulence.VineEstS5C.FlatMod WaveTurbulence.VineEstS5C.Cont VineEstS5C
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open TTree Twist LFTwist RegRed Reg.Skeleton MeasureTheory VineEstS2 VineEstS3 VineEstS4 VineEstS5C VineEstS5C.Cont VineEstS5C.P4.Final VineEstS5C.P4
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS4 Links
open WaveTurbulence.VineSpaceK (ClassMember nodeWeight)
open WaveTurbulence.Flower.V5W (nodeRowIncoh regionWeightFW stateCoreLayer topFilterWeight clLocalKernelFW clLocalSummandFW twistedLocalKernelFW twistedRecenteredFW clLocalStarProductFW)
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {kind : Bool}
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- **One level, flat form, bond-weighted.** -/
theorem classSumBT_flat_stepΓ (lam : ℝ) (ψ : WD d) (C : ℝ) (hC : 0 ≤ C) (hψ : ∀ q q' k, ‖ψ.ψ q q' k‖ ≤ C)
    (W : (Fin 4 → Mom d) → ℂ) (CW : ℝ) (hCW : 0 ≤ CW) (hW : ∀ z, ‖W z‖ ≤ CW)
    (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|)
    (hprime : IsPrimeGarden G) (lv : Famb.VineEstS5C.LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val)
    (hA0 : ∀ j, j ∉ {j | (lv.e j).1.val < (lv.e pstar).1.val} → j ≠ pstar →
      IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j))
    (Ψ' : PsiT G d)
    (hIH : ∀ (t0 t1 t2 : ℝ) (e f g h : Mom d),
      classSumBΓ (p := p) (kind := kind) B RD hG layer hLayer lam ψ (lv.next B RD hG layer hLayer pstar hk) κ0
          t0 t1 t2 e f g h =
        (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 (lv.next B RD hG layer hLayer pstar hk).region *
          clLocalZeta (lv.next B RD hG layer hLayer pstar hk).region *
          lkRaw (lv.next B RD hG layer hLayer pstar hk).region κ0.L κ0.base
            (spatialMul (lvWΓ B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk)) (modPsi b lam Ψ'))
            ![t0, t1, t2] ![e, f, g, h])
    (hlocS : ∀ x (u u' : GBranch G.tree → ℝ), (∀ v ∈ (lv.split B RD hG layer hLayer pstar hk).sb.U, u v = u' v) →
      psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime x u =
        psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime x u')
    (hlocT : ∀ x t' (u u' : GBranch G.tree → ℝ), (∀ v ∈ (lv.split B RD hG layer hLayer pstar hk).tb.U, u v = u' v) →
      Ψ' x t' u = Ψ' x t' u')
    (t0 t1 t2 : ℝ) (e f g h : Mom d)
    (hAbs : GlueAbsConv (lv.split B RD hG layer hLayer pstar hk).RU (lv.split B RD hG layer hLayer pstar hk).RS
      (lv.split B RD hG layer hLayer pstar hk).RT κ0.L κ0.base t0 t1 t2 e f g h
      (Famb.VineEstS5C.LvlΓ.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime Ψ')) :
    classSumBTΓ (p := p) (kind := kind) B RD hG layer hLayer lam ψ W lv κ0 t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
        lkRaw lv.region κ0.L κ0.base
          (spatialMul (lvWTΓ B RD hG layer hLayer ψ W κ0 lv)
            (modPsi b lam (Famb.VineEstS5C.LvlΓ.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime Ψ')))
          ![t0, t1, t2] ![e, f, g, h] := by
  have hcomm : psiStepSp (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime (modPsi b lam (spatialMul (lvWΓ B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk)) Ψ')) =
      modPsi b lam (spatialMul (fun x => (lvWΓ B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk)) (rB (lv.split B RD hG layer hLayer pstar hk).RT x))
        (Famb.VineEstS5C.LvlΓ.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime Ψ')) := by
    exact (psiStepSp_modPsi κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime b lam _).trans
      (congrArg (modPsi b lam) (psiStepSp_spatialMul κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime (lvWΓ B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk)) Ψ'))
  have hbT : b ∈ (lv.split B RD hG layer hLayer pstar hk).tb.U := Famb.VineEstS5C.LvlΓ.b_mem B (lv.next B RD hG layer hLayer pstar hk)
  rw [classSumBT_nestedΓ (p := p) (kind := kind) B RD hG layer hLayer lam ψ C hC hψ W CW hCW hW κ0 hL hF hprime lv pstar hk hA0
    t0 t1 t2 e f g h]
  have hAbs' : GlueAbsConv (lv.split B RD hG layer hLayer pstar hk).RU (lv.split B RD hG layer hLayer pstar hk).RS (lv.split B RD hG layer hLayer pstar hk).RT κ0.L κ0.base t0 t1 t2 e f g h
      (psiStepSp (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime (modPsi b lam (spatialMul (lvWΓ B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk)) Ψ'))) := by
    rw [hcomm]
    refine glueAbsConv_modPsi _ _ _ κ0.L κ0.base t0 t1 t2 e f g h _ ?_ b lam
    exact glueAbsConv_spatialMul (lv.split B RD hG layer hLayer pstar hk).RU (lv.split B RD hG layer hLayer pstar hk).RS (lv.split B RD hG layer hLayer pstar hk).RT κ0.L κ0.base t0 t1 t2 e f g h _ hAbs
      (fun x => (lvWΓ B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk)) (rB (lv.split B RD hG layer hLayer pstar hk).RT x)) (bWNB ψ ((lv.next B RD hG layer hLayer pstar hk).state B RD hG layer hLayer) (lv.next B RD hG layer hLayer pstar hk).c.U C)
      (fun x => norm_bWN_le ψ κ0 ((lv.next B RD hG layer hLayer pstar hk).state B RD hG layer hLayer) (lv.next B RD hG layer hLayer pstar hk).c.U C hψ _)
  have hmerge := flat_merge_W (p := p) (kind := kind) κ0 hL (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime
    (bWT ψ W κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk).sb.U (lv.split B RD hG layer hLayer pstar hk).sb.a)
    (bWNB ψ (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk).sb.U C * CW)
    (fun x => norm_bWT_le ψ W κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk).sb.U (lv.split B RD hG layer hLayer pstar hk).sb.a hψ hW x)
    (modPsi b lam (spatialMul (lvWΓ B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk)) Ψ'))
    (fun t E F' => classSumBΓ (p := p) (kind := kind) B RD hG layer hLayer lam ψ (lv.next B RD hG layer hLayer pstar hk)
      κ0 t t1 t2 E F' g h)
    (lv.next B RD hG layer hLayer pstar hk).region lv.region t0 t1 t2 e f g h
    (fun t E F' => (hIH t t1 t2 E F' g h).trans (congrArg (fun Ψ => (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^
      clLocalOrder1 (lv.next B RD hG layer hLayer pstar hk).region * clLocalZeta (lv.next B RD hG layer hLayer pstar hk).region *
      lkRaw (lv.next B RD hG layer hLayer pstar hk).region κ0.L κ0.base Ψ ![t, t1, t2] ![E, F', g, h]) (spatialMul_modPsi _ _ _ _))) hlocS
    (fun x t' u u' hu => by
      unfold modPsi spatialMul
      rw [hu b hbT, hlocT x t' u u' hu])
    hAbs'
  have hcU : lv.c.U = (lv.split B RD hG layer hLayer pstar hk).sb.U ∪ (lv.split B RD hG layer hLayer pstar hk).tb.U := (lv.split B RD hG layer hLayer pstar hk).union
  have hwB : ∀ x : GNode G.tree → Fin d → ℤ, lvWΓ B RD hG layer hLayer ψ κ0 lv x =
      bWN ψ κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk).sb.U (rA (lv.split B RD hG layer hLayer pstar hk).RS x) * (lvWΓ B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk)) (rB (lv.split B RD hG layer hLayer pstar hk).RT x) := by
    intro x
    unfold lvWΓ bWN
    rw [hcU, bondWD_union (ΨX ψ (lv.state B RD hG layer hLayer)) κ0.L κ0.base (layX (lv.state B RD hG layer hLayer)) (lv.split B RD hG layer hLayer pstar hk).sb.block (lv.split B RD hG layer hLayer pstar hk).hT (lv.split B RD hG layer hLayer pstar hk).hi (lv.split B RD hG layer hLayer pstar hk).hU x,
      bondWD_rA (ΨX ψ (lv.state B RD hG layer hLayer)) κ0.L κ0.base (layX (lv.state B RD hG layer hLayer)) (lv.split B RD hG layer hLayer pstar hk).RS x]
    congr 1
    exact (bondWD_rB (ΨX ψ (lv.state B RD hG layer hLayer)) κ0.L κ0.base (layX (lv.state B RD hG layer hLayer)) (lv.split B RD hG layer hLayer pstar hk).RT x).symm
  have hw : ∀ x : GNode G.tree → Fin d → ℤ, lvWTΓ B RD hG layer hLayer ψ W κ0 lv x =
      bWT ψ W κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk).sb.U
        (lv.split B RD hG layer hLayer pstar hk).sb.a (rA (lv.split B RD hG layer hLayer pstar hk).RS x) *
        (lvWΓ B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk)) (rB (lv.split B RD hG layer hLayer pstar hk).RT x) := by
    intro x
    have hn : nodeWeight W κ0.L κ0.base (lv.split B RD hG layer hLayer pstar hk).sb.a
        (rA (lv.split B RD hG layer hLayer pstar hk).RS x) = nodeWeight W κ0.L κ0.base lv.c.a x :=
      (nodeWeight_rA (lv.split B RD hG layer hLayer pstar hk).sb.block (lv.split B RD hG layer hLayer pstar hk).hT
        (lv.split B RD hG layer hLayer pstar hk).hi (lv.split B RD hG layer hLayer pstar hk).hU
        (lv.split B RD hG layer hLayer pstar hk).RS W κ0.L κ0.base x).trans
        (by rw [(lv.split B RD hG layer hLayer pstar hk).sa]; rfl)
    have hb := hwB x
    unfold lvWΓ at hb
    unfold lvWTΓ bWT lvWΓ
    rw [hb, hn]
    exact mul_right_comm _ _ _
  have hΨ := spatialMul_combine (G' := G) (lvWTΓ B RD hG layer hLayer ψ W κ0 lv) (bWT ψ W κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk).sb.U (lv.split B RD hG layer hLayer pstar hk).sb.a) (lvWΓ B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk))
    (rA (lv.split B RD hG layer hLayer pstar hk).RS) (rB (lv.split B RD hG layer hLayer pstar hk).RT) b lam (Famb.VineEstS5C.LvlΓ.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime Ψ') hw
  refine hmerge.trans ((congrArg (fun Ψ => (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region *
    clLocalZeta lv.region * lkRaw lv.region κ0.L κ0.base
      (spatialMul (fun x => bWT ψ W κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk).sb.U (lv.split B RD hG layer hLayer pstar hk).sb.a (rA (lv.split B RD hG layer hLayer pstar hk).RS x)) Ψ) ![t0, t1, t2] ![e, f, g, h]) hcomm).trans ?_)
  exact congrArg (fun Ψ => (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
    lkRaw lv.region κ0.L κ0.base Ψ ![t0, t1, t2] ![e, f, g, h]) hΨ

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WT
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory WaveTurbulence.VineEstS5C.FlatMod WaveTurbulence.VineEstS5C.Cont VineEstS5C
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open TTree Twist LFTwist RegRed Reg.Skeleton MeasureTheory VineEstS2 VineEstS3 VineEstS4 VineEstS5C VineEstS5C.Cont VineEstS5C.P4.Final VineEstS5C.P4
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS4 Links
open WaveTurbulence.VineSpaceK (ClassMember nodeWeight)
open WaveTurbulence.Flower.V5W (nodeRowIncoh regionWeightFW stateCoreLayer topFilterWeight clLocalKernelFW clLocalSummandFW twistedLocalKernelFW twistedRecenteredFW clLocalStarProductFW)
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {kind : Bool}
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- **The top-weighted level sum, flat form**: one top-weighted step over V5W-B-WORLD's bond-weighted induction
(`classSumB_flatΓ` for the next level). -/
theorem classSumBT_flatΓ (lam : ℝ) (ψ : WD d) (C : ℝ) (hC : 0 ≤ C) (hψ : ∀ q q' k, ‖ψ.ψ q q' k‖ ≤ C)
    (W : (Fin 4 → Mom d) → ℂ) (CW : ℝ) (hCW : 0 ≤ CW) (hW : ∀ z, ‖W z‖ ≤ CW)
    (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|)
    (hprime : IsPrimeGarden G)
    (hlocS : ∀ (lv : Famb.VineEstS5C.LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) x (u u' : GBranch G.tree → ℝ),
      (∀ v ∈ (lv.split B RD hG layer hLayer pstar hk).sb.U, u v = u' v) →
      psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime x u =
        psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime x u')
    (hlocPsi : ∀ (m : ℕ) (lv : Famb.VineEstS5C.LvlΓ B) x t (u u' : GBranch G.tree → ℝ), (∀ v ∈ lv.c.U, u v = u' v) →
      Famb.VineEstS5C.LvlΓ.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m lv x t u =
        Famb.VineEstS5C.LvlΓ.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m lv x t u')
    (hAbs : ∀ (m : ℕ) (lv : Famb.VineEstS5C.LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (t0 t1 t2 : ℝ) (e f g h : Mom d),
      GlueAbsConv (lv.split B RD hG layer hLayer pstar hk).RU (lv.split B RD hG layer hLayer pstar hk).RS
        (lv.split B RD hG layer hLayer pstar hk).RT κ0.L κ0.base t0 t1 t2 e f g h
        (Famb.VineEstS5C.LvlΓ.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime
          (Famb.VineEstS5C.LvlΓ.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m (lv.next B RD hG layer hLayer pstar hk)))) :
    ∀ (m : ℕ) (lv : Famb.VineEstS5C.LvlΓ B), Fintype.card lv.ι ≤ m → ∀ (t0 t1 t2 : ℝ) (e f g h : Mom d),
      classSumBTΓ (p := p) (kind := kind) B RD hG layer hLayer lam ψ W lv κ0 t0 t1 t2 e f g h =
        (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
          lkRaw lv.region κ0.L κ0.base
            (spatialMul (lvWTΓ B RD hG layer hLayer ψ W κ0 lv)
              (modPsi b lam (Famb.VineEstS5C.LvlΓ.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1) lv)))
            ![t0, t1, t2] ![e, f, g, h] := by
  intro m
  cases m with
  | zero =>
    intro lv hc t0 t1 t2 e f g h
    have hno : ∀ j, IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j) := by
      intro j
      have : Fintype.card lv.ι = 0 := Nat.le_zero.mp hc
      exact ((Fintype.card_eq_zero_iff.mp this).false j).elim
    have hnop : ¬ ∃ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j := fun ⟨j, hj⟩ => (hno j).false hj.some
    rw [classSumBT_baseΓ (p := p) (kind := kind) B RD hG layer hLayer lam ψ W κ0 hprime lv hno]
    simp only [Famb.VineEstS5C.LvlΓ.psiFuel, hnop, dite_false]
  | succ m =>
    intro lv hc t0 t1 t2 e f g h
    by_cases hop : ∃ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j
    · obtain ⟨hpop, hpmax⟩ := Classical.choose_spec (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop)
      set pstar := Classical.choose (lv.exists_top (p := p) (kind := kind) B RD hG layer hLayer hop) with hpstar
      by_cases hk : 1 ≤ (lv.e pstar).1.val
      swap
      · have h0 : (lv.e pstar).1.val = 0 := by omega
        have hup : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j) := by
          intro j hjp
          refine ⟨fun op => hjp ?_⟩
          have h1 := hpmax j ⟨op⟩
          have h2 : (lv.e j).1.val = (lv.e pstar).1.val := by omega
          exact lv.he (Subtype.ext (Fin.ext h2))
        have hstep : Famb.VineEstS5C.LvlΓ.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1 + 1) lv =
            WaveTurbulence.VineEstS5B2.psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c pstar := by
          rw [Famb.VineEstS5C.LvlΓ.psiFuel, dite_eq_left hop]
          exact dite_eq_right hk
        rw [hstep]
        exact classSumBT_bottomΓ (p := p) (kind := kind) B RD hG layer hLayer lam ψ C hC hψ W CW hCW hW κ0 hL hF hprime lv
          pstar h0 hup
          t0 t1 t2 e f g h
      have hA0 : ∀ j, j ∉ {j | (lv.e j).1.val < (lv.e pstar).1.val} → j ≠ pstar →
          IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j) := by
        intro j hj hjp
        refine ⟨fun op => ?_⟩
        have h1 := hpmax j ⟨op⟩
        have h2 : (lv.e j).1.val = (lv.e pstar).1.val := le_antisymm h1 (not_lt.mp hj)
        exact hjp (lv.he (Subtype.ext (Fin.ext h2)))
      have hcard : Fintype.card (lv.next B RD hG layer hLayer pstar hk).ι ≤ m := by
        have := Famb.VineEstS5C.LvlΓ.card_next_lt B RD hG layer hLayer lv pstar hk
        omega
      have hIH := fun t0 t1 t2 e f g h => classSumB_flatΓ (p := p) (kind := kind) B RD hG layer hLayer lam ψ C hC hψ
        κ0 hL hF hprime hlocS hlocPsi hAbs m (lv.next B RD hG layer hLayer pstar hk) hcard t0 t1 t2 e f g h
      have hstep : Famb.VineEstS5C.LvlΓ.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1 + 1) lv =
          Famb.VineEstS5C.LvlΓ.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime
            (Famb.VineEstS5C.LvlΓ.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1) (lv.next B RD hG layer hLayer pstar hk)) := by
        rw [Famb.VineEstS5C.LvlΓ.psiFuel, dite_eq_left hop]
        exact dite_eq_left hk
      rw [hstep]
      exact classSumBT_flat_stepΓ (p := p) (kind := kind) B RD hG layer hLayer lam ψ C hC hψ W CW hCW hW κ0 hL hF hprime lv
        pstar hk hA0 _
        hIH (hlocS lv pstar hk) (fun x t' u u' hu => hlocPsi (m + 1) (lv.next B RD hG layer hLayer pstar hk) x t' u u' hu)
        t0 t1 t2 e f g h (hAbs (m + 1) lv pstar hk t0 t1 t2 e f g h)
    · have hno : ∀ j, IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j) :=
        fun j => ⟨fun op => hop ⟨j, ⟨op⟩⟩⟩
      rw [classSumBT_baseΓ (p := p) (kind := kind) B RD hG layer hLayer lam ψ W κ0 hprime lv hno]
      simp only [Famb.VineEstS5C.LvlΓ.psiFuel, hop, dite_false]

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WT
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory WaveTurbulence.VineEstS5C.FlatMod WaveTurbulence.VineEstS5C.Cont VineEstS5C
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open TTree Twist LFTwist RegRed Reg.Skeleton MeasureTheory VineEstS2 VineEstS3 VineEstS4 VineEstS5C VineEstS5C.Cont VineEstS5C.P4.Final VineEstS5C.P4
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS4 Links
open WaveTurbulence.VineSpaceK (ClassMember nodeWeight)
open WaveTurbulence.Flower.V5W (nodeRowIncoh regionWeightFW stateCoreLayer topFilterWeight clLocalKernelFW clLocalSummandFW twistedLocalKernelFW twistedRecenteredFW clLocalStarProductFW)
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {kind : Bool}
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- **Top-weighted FLAT-MOD**: every level's top-weighted class sum is `c ζ lkRaw` of the level's top-weighted bond
weight times the unweighted modulated `psiFuel`. -/
theorem classSumBT_eq_flatΓ (lam : ℝ) (ψ : WD d) (C : ℝ) (hC : 0 ≤ C) (hψ : ∀ q q' k, ‖ψ.ψ q q' k‖ ≤ C)
    (W : (Fin 4 → Mom d) → ℂ) (CW : ℝ) (hCW : 0 ≤ CW) (hW : ∀ z, ‖W z‖ ≤ CW)
    (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|) (hprime : IsPrimeGarden G)
    (lv : Famb.VineEstS5C.LvlΓ B) (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    classSumBTΓ (p := p) (kind := kind) B RD hG layer hLayer lam ψ W lv κ0 t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
        lkRaw lv.region κ0.L κ0.base
          (spatialMul (lvWTΓ B RD hG layer hLayer ψ W κ0 lv)
            (modPsi b lam (Famb.VineEstS5C.LvlΓ.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (Fintype.card lv.ι + 1) lv)))
          ![t0, t1, t2] ![e, f, g, h] :=
  classSumBT_flatΓ (p := p) (kind := kind) B RD hG layer hLayer lam ψ C hC hψ W CW hCW hW κ0 hL hF hprime
    (fun lv pstar hk x _u _u' hu => psiSB_congr (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer)
      (lv.split B RD hG layer hLayer pstar hk) hprime x hu)
    (fun m lv x t _u _u' hu => Famb.VineEstS5C.LvlΓ.psiFuel_congr (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime m lv x t hu)
    (Famb.VineEstS5C.LvlΓ.hAbs_of_leaves (p := p) (kind := kind) B RD hG layer hLayer κ0 hL hprime
      (Famb.VineEstS5C.LvlΓ.absLeaves (p := p) (kind := kind) B RD hG layer hLayer κ0 hL hF hprime))
    (Fintype.card lv.ι) lv le_rfl t0 t1 t2 e f g h

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WT
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory WaveTurbulence.VineEstS5C.FlatMod WaveTurbulence.VineEstS5C.Cont VineEstS5C
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open TTree Twist LFTwist RegRed Reg.Skeleton MeasureTheory VineEstS2 VineEstS3 VineEstS4 VineEstS5C VineEstS5C.Cont VineEstS5C.P4.Final VineEstS5C.P4
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS4 Links
open WaveTurbulence.VineSpaceK (ClassMember nodeWeight)
open WaveTurbulence.Flower.V5W (nodeRowIncoh regionWeightFW stateCoreLayer topFilterWeight clLocalKernelFW clLocalSummandFW twistedLocalKernelFW twistedRecenteredFW clLocalStarProductFW)
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {kind : Bool}
variable {w d p : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
  {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
variable (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

theorem twistedRecenteredModCX_bondT_eq_flatΓ (hprime : IsPrimeGarden G) (lam : ℝ) (ψ : WD d)
    (C : ℝ) (hC : 0 ≤ C) (hψ : ∀ q q' k, ‖ψ.ψ q q' k‖ ≤ C) (W : (Fin 4 → Mom d) → ℂ) (CW : ℝ) (hCW : 0 ≤ CW) (hW : ∀ z, ‖W z‖ ≤ CW)
    (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun z : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L z)|)
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    twistedRecenteredModCX G a (canonFinsetK p kind (Famb.VineEstS4.startStateΓ B RD hG layer hLayer) (Famb.VineEstS4.chainStartΓ B))
      (fun z => bWT ψ W κ0 z.1 z.2.U z.2.a) κ0.L κ0.γ κ0.δ κ0.F κ0.base lam t0 t1 t2 e f g h =
    Complex.exp (((-(Real.pi * κ0.δ * κ0.L ^ (2 * κ0.γ)) * t0 *
      boundaryEnergyFromMomenta (G.sign a.toNode) e f g h : ℝ) : ℂ) * Complex.I) *
      ((coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 (Famb.VineEstS5C.LvlΓ.top B).region * clLocalZeta (Famb.VineEstS5C.LvlΓ.top B).region *
        lkRaw (Famb.VineEstS5C.LvlΓ.top B).region κ0.L κ0.base (spatialMul (lvWTΓ B RD hG layer hLayer ψ W κ0 (Famb.VineEstS5C.LvlΓ.top B))
          (modPsi b lam (Famb.VineEstS5C.LvlΓ.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime
            (Fintype.card (Famb.VineEstS5C.LvlΓ.top B).ι + 1) (Famb.VineEstS5C.LvlΓ.top B)))) ![t0,t1,t2] ![e,f,g,h]) := by
  exact congrArg (fun z => Complex.exp (((-(Real.pi * κ0.δ * κ0.L ^ (2 * κ0.γ)) * t0 *
    boundaryEnergyFromMomenta (G.sign a.toNode) e f g h : ℝ) : ℂ) * Complex.I) * z)
    (classSumBT_eq_flatΓ (p := p) (kind := kind) B RD hG layer hLayer lam ψ C hC hψ W CW hCW hW κ0 hL hF hprime
      (Famb.VineEstS5C.LvlΓ.top B) t0 t1 t2 e f g h)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WT
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory WaveTurbulence.VineEstS5C.FlatMod WaveTurbulence.VineEstS5C.Cont VineEstS5C
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open TTree Twist LFTwist RegRed Reg.Skeleton MeasureTheory VineEstS2 VineEstS3 VineEstS4 VineEstS5C VineEstS5C.Cont VineEstS5C.P4.Final VineEstS5C.P4
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS4 Links
open WaveTurbulence.VineSpaceK (ClassMember nodeWeight)
open WaveTurbulence.Flower.V5W (nodeRowIncoh regionWeightFW stateCoreLayer topFilterWeight clLocalKernelFW clLocalSummandFW twistedLocalKernelFW twistedRecenteredFW clLocalStarProductFW)
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {kind : Bool}
variable {w d p : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
  {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
variable (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

theorem twistedRecenteredModCX_bondT_eq_flatFnΓ (hprime : IsPrimeGarden G) (lam : ℝ) (ψ : WD d)
    (C : ℝ) (hC : 0 ≤ C) (hψ : ∀ q q' k, ‖ψ.ψ q q' k‖ ≤ C) (W : (Fin 4 → Mom d) → ℂ) (CW : ℝ) (hCW : 0 ≤ CW) (hW : ∀ z, ‖W z‖ ≤ CW)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (hL : L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun z : Fin d → ℤ => |F k (base + latticePoint L z)|) :
    (fun (tt : Fin 3 → ℝ) (E : Fin 4 → Mom d) =>
      twistedRecenteredModCX G a (canonFinsetK p kind (Famb.VineEstS4.startStateΓ B RD hG layer hLayer) (Famb.VineEstS4.chainStartΓ B))
        (fun z => bWT ψ W (kparOf L γ δ F base) z.1 z.2.U z.2.a) L γ δ F base lam
        (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
        (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)) =
      flatFnRMXΓ (p := p) (kind := kind) B RD hG layer hLayer
        (lvWTΓ B RD hG layer hLayer ψ W (kparOf L γ δ F base) (Famb.VineEstS5C.LvlΓ.top B)) lam (G.sign a.toNode)
        (kparOf L γ δ F base) hprime (G.sign a.toNode) := by
  funext tt E
  have hh := twistedRecenteredModCX_bondT_eq_flatΓ (p := p) (kind := kind) B RD hG layer hLayer hprime lam ψ C hC hψ
    W CW hCW hW
    (kparOf L γ δ F base) hL hF (tt 0) (tt 1) (tt 2)
    (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
    (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)
  rw [P3.vec3_eta, P3.vec4_eta'] at hh
  exact hh

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WT
open WaveTurbulence MeasureTheory Cut2A DegenVine
open scoped FourierTransform
open RegRed Reg.Skeleton VineParamContract VineEstS2 VineEstS3 VineEstS4 VineEstS5C VineEstS5C.P3
variable {γF : ℝ}
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- The top-filter presentation (Lemma 9.3 in V5's normalized chain coordinates; S-V5W probe §3). -/
def TopFilterPullbackStatementΓ : Prop :=
  ∀ {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (R : CLRegionData G U a b) (L : ℝ) (base : Mom d) (S : Option ℝ), (∀ s, S = some s → 0 < s) →
    EnginePullbackOutΓ (γF := γF) R L base (VineSpaceK.nodeWeight (V5W.topFilterWeight S) L base a) V5W.topFilterMass

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WT
open WaveTurbulence MeasureTheory Cut2A DegenVine
open scoped FourierTransform
open RegRed Reg.Skeleton VineParamContract VineEstS2 VineEstS3 VineEstS4 VineEstS5C VineEstS5C.P3
variable {γF : ℝ}
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- The `S = some s` case. -/
theorem enginePullbackOut_topFilter_someΓ (R : CLRegionData G U a b) (L : ℝ) (base : Mom d) (s : ℝ) :
    EnginePullbackOutΓ (γF := γF) R L base (VineSpaceK.nodeWeight (V5W.topFilterWeight (some s)) L base a)
      V5W.topFilterMass := by
  classical
  intro n hM9 B hL
  obtain ⟨A₁, c₁, hc₁⟩ := normalized_node_affineΓ hM9 B (a.child 1) L base
  set σ : ℤˣ := G.sign a.toNode with hσ
  let r : (Fin 4 → Mom d) → Mom d := fun E => sumintBoundary σ E 0 - sumintBoundary σ E 1
  let f : (Fin 4 → Mom d) → Mom d := fun E => sumintBoundary σ E 1
  let A : (Fin 4 → Mom d) → (Famb.VineEstS2.assemblyShapeΓ hM9 B).VIdx → Mom d →L[ℝ] ℝ :=
    fun E v => (innerSL ℝ ((2 / s) • r E)).comp (A₁ v)
  let c : (Fin 4 → Mom d) → ℝ := fun E =>
    innerSL ℝ ((2 / s) • r E) (base + c₁ E) + -((2 / s) * inner ℝ (r E) (f E))
  refine ⟨affineOutCharMix (Famb.VineEstS2.assemblyShapeΓ hM9 B) FlAffine.chi0Measure A c, ?_, ?_⟩
  · rw [affineOutCharMix_mass]
    exact le_of_eq topFilterMass_eq.symm
  · intro β hβ x
    rw [affineOutCharMix_val]
    set κ := (Famb.VineEstS2.clNormalizedChainEquivΓ hL B base β hβ hM9).symm x with hκ
    set z := clExtendIndices R κ.1 with hz
    have haU : a ∈ U := B.isBlock.2.1
    have hcons := κ.2.1 a haU
    have hb0 := κ.2.2.2 0
    have hb1 := κ.2.2.2 1
    simp only [clBoundaryNodes, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hb0 hb1
    rw [nodeWeight_topFilter_eq L base s a z hcons R.excluded R.excluded_ne_middle]
    have hE : (fun j => base + latticePoint L (β j)) =
        sumintBoundary σ (sumintBoundary σ (fun j => base + latticePoint L (β j))) :=
      (sumintBoundary_invol σ _).symm
    have he : cosetDecoration G L base z a.toNode =
        sumintBoundary σ (sumintBoundary σ (fun j => base + latticePoint L (β j))) 0 := by
      rw [← hE]; exact hb0
    have hf : cosetDecoration G L base z (a.child R.excluded) =
        sumintBoundary σ (sumintBoundary σ (fun j => base + latticePoint L (β j))) 1 := by
      rw [← hE]; exact hb1
    have ha1 : cosetDecoration G L base z (a.child 1) =
        base + (c₁ (sumintBoundary σ (fun j => base + latticePoint L (β j))) +
          ∑ v, A₁ v (latticePoint L (x v))) := by
      change base + latticePoint L (z (a.child 1)) = _
      rw [hz, hκ, hc₁ hL β hβ x]
    rw [he, hf, ha1]
    congr 1
    simp only [A, c, r, f, map_add, map_sum, ContinuousLinearMap.comp_apply]
    ring

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WT
open WaveTurbulence MeasureTheory Cut2A DegenVine
open scoped FourierTransform
open RegRed Reg.Skeleton VineParamContract VineEstS2 VineEstS3 VineEstS4 VineEstS5C VineEstS5C.P3
variable {γF : ℝ}
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- **T4′.** `TopFilterPullbackStatementΓ` (supplement Lemma 9.3 in chain coordinates). -/
theorem topFilterPullbackStatementΓ : TopFilterPullbackStatementΓ (γF := γF) := by
  intro w d G U a b R L base S _
  cases S with
  | some s => exact enginePullbackOut_topFilter_someΓ R L base s
  | none =>
    refine enginePullbackOut_monoΓ R L base (enginePullbackOut_congrΓ R L base
      (enginePullbackOut_ofΓ R L base (enginePullback_oneΓ R L base)) ?_) V5WB.one_le_topFilterMass
    funext z
    simp [VineSpaceK.nodeWeight, V5W.topFilterWeight]

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WT
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS2 VineEstS3 VineEstS4 VineEstS5B Links MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback)
open WaveTurbulence.VineSpaceB (regionDarts)
open WaveTurbulence.Flower.V5W (twistedRecenteredFW topFilterMass topFilterWeight V5FrontierClassBound V5FrontierClassBoundAt)
open WaveTurbulence.Flower.Stage1W (topPsi GPresented)
open scoped ENNReal
open VineEstS5C.P4.Final LGSpine
variable {γF : ℝ}

/-- **The `S ≠ none` half of the weighted vine class bound at a record**, from the output-dependent weighted flat
estimate at that record for every row selector. -/
theorem v5FrontierClassBoundSomeAt_of_flatΓ (P : WTParams) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L)
    (H : ∀ {u : Unit} [_I : VineEst.RowSel u], VineFlatHalfMXOutΓ (γF := γF) P) : V5FrontierClassBoundOnAtΓ (γF := γF) (· ≠ none) P := by
  intro p hp h B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre wBar lam
    g cψ hcψ hpres hreal S hS hSpos hcoh
  obtain ⟨s, rfl⟩ := Option.ne_none_iff_exists'.mp hS
  have hc0 : 0 ≤ cψ := le_trans zero_le_one hcψ
  obtain ⟨αg, _, Mg, hMg, hvg⟩ := Flower.V5WA.presented_of_gPresented hc0 (hpres a.1.1)
  have hgle : ∀ x, ‖g a.1.1 x‖ ≤ cψ := fun x => by
    rw [← hvg]
    exact (Mg.norm_value_le x).trans hMg
  let I : VineEst.RowSel () := selW p (g a.1.1) cψ hcψ hgle (hreal a.1.1)
  have hB : ProfileBound P (truncF p h) (fun _ => B₀) p :=
    fun r hr => ⟨hB₀, by rw [truncF_eq h r hr]; exact hh r hr⟩
  have hF : ∀ k : ℕ, Summable fun z : Fin P.d → ℤ => |truncF p h k (wBar + latticePoint P.L z)| := by
    intro k
    by_cases hk : k ≤ p
    · simpa only [truncF, ite_eq_left hk] using P2.summable_layer_coset hB hd hL hk wBar
    · simp only [truncF, ite_eq_right hk, Pi.zero_apply, abs_zero, summable_zero]
  have hAl : ∀ x, stateLayer (Famb.VineEstS4.startStateΓ B RD hG layer hLayer) x ≤ p := by
    rw [Famb.VineEstS5C.P4.stateLayer_startStateΓ]
    exact hlay
  have hbr : (fun (tt : Fin 3 → ℝ) (E : Fin 4 → Mom P.d) => twistedRecenteredFW p (g a.1.1) (some s) G a
      (canonFinsetK p kind (Famb.VineEstS4.startStateΓ B RD hG layer hLayer) (Famb.VineEstS4.chainStartΓ B)) P.L P.γ P.δ h wBar (VineC.modW lam)
      (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
      (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)) =
      flatFnRMXΓ (rowSel := I) (p := p) (kind := kind) B RD hG layer hLayer
        (lvWTΓ B RD hG layer hLayer (wdOf p (g a.1.1) cψ) (topFilterWeight (some s))
          (kparOf P.L P.γ P.δ (truncF p h) wBar) (Famb.VineEstS5C.LvlΓ.top B))
        lam (G.sign a.toNode) (kparOf P.L P.γ P.δ (truncF p h) wBar) hprime (G.sign a.toNode) := by
    funext tt E
    rw [twistedRecenteredFW_eq p (g a.1.1) cψ hcψ hgle (hreal a.1.1) (some s)]
    refine (twistedRecenteredModCX_congr_F (rowSel := I) (Famb.VineEstS4.startStateΓ B RD hG layer hLayer) hprime (Famb.VineEstS4.chainStartΓ B) hAl
      a P.L P.γ P.δ h (truncF p h) wBar lam _ (tt 0) (tt 1) (tt 2) _ _ _ _ (fun r hr => (truncF_eq h r hr).symm)).trans ?_
    exact congrFun (congrFun (twistedRecenteredModCX_bondT_eq_flatFnΓ (rowSel := I) (p := p) (kind := kind) B RD hG
      layer hLayer hprime lam (wdOf p (g a.1.1) cψ) cψ hc0
      (fun q q' k => by
        show ‖topPsi p (g a.1.1) q q' k‖ ≤ cψ
        unfold topPsi
        split_ifs
        · exact hgle k
        · simpa using hcψ)
      (topFilterWeight (some s)) 1 zero_le_one (norm_topFilterWeight_le s)
      P.L P.γ P.δ (truncF p h) wBar (by linarith only [hL]) hF) tt) E
  have hT := one_le_topFilterMass
  set mass : ℝ := cψ ^ (3 * U.card) * ∏ y ∈ regionDarts G U,
    nodeNorm (Famb.VineEstS4.startStateΓ B RD hG layer hLayer).data (Famb.VineEstS4.startStateΓ B RD hG layer hLayer).plain
      (stateLayer (Famb.VineEstS4.startStateΓ B RD hG layer hLayer)) (stateLayer_isLayering (Famb.VineEstS4.startStateΓ B RD hG layer hLayer)) cψ
      (Mole.dartNode G y) with hmassd
  have hpullB := enginePullback_bWNΓ (γF := γF) (Famb.VineEstS4.startStateΓ B RD hG layer hLayer) (Famb.VineEstS5C.LvlΓ.top B).region B.isBlock P.L wBar p
    (g a.1.1) cψ hcψ ⟨αg, inferInstance, Mg, hMg, hvg⟩
  have hpullT := topFilterPullbackStatementΓ (γF := γF) (Famb.VineEstS5C.LvlΓ.top B).region P.L wBar (some s) hSpos
  have hpull : EnginePullbackOutΓ (γF := γF) (Famb.VineEstS5C.LvlΓ.top B).region P.L wBar
      (lvWTΓ B RD hG layer hLayer (wdOf p (g a.1.1) cψ) (topFilterWeight (some s))
        (kparOf P.L P.γ P.δ (truncF p h) wBar) (Famb.VineEstS5C.LvlΓ.top B)) (mass * topFilterMass) :=
    enginePullbackOut_mulΓ (Famb.VineEstS5C.LvlΓ.top B).region P.L wBar hpullB hpullT
  have hrow : ∏ y ∈ regionDarts G U,
      nodeNorm (Famb.VineEstS4.startStateΓ B RD hG layer hLayer).data (Famb.VineEstS4.startStateΓ B RD hG layer hLayer).plain
        (stateLayer (Famb.VineEstS4.startStateΓ B RD hG layer hLayer)) (stateLayer_isLayering (Famb.VineEstS4.startStateΓ B RD hG layer hLayer)) cψ
        (Mole.dartNode G y) =
      rowNorm cψ (Famb.VineEstS4.startStateΓ B RD hG layer hLayer).data (Famb.VineEstS4.startStateΓ B RD hG layer hLayer).plain R
        (stateLayer (Famb.VineEstS4.startStateΓ B RD hG layer hLayer)) (stateLayer_isLayering (Famb.VineEstS4.startStateΓ B RD hG layer hLayer)) :=
    prod_nodeNorm_regionDarts _ _ _ _ cψ hc0 B.isBlock R
  have hrowle := rowNorm_le hcψ (Famb.VineEstS4.startStateΓ B RD hG layer hLayer).data (Famb.VineEstS4.startStateΓ B RD hG layer hLayer).plain
    B.isBlock R (stateLayer (Famb.VineEstS4.startStateΓ B RD hG layer hLayer)) (stateLayer_isLayering (Famb.VineEstS4.startStateΓ B RD hG layer hLayer))
  have hrow0 : 0 ≤ rowNorm cψ (Famb.VineEstS4.startStateΓ B RD hG layer hLayer).data (Famb.VineEstS4.startStateΓ B RD hG layer hLayer).plain R
      (stateLayer (Famb.VineEstS4.startStateΓ B RD hG layer hLayer)) (stateLayer_isLayering (Famb.VineEstS4.startStateΓ B RD hG layer hLayer)) :=
    hrow ▸ Finset.prod_nonneg fun y _ => by unfold nodeNorm; split_ifs <;> positivity
  have hT0 : 0 ≤ topFilterMass := le_trans zero_le_one hT
  have hmass0 : 0 ≤ mass * topFilterMass := by rw [hmassd, hrow]; positivity
  have hsp : I.weighted = true → I.p = p ∧ GPresented (32 * P.d) (I.g P.d) I.cψ := fun _ =>
    ⟨rfl, by show GPresented (32 * P.d) (gAt (g a.1.1) P.d) cψ; rw [gAt_self]; exact hpres a.1.1⟩
  have key := @H () I p hp hsp h B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1
    centre wBar lam _ (mass * topFilterMass) hmass0 hpull hcoh
  rw [hbr]
  refine key.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  have hU1 : clLocalOrder1 R ≤ U.card := Finset.card_erase_le
  refine mul_le_mul_of_nonneg_right ?_ hT0
  calc mass = cψ ^ (3 * U.card) * rowNorm cψ (Famb.VineEstS4.startStateΓ B RD hG layer hLayer).data
        (Famb.VineEstS4.startStateΓ B RD hG layer hLayer).plain R (stateLayer (Famb.VineEstS4.startStateΓ B RD hG layer hLayer))
        (stateLayer_isLayering (Famb.VineEstS4.startStateΓ B RD hG layer hLayer)) := by rw [hmassd, hrow]
    _ ≤ cψ ^ (3 * U.card) * cψ ^ (2 * clLocalOrder2 RD hG R + 2 * clLocalOrder1 R) :=
        mul_le_mul_of_nonneg_left hrowle (by positivity)
    _ = cψ ^ (3 * U.card + (2 * clLocalOrder2 RD hG R + 2 * clLocalOrder1 R)) := (pow_add _ _ _).symm
    _ ≤ cψ ^ (9 * U.card + 4 * clLocalOrder2 RD hG R) := pow_le_pow_right₀ hcψ (by omega)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WT
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS2 VineEstS3 VineEstS4 VineEstS5B Links MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback)
open WaveTurbulence.VineSpaceB (regionDarts)
open WaveTurbulence.Flower.V5W (twistedRecenteredFW topFilterMass topFilterWeight V5FrontierClassBound V5FrontierClassBoundAt)
open WaveTurbulence.Flower.Stage1W (topPsi GPresented)
open scoped ENNReal
open VineEstS5C.P4.Final LGSpine
variable {γF : ℝ}

/-- **V5W-T: the `S ≠ none` half of the weighted vine class bound** (supplement Lemma 5.3 with the region-top stem
filter of Lemma 9.3, V5 form), in the gate form of the frozen `WTPrefix`. -/
theorem v5FrontierClassBoundSomeΓ : WTPrefix (V5FrontierClassBoundOnAtΓ (γF := γF) (· ≠ none)) := by
  have H := vineFlatHalfMXOut_of_uniformCertΓ (γF := γF) (uniformTermCertKSΓ (γF := γF)) Spine.leafwise_coherent_approximation
    Spine.leafwise_incoherent_decay VineEstS5C.P1.realityAll IncTop.topIncoherentDecayGateR
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H1⟩ := H d hd γ hγ
  refine ⟨η₀, hη₀, ?_⟩
  intro η hη φin hφin τ hτ φ hsol
  obtain ⟨C₁, hC₁, ν₀, hν₀, H2⟩ := H1 η hη φin hφin τ hτ φ hsol
  refine ⟨C₁, hC₁, ν₀, hν₀, ?_⟩
  intro ν hν
  obtain ⟨δ₀, hδ₀, H3⟩ := H2 ν hν
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ D hD htime
  obtain ⟨C₂, hC₂, L₀, hL₀, H4⟩ := H3 δ hδ D hD htime
  refine ⟨C₂, hC₂, L₀, hL₀, ?_⟩
  intro L hL
  exact v5FrontierClassBoundSomeAt_of_flatΓ ⟨d, γ, η, φin, τ, φ, C₁, ν, δ, D, C₂, L⟩
    (by change 1 ≤ d; omega) (by change 1 ≤ L; linarith only [hL₀, hL]) (H4 L hL)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WT
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS2 VineEstS3 VineEstS4 VineEstS5B Links MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback)
open WaveTurbulence.VineSpaceB (regionDarts)
open WaveTurbulence.Flower.V5W (twistedRecenteredFW topFilterMass topFilterWeight V5FrontierClassBound V5FrontierClassBoundAt)
open WaveTurbulence.Flower.Stage1W (topPsi GPresented)
open scoped ENNReal
open VineEstS5C.P4.Final LGSpine
variable {γF : ℝ}

/-- **The weighted vine class bound** `V5FrontierClassBoundΓ` (V5W-0's statement), from its two halves. -/
theorem v5FrontierClassBoundΓ : V5FrontierClassBoundΓ (γF := γF) :=
  v5FrontierClassBound_of_topΓ v5FrontierClassBoundSomeΓ

end

end WaveTurbulence.GammaLow.Flower
