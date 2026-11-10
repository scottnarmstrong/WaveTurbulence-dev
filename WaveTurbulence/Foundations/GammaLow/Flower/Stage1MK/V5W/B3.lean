/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.V5W.B2
public import WaveTurbulence.Foundations.Flower.V5WB.Final
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyShape
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainAssembly
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.BadClause
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.CohmolBound
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.LayerFacts
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.Step3At
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.Step3Data
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.Class
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelTop
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.Final.Core
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.Final.Iface
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.Free
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.WinChain

/-! # FLOWER-LOW (packet L8), item I3 (B3): the weighted vine estimate (V5W) over `𝒱_γ`

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
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {kind : Bool}

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {kind : Bool}

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {kind : Bool}

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {kind : Bool}

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {kind : Bool}

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.DegenVinePar VineParamContract Set
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P2
open scoped ENNReal
open VineEstS5C.P4.Final
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.DegenVinePar VineParamContract Set
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P2
open scoped ENNReal
open VineEstS5C.P4.Final
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS2 VineEstS3 VineEstS4 VineEstS5B Links MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback enginePullback_one)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts layX enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_topDarts_le)
open WaveTurbulence.Flower.V5W (nodeRowIncoh twistedRecenteredFW topFilterMass V5FrontierClassBound V5FrontierClassBoundAt)
open WaveTurbulence.Flower.Stage1W (topPsi GPresented)
open scoped ENNReal FourierTransform
open VineEstS5C.P4.Final LGSpine
variable {γF : ℝ}
variable {w d : ℕ} {ι : Type*} {U : Finset (GBranch _)} 

/-- **The engine pullback of the masked, normalized bond weight of a block.** -/
theorem enginePullback_bWNΓ (X : FamilyReconstruction w ι) {U : Finset (GBranch X.skeleton.tree)}
    {a b : GBranch X.skeleton.tree} (R : CLRegionData X.skeleton U a b) (hU : X.skeleton.molecule.IsBlock U a b)
    (L : ℝ) (base : Mom d) (p : ℕ) (g : Mom d → ℂ) (cψ : ℝ) (hcψ : 1 ≤ cψ)
    (hpres : ∃ (α : Type) (_ : MeasurableSpace α) (M : Cut2A.SpatialMeasure (Mom d) α),
      M.mass ≤ cψ ∧ ∀ x, M.value x = g x) :
    EnginePullbackΓ (γF := γF) R L base (bondWD X.skeleton (ΨX (wdOf p g cψ) X) L base (layX X) U)
      (cψ ^ (3 * U.card) * ∏ y ∈ regionDarts X.skeleton U,
        nodeNorm X.data X.plain (stateLayer X) (stateLayer_isLayering X) cψ (Mole.dartNode X.skeleton y)) := by
  classical
  have hc0 : 0 ≤ cψ := by linarith
  let T : GardenDart X.skeleton → Prop := fun y =>
    layX X (X.skeleton.molecule.atom (X.skeleton.molecule.mate y)) < p ∧ layX X (X.skeleton.molecule.atom y) = p
  have hfac : ∀ y ∈ regionDarts X.skeleton U, EnginePullbackΓ (γF := γF) R L base
      (fun z => ΨX (wdOf p g cψ) X y (layX X (X.skeleton.molecule.atom (X.skeleton.molecule.mate y)))
        (layX X (X.skeleton.molecule.atom y)) (cosetDecoration X.skeleton L base z (Mole.dartNode X.skeleton y)))
      ((if T y then cψ else 1) *
        nodeNorm X.data X.plain (stateLayer X) (stateLayer_isLayering X) cψ (Mole.dartNode X.skeleton y)) := by
    intro y _
    unfold ΨX nodeNorm
    by_cases hi : nodeRowIncoh X.data X.plain (stateLayer X) (stateLayer_isLayering X) (Mole.dartNode X.skeleton y) = 0
    · simp only [hi, ↓reduceIte, mul_one, wdOf]
      by_cases hy : T y
      · rw [if_pos hy]
        obtain ⟨α, _, M, hM, hv⟩ := hpres
        refine enginePullback_monoΓ R L base (enginePullback_congrΓ R L base
          (enginePullback_nodeValueΓ R L base M (Mole.dartNode X.skeleton y)) ?_) hM
        funext z
        rw [hv]
        exact (if_pos hy).symm
      · rw [if_neg hy]
        refine enginePullback_congrΓ R L base (enginePullback_oneΓ R L base) ?_
        funext z
        simp only [topPsi]
        rw [if_neg hy]
    · simp only [hi, ↓reduceIte]
      obtain ⟨α, _, M, hM, hv⟩ := const_presented (d := d)
        (cψ ^ ((nodeRowExp X.data X.plain (stateLayer X) (stateLayer_isLayering X)
          (Mole.dartNode X.skeleton y) : ℝ) / 2))
      have hr : 0 ≤ cψ ^ ((nodeRowExp X.data X.plain (stateLayer X) (stateLayer_isLayering X)
          (Mole.dartNode X.skeleton y) : ℝ) / 2) := Real.rpow_nonneg hc0 _
      have h1 : (1 : ℝ) ≤ if T y then cψ else 1 := by split_ifs <;> linarith
      refine enginePullback_monoΓ R L base (enginePullback_congrΓ R L base
        (enginePullback_nodeValueΓ R L base M (Mole.dartNode X.skeleton y)) ?_) ?_
      · funext z
        rw [hv]
        rfl
      · rw [abs_of_nonneg hr] at hM
        exact hM.trans (le_mul_of_one_le_left hr h1)
  have hprod := enginePullback_finsetProdΓ R L base (regionDarts X.skeleton U) _ _ hfac
  rw [Finset.prod_mul_distrib] at hprod
  have hmass : (∏ y ∈ regionDarts X.skeleton U, if T y then cψ else 1) =
      cψ ^ (topDarts X.skeleton (layX X) U p).card := by
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    rfl
  rw [hmass] at hprod
  refine enginePullback_monoΓ R L base hprod ?_
  refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hcψ ?_)
    (Finset.prod_nonneg fun y _ => ?_)
  · have := card_topDarts_le hU (layX X) p
    omega
  · unfold nodeNorm
    split_ifs
    · exact zero_le_one
    · exact Real.rpow_nonneg hc0 _

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS2 VineEstS3 VineEstS4 VineEstS5B Links MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback enginePullback_one)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts layX enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_topDarts_le)
open WaveTurbulence.Flower.V5W (nodeRowIncoh twistedRecenteredFW topFilterMass V5FrontierClassBound V5FrontierClassBoundAt)
open WaveTurbulence.Flower.Stage1W (topPsi GPresented)
open scoped ENNReal FourierTransform
open VineEstS5C.P4.Final LGSpine
variable {γF : ℝ}

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS2 VineEstS3 VineEstS4 VineEstS5B Links MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback enginePullback_one)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts layX enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_topDarts_le)
open WaveTurbulence.Flower.V5W (nodeRowIncoh twistedRecenteredFW topFilterMass V5FrontierClassBound V5FrontierClassBoundAt)
open WaveTurbulence.Flower.Stage1W (topPsi GPresented)
open scoped ENNReal FourierTransform
open VineEstS5C.P4.Final LGSpine
variable {γF : ℝ}

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS2 VineEstS3 VineEstS4 VineEstS5B Links MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback enginePullback_one)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts layX enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_topDarts_le)
open WaveTurbulence.Flower.V5W (nodeRowIncoh twistedRecenteredFW topFilterMass V5FrontierClassBound V5FrontierClassBoundAt)
open WaveTurbulence.Flower.Stage1W (topPsi GPresented)
open scoped ENNReal FourierTransform
open VineEstS5C.P4.Final LGSpine
variable {γF : ℝ}

end

end WaveTurbulence.GammaLow.Flower
