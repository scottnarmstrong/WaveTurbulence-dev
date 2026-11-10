/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.V5W.B3
public import WaveTurbulence.Foundations.Flower.V5WT.ClassT
public import WaveTurbulence.Foundations.Flower.V5WT.Engine
public import WaveTurbulence.Foundations.Flower.V5WT.FlatOut
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyShape
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainAssembly
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLNormalizedCoordinates
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.BadClause
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.CohmolBound
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.LayerFacts
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.Step3At
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.Step3Data
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelRec
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelTop
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P2.Dict2
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P2.Recentered
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P3.Bound
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.Final.Core
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.Final.Iface
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.Free

/-! # FLOWER-LOW (packet L8), item I3 (T1): the weighted vine estimate (V5W) over `𝒱_γ`

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
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS4 VineEstS5B
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS2 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory VineEstS4 VineEstS5B
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS5C.FlatMod TTree MeasureTheory
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {kind : Bool}
variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {pstar : ι} {J : Set ι}
variable [Fintype ι] [DecidableEq ι]
variable {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
variable (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- **The top-weighted modulated class sum of a level** (members weighted by `bWT`: bond weight times `W` at the
member's region top). -/
noncomputable def classSumBTΓ (lam : ℝ) (ψ : WD d) (W : (Fin 4 → Mom d) → ℂ) (lv : Famb.VineEstS5C.LvlΓ B) (κ0 : KPar d) (t0 t1 t2 : ℝ)
    (e f g h : Mom d) : ℂ :=
  ∑ z ∈ canonFinsetK p kind (lv.state B RD hG layer hLayer) lv.c,
    memberBT {κ0 with t0 := t0, t1 := t1, t2 := t2, e := e, f := f, g := g, h := h} lam ψ W z.1 z.2

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WT
open WaveTurbulence.Flower.V5WB
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS4 VineEstS5B
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS2 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory VineEstS4 VineEstS5B
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS5C.FlatMod TTree MeasureTheory
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {kind : Bool}
variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {pstar : ι} {J : Set ι}
variable [Fintype ι] [DecidableEq ι]
variable {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
variable (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- **One level of TARGET Step 4, nested form, with the bond weight.** -/
theorem classSumBT_nestedΓ (lam : ℝ) (ψ : WD d) (C : ℝ) (hC : 0 ≤ C)
    (hψ : ∀ q q' k, ‖ψ.ψ q q' k‖ ≤ C) (W : (Fin 4 → Mom d) → ℂ) (CW : ℝ) (hCW : 0 ≤ CW) (hW : ∀ z, ‖W z‖ ≤ CW) (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|)
    (hprime : IsPrimeGarden G) (lv : Famb.VineEstS5C.LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val)
    (hA0 : ∀ j, j ∉ {j | (lv.e j).1.val < (lv.e pstar).1.val} → j ≠ pstar →
      IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j))
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    classSumBTΓ (p := p) (kind := kind) B RD hG layer hLayer lam ψ W lv κ0 t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 (lv.split B RD hG layer hLayer pstar hk).RS *
        clLocalZeta (lv.split B RD hG layer hLayer pstar hk).RS *
        ∑' x : ExtS (lv.split B RD hG layer hLayer pstar hk).RS κ0.L κ0.base e f,
          ∫ σ : CLInternalTime (lv.split B RD hG layer hLayer pstar hk).RS,
            bWT ψ W κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk).sb.U
              (lv.split B RD hG layer hLayer pstar hk).sb.a x.1 *
            (psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk)
              hprime x.1 (clLocalClock (lv.split B RD hG layer hLayer pstar hk).RS ![t0, t1, t2] σ) *
            classSumBΓ (p := p) (kind := kind) B RD hG layer hLayer lam ψ (lv.next B RD hG layer hLayer pstar hk) κ0
              (clLocalClock (lv.split B RD hG layer hLayer pstar hk).RS ![t0, t1, t2] σ
                (lv.split B RD hG layer hLayer pstar hk).sb.b) t1 t2
              (κ0.base + latticePoint κ0.L (x.1 ((lv.state B RD hG layer hLayer).family.placement pstar).lower.toNode))
              (κ0.base + latticePoint κ0.L (x.1 ((lv.state B RD hG layer hLayer).family.placement pstar).retained.toNode))
              g h) := by
  classical
  set A' := lv.state B RD hG layer hLayer with hA'
  set sp := lv.split B RD hG layer hLayer pstar hk with hsp
  let κ : KPar d := { κ0 with t0 := t0, t1 := t1, t2 := t2, e := e, f := f, g := g, h := h }
  have hc : Stage1.OpsCommute p kind w lv.ι := Stage1.opsCommute_all
  have h1 := tildeJ2_BT_canon (p := p) (kind := kind) κ lam ψ C hC hψ W CW hCW hW A' sp hprime hA0 hL hF
  have hKt := KtilB_eq_canon (p := p) (kind := kind) hc
    (Subtype.val : {j : lv.ι // (lv.e j).1.val < (lv.e pstar).1.val} → lv.ι)
    Subtype.val_injective (fun j => j.2) (fun i hi => ⟨⟨i, hi⟩, rfl⟩) κ lam ψ hprime sp hA0
  have e1 : classSumBTΓ (p := p) (kind := kind) B RD hG layer hLayer lam ψ W lv κ0 t0 t1 t2 e f g h =
      ∑ G ∈ zpFinset p kind pstar _ A' sp hprime,
        sSumBAtT κ ψ W G.1 G.2 (ktildeB (p := p) (kind := kind) κ lam ψ A' sp hprime G) := h1
  rw [e1]
  rw [Finset.sum_congr rfl (fun Z hZ => zp_stateBWT κ lam ψ W A' sp hprime hZ), ← Finset.mul_sum,
    weighted_bundle_sumB κ lam ψ C hC hψ A' sp hprime hA0 hL hF (bWT ψ W κ A' sp.sb.U sp.sb.a)
      (bWNB ψ A' sp.sb.U C * CW) (mul_nonneg (bWNB_nonneg _ _ _ hC) hCW)
      (fun x => norm_bWT_le ψ W κ A' sp.sb.U sp.sb.a hψ hW x)]
  congr 1
  refine tsum_congr fun x => integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
  beta_reduce
  rw [hKt]
  rfl

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WT
open WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS3Par.Eng
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.SumintPar WaveTurbulence.VineEstS3.FS Finset MeasureTheory
open scoped ENNReal
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS5C.P2 WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar MeasureTheory WaveTurbulence.VineEstS5C.P4
open scoped ENNReal
open MeasureTheory DegenVine VineEstS5C VineEstS5C.P2 VineEstS5C.P3 VineEstS5C.P4 RegRed Reg.Skeleton VineParamContract VineEstS2 VineEstS3 VineEstS4 TTree
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence.VineSpaceK (spatialMul freeDict_mul)
open scoped ENNReal
variable {γF : ℝ}
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- `EnginePullbackΓ` with an output-dependent mixture (S-V5W probe §3). -/
def EnginePullbackOutΓ (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    (m : (GNode G.tree → Fin d → ℤ) → ℂ) (mass : ℝ) : Prop :=
  ∀ (n : ℕ) (hM9 : Famb.NormalChartSupply γF) (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (hL : L ≠ 0),
  ∃ N : OutCharMix (Famb.VineEstS2.assemblyShapeΓ hM9 B) d, N.mass ≤ mass ∧
    ∀ (β : Fin 4 → Fin d → ℤ) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) x,
      m (clExtendIndices R ((Famb.VineEstS2.clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1) =
        N.val L (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) x

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WT
open WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS3Par.Eng
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.SumintPar WaveTurbulence.VineEstS3.FS Finset MeasureTheory
open scoped ENNReal
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS5C.P2 WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar MeasureTheory WaveTurbulence.VineEstS5C.P4
open scoped ENNReal
open MeasureTheory DegenVine VineEstS5C VineEstS5C.P2 VineEstS5C.P3 VineEstS5C.P4 RegRed Reg.Skeleton VineParamContract VineEstS2 VineEstS3 VineEstS4 TTree
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence.VineSpaceK (spatialMul freeDict_mul)
open scoped ENNReal
variable {γF : ℝ}
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- A plain engine pullback is an output-dependent one. -/
theorem enginePullbackOut_ofΓ (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    {m : (GNode G.tree → Fin d → ℤ) → ℂ} {mass : ℝ} (h : EnginePullbackΓ (γF := γF) R L base m mass) :
    EnginePullbackOutΓ (γF := γF) R L base m mass := by
  intro n hM9 B hL
  obtain ⟨N, hN, he⟩ := h n hM9 B hL
  exact ⟨OutCharMix.ofCharMix N, hN, he⟩

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WT
open WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS3Par.Eng
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.SumintPar WaveTurbulence.VineEstS3.FS Finset MeasureTheory
open scoped ENNReal
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS5C.P2 WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar MeasureTheory WaveTurbulence.VineEstS5C.P4
open scoped ENNReal
open MeasureTheory DegenVine VineEstS5C VineEstS5C.P2 VineEstS5C.P3 VineEstS5C.P4 RegRed Reg.Skeleton VineParamContract VineEstS2 VineEstS3 VineEstS4 TTree
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence.VineSpaceK (spatialMul freeDict_mul)
open scoped ENNReal
variable {γF : ℝ}
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- **Product of a plain and an output-dependent engine pullback** (masses multiply). -/
theorem enginePullbackOut_mulΓ (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    {m₁ m₂ : (GNode G.tree → Fin d → ℤ) → ℂ} {mass₁ mass₂ : ℝ}
    (h₁ : EnginePullbackΓ (γF := γF) R L base m₁ mass₁) (h₂ : EnginePullbackOutΓ (γF := γF) R L base m₂ mass₂) :
    EnginePullbackOutΓ (γF := γF) R L base (fun z => m₁ z * m₂ z) (mass₁ * mass₂) := by
  intro n hM9 B hL
  obtain ⟨N₁, hN₁, he₁⟩ := h₁ n hM9 B hL
  obtain ⟨N₂, hN₂, he₂⟩ := h₂ n hM9 B hL
  refine ⟨OutCharMix.mulC N₁ N₂, ?_, ?_⟩
  · rw [OutCharMix.mulC_mass]
    exact mul_le_mul hN₁ hN₂ N₂.mass_nonneg (N₁.mass_nonneg.trans hN₁)
  · intro β hβ x
    beta_reduce
    rw [OutCharMix.mulC_val, he₁ β hβ x, he₂ β hβ x]

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WT
open WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS3Par.Eng
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.SumintPar WaveTurbulence.VineEstS3.FS Finset MeasureTheory
open scoped ENNReal
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS5C.P2 WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar MeasureTheory WaveTurbulence.VineEstS5C.P4
open scoped ENNReal
open MeasureTheory DegenVine VineEstS5C VineEstS5C.P2 VineEstS5C.P3 VineEstS5C.P4 RegRed Reg.Skeleton VineParamContract VineEstS2 VineEstS3 VineEstS4 TTree
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence.VineSpaceK (spatialMul freeDict_mul)
open scoped ENNReal
variable {γF : ℝ}
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem enginePullbackOut_congrΓ (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    {m m' : (GNode G.tree → Fin d → ℤ) → ℂ} {mass : ℝ} (h : EnginePullbackOutΓ (γF := γF) R L base m mass) (he : m = m') :
    EnginePullbackOutΓ (γF := γF) R L base m' mass := he ▸ h

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WT
open WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS3Par.Eng
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.SumintPar WaveTurbulence.VineEstS3.FS Finset MeasureTheory
open scoped ENNReal
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS5C.P2 WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar MeasureTheory WaveTurbulence.VineEstS5C.P4
open scoped ENNReal
open MeasureTheory DegenVine VineEstS5C VineEstS5C.P2 VineEstS5C.P3 VineEstS5C.P4 RegRed Reg.Skeleton VineParamContract VineEstS2 VineEstS3 VineEstS4 TTree
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence.VineSpaceK (spatialMul freeDict_mul)
open scoped ENNReal
variable {γF : ℝ}
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WT
open WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS3Par.Eng
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.SumintPar WaveTurbulence.VineEstS3.FS Finset MeasureTheory
open scoped ENNReal
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS5C.P2 WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar MeasureTheory WaveTurbulence.VineEstS5C.P4
open scoped ENNReal
open MeasureTheory DegenVine VineEstS5C VineEstS5C.P2 VineEstS5C.P3 VineEstS5C.P4 RegRed Reg.Skeleton VineParamContract VineEstS2 VineEstS3 VineEstS4 TTree
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence.VineSpaceK (spatialMul freeDict_mul)
open scoped ENNReal
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- `Famb.VineEstS5C.P4.W2.FreeDictΓ` depends on the mixture only through its value at the boundary output. -/
theorem freeDict_val_congrΓ (hM9 : Famb.NormalChartSupply γF) (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (Famb.VineEstS2.assemblyShapeΓ hM9 B) d) {L : ℝ} (hL : L ≠ 0) (γ δ η : ℝ) (base : Mom d)
    (β : Fin 4 → (Fin d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (tt : Fin 3 → ℝ)
    (ψ : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → ℂ)
    (wN wDec : ℕ) (bk : Fin (Famb.VineEstS2.assemblyShapeΓ hM9 B).I → Fin 4)
    (cons : Finset ((Famb.VineEstS2.assemblyShapeΓ hM9 B).TVar × (Famb.VineEstS2.assemblyShapeΓ hM9 B).TVar)) (g g' : (Famb.VineEstS2.assemblyShapeΓ hM9 B).VIdx → ℕ)
    (Mx Mx' : CharMix (Famb.VineEstS2.assemblyShapeΓ hM9 B) d) (cr : ClockedRows3 (Famb.VineEstS5C.P2.engDatumΓ hM9 B hG W wN wDec bk cons g g'))
    (hv : ∀ x, Mx.val L (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) x =
      Mx'.val L (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) x)
    (hD : Famb.VineEstS5C.P4.W2.FreeDictΓ hM9 B hG W hL γ δ η base β hβ tt ψ wN wDec bk cons g g' Mx cr) :
    Famb.VineEstS5C.P4.W2.FreeDictΓ hM9 B hG W hL γ δ η base β hβ tt ψ wN wDec bk cons g g' Mx' cr := by
  intro x
  filter_upwards [hD x] with τ hτ
  rw [hτ, hv x]

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WT
open WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS3Par.Eng
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.SumintPar WaveTurbulence.VineEstS3.FS Finset MeasureTheory
open scoped ENNReal
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS5C.P2 WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar MeasureTheory WaveTurbulence.VineEstS5C.P4
open scoped ENNReal
open MeasureTheory DegenVine VineEstS5C VineEstS5C.P2 VineEstS5C.P3 VineEstS5C.P4 RegRed Reg.Skeleton VineParamContract VineEstS2 VineEstS3 VineEstS4 TTree
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence.VineSpaceK (spatialMul freeDict_mul)
open scoped ENNReal
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}
variable {p : ℕ} {kind : Bool} (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
variable {A : ℝ} {P : WTParams}

/-- Copy of `Famb.VineEstS5C.P4.W2.termFnR_leaf_eqΓ` with the mixture depending on the boundary output (`Mxf E`). -/
theorem termFnR_leaf_eqOutΓ (κ0 : KPar P.d) (hκL : κ0.L = P.L) (hκγ : κ0.γ = P.γ) (hκδ : κ0.δ = P.δ) (lv : Famb.VineEstS5C.LvlΓ B)
    (ψ : PsiT G P.d) {Bx : Set (Fin 3 → ℝ)} (n' : ℕ) (hM9 : Famb.NormalChartSupply γF) (B' : Famb.VineEstS2.CLChainAssemblyΓ γF G lv.region n')
    (W : SumintWeightClockData (Famb.VineEstS2.assemblyShapeΓ hM9 B') P.d) (wN wDec : ℕ) (bk : Fin (Famb.VineEstS2.assemblyShapeΓ hM9 B').I → Fin 4)
    (cons : Finset ((Famb.VineEstS2.assemblyShapeΓ hM9 B').TVar × (Famb.VineEstS2.assemblyShapeΓ hM9 B').TVar)) (g g' : (Famb.VineEstS2.assemblyShapeΓ hM9 B').VIdx → ℕ)
    (Z : AmbW A P (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g'))
    (Mxf : (Fin 4 → Mom P.d) → CharMix (Famb.VineEstS2.assemblyShapeΓ hM9 B') P.d)
    (Rw : ∀ ρ : Row (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g'), RowData (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g') (6 * P.η ^ 6) ρ)
    (hL : P.L ≠ 0) (hbase : W.wBar = κ0.base)
    (hind : ∀ (t : Fin 3 → ℝ) (β' : Fin 4 → Mom P.d) (κ : CLLocalDecoration lv.region P.L W.wBar β') (u : GBranch G.tree → ℝ),
      u lv.c.a = t 0 → ψ (clExtendIndices lv.region κ.1) t u = ψ (clExtendIndices lv.region κ.1)
        (WaveTurbulence.VineEstS3.leafT (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut (Famb.VineEstS5C.P4.W2.LeafPosΓ B lv) (Famb.VineEstS5C.P4.W2.LeafNegΓ B lv) t) u)
    (hD : ∀ tt ∈ Bx, ∀ (β : Fin 4 → (Fin P.d → ℤ))
      (hβ : ((G.sign lv.c.a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3),
      sumintBoundary (G.sign lv.c.a.toNode) (fun j => W.wBar + latticePoint P.L (β j)) ∈
        outSet (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η →
      Famb.VineEstS5C.P4.W2.FreeDictΓ hM9 B' hG W hL P.γ P.δ P.η W.wBar β hβ
        (WaveTurbulence.VineEstS3.leafT (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut (Famb.VineEstS5C.P4.W2.LeafPosΓ B lv) (Famb.VineEstS5C.P4.W2.LeafNegΓ B lv) tt)
        ψ wN wDec bk cons g g' (Mxf (sumintBoundary (G.sign lv.c.a.toNode) (fun j => W.wBar + latticePoint P.L (β j))))
        (allCR Rw))
    (s : ℤˣ) (hs : s = G.sign lv.c.a.toNode) (tt : Fin 3 → ℝ) (htt : tt ∈ Bx) (E : Fin 4 → Mom P.d)
    (hE : E ∈ outSet (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η) :
    Famb.VineEstS5C.P2.termFnRΓ B (G.sign lv.c.a.toNode) κ0 lv ψ s tt E =
      Famb.VineEstS5C.P3.LvlΓ.cstΓ B κ0 lv * clockedExprMul3 (Mxf E) (allCR Rw) Z.hI P.L P.γ (2 * P.δ) P.η
        (WaveTurbulence.VineEstS3.leafT (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut (Famb.VineEstS5C.P4.W2.LeafPosΓ B lv) (Famb.VineEstS5C.P4.W2.LeafNegΓ B lv) tt) E := by
  subst hs
  set q := (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut
  set tt' := WaveTurbulence.VineEstS3.leafT q (Famb.VineEstS5C.P4.W2.LeafPosΓ B lv) (Famb.VineEstS5C.P4.W2.LeafNegΓ B lv) tt with htt'
  have h0 : tt 0 = tt' 0 := (WaveTurbulence.VineEstS3.leafT_zero q _ _ tt).symm
  have hlk := lkRaw_leaf_eq (P := P) lv.region P.L W.wBar ψ tt tt' h0
    (by by_cases h : Famb.VineEstS5C.P4.W2.LeafPosΓ B lv
        · exact Or.inl h
        · exact Or.inr (by rw [htt', WaveTurbulence.VineEstS3.leafT_one]; simp [h]))
    (by by_cases h : Famb.VineEstS5C.P4.W2.LeafNegΓ B lv
        · exact Or.inl h
        · exact Or.inr (by rw [htt', WaveTurbulence.VineEstS3.leafT_two]; simp [h]))
    (fun β' κ u hu => hind tt β' κ u hu) (sumintBoundary (G.sign lv.c.a.toNode) E)
  obtain ⟨β, hβ, rfl⟩ := outSet_exists_beta hL (G.sign lv.c.a.toNode) W.wBar E (fun c => (hE.1 c).1) hE.2.1
  have hfd := Famb.VineEstS5C.P4.W2.termFnR_eq_expr3_freeΓ hM9 B' hG W hL P.γ P.δ P.η W.wBar β hβ tt' ψ wN wDec bk cons g g'
    (Mxf (sumintBoundary (G.sign lv.c.a.toNode) (fun j => W.wBar + latticePoint P.L (β j)))) (allCR Rw)
    (hD tt htt β hβ hE)
  unfold Famb.VineEstS5C.P2.termFnRΓ Famb.VineEstS5C.P3.termFnΓ Famb.VineEstS5C.P3.LvlΓ.cstΓ
  rw [hκL, hκγ, hκδ, ← hbase, hlk.1]
  have hrf : recFac (G.sign lv.c.a.toNode) (G.sign lv.c.a.toNode) P.L P.γ P.δ tt
      (sumintBoundary (G.sign lv.c.a.toNode) (fun j => W.wBar + latticePoint P.L (β j))) =
      recFac (G.sign lv.c.a.toNode) (G.sign lv.c.a.toNode) P.L P.γ P.δ tt'
      (sumintBoundary (G.sign lv.c.a.toNode) (fun j => W.wBar + latticePoint P.L (β j))) := by
    unfold recFac; rw [← h0]
  rw [hrf]
  exact hfd

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WT
open WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS3Par.Eng
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.SumintPar WaveTurbulence.VineEstS3.FS Finset MeasureTheory
open scoped ENNReal
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS5C.P2 WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar MeasureTheory WaveTurbulence.VineEstS5C.P4
open scoped ENNReal
open MeasureTheory DegenVine VineEstS5C VineEstS5C.P2 VineEstS5C.P3 VineEstS5C.P4 RegRed Reg.Skeleton VineParamContract VineEstS2 VineEstS3 VineEstS4 TTree
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence.VineSpaceK (spatialMul freeDict_mul)
open scoped ENNReal
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}
variable {p : ℕ} {kind : Bool} (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
variable {A : ℝ} {P : WTParams}

/-- The certified term multiplied by an output-dependent pullback: the leaf independence and the free dictionary of the
product mixture `mulC Z.Mx N` (frozen at each boundary output). -/
theorem termCertW_mulOut_dataΓ (κ0 : KPar P.d) (lv : Famb.VineEstS5C.LvlΓ B) (ψ : PsiT G P.d) {Bx : Set (Fin 3 → ℝ)}
    (n' : ℕ) (hM9 : Famb.NormalChartSupply γF) (B' : Famb.VineEstS2.CLChainAssemblyΓ γF G lv.region n')
    (W : SumintWeightClockData (Famb.VineEstS2.assemblyShapeΓ hM9 B') P.d) (wN wDec : ℕ) (bk : Fin (Famb.VineEstS2.assemblyShapeΓ hM9 B').I → Fin 4)
    (cons : Finset ((Famb.VineEstS2.assemblyShapeΓ hM9 B').TVar × (Famb.VineEstS2.assemblyShapeΓ hM9 B').TVar)) (g g' : (Famb.VineEstS2.assemblyShapeΓ hM9 B').VIdx → ℕ)
    (Mx : CharMix (Famb.VineEstS2.assemblyShapeΓ hM9 B') P.d)
    (Rw : ∀ ρ : Row (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g'), RowData (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g') (6 * P.η ^ 6) ρ)
    (hL : P.L ≠ 0)
    (hD : ∀ tt ∈ Bx, ∀ (β : Fin 4 → (Fin P.d → ℤ))
      (hβ : ((G.sign lv.c.a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3),
      sumintBoundary (G.sign lv.c.a.toNode) (fun j => W.wBar + latticePoint P.L (β j)) ∈
        outSet (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η →
      Famb.VineEstS5C.P4.W2.FreeDictΓ hM9 B' hG W hL P.γ P.δ P.η W.wBar β hβ
        (WaveTurbulence.VineEstS3.leafT (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut (Famb.VineEstS5C.P4.W2.LeafPosΓ B lv) (Famb.VineEstS5C.P4.W2.LeafNegΓ B lv) tt)
        ψ wN wDec bk cons g g' Mx (allCR Rw))
    (m : (GNode G.tree → Fin P.d → ℤ) → ℂ) (N : OutCharMix (Famb.VineEstS2.assemblyShapeΓ hM9 B') P.d)
    (hN : ∀ (β : Fin 4 → Fin P.d → ℤ) (hβ : ((G.sign lv.c.a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) x,
      m (clExtendIndices lv.region ((Famb.VineEstS2.clNormalizedChainEquivΓ hL B' W.wBar β hβ hM9).symm x).1) =
        N.val P.L (sumintBoundary (G.sign lv.c.a.toNode) (fun j => W.wBar + latticePoint P.L (β j))) x) :
    ∀ tt ∈ Bx, ∀ (β : Fin 4 → (Fin P.d → ℤ))
      (hβ : ((G.sign lv.c.a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3),
      sumintBoundary (G.sign lv.c.a.toNode) (fun j => W.wBar + latticePoint P.L (β j)) ∈
        outSet (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η →
      Famb.VineEstS5C.P4.W2.FreeDictΓ hM9 B' hG W hL P.γ P.δ P.η W.wBar β hβ
        (WaveTurbulence.VineEstS3.leafT (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut (Famb.VineEstS5C.P4.W2.LeafPosΓ B lv) (Famb.VineEstS5C.P4.W2.LeafNegΓ B lv) tt)
        (spatialMul m ψ) wN wDec bk cons g g'
        ((OutCharMix.mulC Mx N).freeze (sumintBoundary (G.sign lv.c.a.toNode) (fun j => W.wBar + latticePoint P.L (β j))))
        (allCR Rw) := by
  intro tt htt β hβ hE
  have h1 := freeDict_mulΓ hM9 B' hG W hL P.γ P.δ P.η W.wBar β hβ
    (WaveTurbulence.VineEstS3.leafT (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut (Famb.VineEstS5C.P4.W2.LeafPosΓ B lv) (Famb.VineEstS5C.P4.W2.LeafNegΓ B lv) tt)
    ψ m wN wDec bk cons g g' Mx
    (N.freeze (sumintBoundary (G.sign lv.c.a.toNode) (fun j => W.wBar + latticePoint P.L (β j)))) (allCR Rw)
    (hD tt htt β hβ hE) (fun x => hN β hβ x)
  exact freeDict_val_congrΓ hM9 B' hG W hL P.γ P.δ P.η W.wBar β hβ _ _ wN wDec bk cons g g' _ _ (allCR Rw)
    (fun x => (OutCharMix.mulC_val_freeze Mx N P.L _ x).symm) h1

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WT
open WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS3Par.Eng
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.SumintPar WaveTurbulence.VineEstS3.FS Finset MeasureTheory
open scoped ENNReal
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS5C.P2 WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar MeasureTheory WaveTurbulence.VineEstS5C.P4
open scoped ENNReal
open MeasureTheory DegenVine VineEstS5C VineEstS5C.P2 VineEstS5C.P3 VineEstS5C.P4 RegRed Reg.Skeleton VineParamContract VineEstS2 VineEstS3 VineEstS4 TTree
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence.VineSpaceK (spatialMul freeDict_mul)
open scoped ENNReal
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}
variable {p : ℕ} {kind : Bool} (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
variable {A : ℝ} {P : WTParams}

/-- **T3: the term bound from W2's certificate and an output-dependent pullback** (`Famb.VineEstS5C.P4.W2.termBoundWΓ` for
`spatialMul m ψ`, re-run on the destructured certificate with the product mixture; the only new analytic input is
`SumintMixParDoubledOutAt A P`).  Nothing of W2's construction is re-run. -/
theorem termBoundWOutΓ (hdbO : SumintMixParDoubledOutAt A P) (κ0 : KPar P.d) (hκL : κ0.L = P.L) (hκγ : κ0.γ = P.γ)
    (hκδ : κ0.δ = P.δ) (lv : Famb.VineEstS5C.LvlΓ B) (σ s : ℤˣ) (hσ : σ = G.sign lv.c.a.toNode) (hs : s = σ) {Bx : Set (Fin 3 → ℝ)}
    {K : Set (Fin 4 → Mom P.d)} {β' : ℝ≥0∞} (ψ : PsiT G P.d) (hC : Famb.VineEstS5C.P4.W2.TermCertWΓ (A := A) B hG κ0 lv ψ Bx K β')
    (m : (GNode G.tree → Fin P.d → ℤ) → ℂ) {mass : ℝ} (hpull : EnginePullbackOutΓ (γF := γF) lv.region P.L κ0.base m mass) :
    XNorm00Restr (2 * P.η ^ 8) Bx K (Famb.VineEstS5C.P2.termFnRΓ B σ κ0 lv (spatialMul m ψ) s) ≤
      ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region‖ₑ *
        (ENNReal.ofReal mass * β') := by
  obtain ⟨n', hM9, B', W, wN, wDec, bk, cons, g, g', Z, Rw, hL, hAe, hWs, hbase, hBx, rfl, hind, hD, hβ⟩ := hC
  subst hs hσ
  have hpullW : EnginePullbackOutΓ (γF := γF) lv.region P.L W.wBar m mass := by rw [hbase]; exact hpull
  obtain ⟨N, hNm, hNe⟩ := hpullW n' hM9 B' hL
  have hD' := termCertW_mulOut_dataΓ B hG κ0 lv ψ n' hM9 B' W wN wDec bk cons g g' Z.Mx Rw hL hD m N hNe
  have hind' : ∀ (t : Fin 3 → ℝ) (β' : Fin 4 → Mom P.d) (κ : CLLocalDecoration lv.region P.L W.wBar β')
      (u : GBranch G.tree → ℝ), u lv.c.a = t 0 →
      spatialMul m ψ (clExtendIndices lv.region κ.1) t u = spatialMul m ψ (clExtendIndices lv.region κ.1)
        (WaveTurbulence.VineEstS3.leafT (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut (Famb.VineEstS5C.P4.W2.LeafPosΓ B lv) (Famb.VineEstS5C.P4.W2.LeafNegΓ B lv) t) u := by
    intro t β'' κ u hu
    simp only [VineSpaceK.spatialMul]
    rw [hind t β'' κ u hu]
  have hθ : (0 : ℝ) ≤ 2 * P.η ^ 8 := by have := Z.hη0; positivity
  have hcst : Famb.VineEstS5C.P3.LvlΓ.cstΓ B κ0 lv = (coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region := by
    unfold Famb.VineEstS5C.P3.LvlΓ.cstΓ; rw [hκL, hκγ, hκδ]
  set Ifun : (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ := fun tt E =>
    Famb.VineEstS5C.P3.LvlΓ.cstΓ B κ0 lv * clockedExprMul3 ((OutCharMix.mulC Z.Mx N).freeze E) (allCR Rw) Z.hI P.L P.γ (2 * P.δ) P.η tt E with hIfun
  have h1 : XNorm00Restr (2 * P.η ^ 8) Bx (outSet (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η)
      (Famb.VineEstS5C.P2.termFnRΓ B (G.sign lv.c.a.toNode) κ0 lv (spatialMul m ψ) (G.sign lv.c.a.toNode)) ≤
      XNorm00Restr (2 * P.η ^ 8) Bx (outSet (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η)
        (fun tt E => Ifun (WaveTurbulence.VineEstS3.leafT (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut
          (Famb.VineEstS5C.P4.W2.LeafPosΓ B lv) (Famb.VineEstS5C.P4.W2.LeafNegΓ B lv) tt) E) :=
    XNorm00Restr_mono_of_eq _ _ _ _ _ (fun tt htt E hE =>
      termFnR_leaf_eqOutΓ B hG κ0 hκL hκγ hκδ lv (spatialMul m ψ) n' hM9 B' W wN wDec bk cons g g' Z
        (fun E => (OutCharMix.mulC Z.Mx N).freeze E) Rw hL hbase hind' hD' _ rfl tt htt E hE)
  have h2 : XNorm00Restr (2 * P.η ^ 8) Bx (outSet (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η)
        (fun tt E => Ifun (WaveTurbulence.VineEstS3.leafT (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut
          (Famb.VineEstS5C.P4.W2.LeafPosΓ B lv) (Famb.VineEstS5C.P4.W2.LeafNegΓ B lv) tt) E) ≤
      XNorm00Restr (2 * P.η ^ 8) (boxQ (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut)
        (outSet (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η)
        (fun tt E => Ifun (WaveTurbulence.VineEstS3.leafT (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut
          (Famb.VineEstS5C.P4.W2.LeafPosΓ B lv) (Famb.VineEstS5C.P4.W2.LeafNegΓ B lv) tt) E) :=
    XNorm00Restr_mono_set _ hBx _ _
  have hI : ∀ E ∈ outSet (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η,
      ContinuousOn (fun t => Ifun t E) (WaveTurbulence.VineEstS3.cubeSet (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut) :=
    fun E _ => continuousOn_const.mul (expr_continuousOn_cube Z.hL Z.hI ((OutCharMix.mulC Z.Mx N).freeze E) Z.hη3 Z.hη0 Z.Cph Z.hCph0 Z.hCph
      Z.hreg Rw hWs E)
  have h3 := XNorm00Restr_leafQ hθ (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut
    (outSet (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η) Ifun
    (fun tt E => Ifun (WaveTurbulence.VineEstS3.leafT (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut
      (Famb.VineEstS5C.P4.W2.LeafPosΓ B lv) (Famb.VineEstS5C.P4.W2.LeafNegΓ B lv) tt) E)
    (Famb.VineEstS5C.P4.W2.LeafPosΓ B lv) (Famb.VineEstS5C.P4.W2.LeafNegΓ B lv) hI (fun t _ v _ => rfl)
  have h4 : XNorm00Restr (2 * P.η ^ 8) (boxQ (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut)
      (outSet (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η) Ifun ≤
      ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region‖ₑ *
        XNorm00Restr (2 * P.η ^ 8) (outBox (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g'))
          (outSet (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η)
          (fun tt E => clockedExprMul3 ((OutCharMix.mulC Z.Mx N).freeze E) (allCR Rw) Z.hI P.L P.γ (2 * P.δ) P.η tt E) := by
    rw [hcst] at hIfun
    have := WaveTurbulence.VineEstS3.Eng.XNorm00Restr_const_mul_le (2 * P.η ^ 8)
      (outBox (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g')) (outSet (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η)
      ((coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region)
      (fun tt E => clockedExprMul3 ((OutCharMix.mulC Z.Mx N).freeze E) (allCR Rw) Z.hI P.L P.γ (2 * P.δ) P.η tt E)
    simpa [hIfun, hcst, outBoxPar_eq] using this
  have h5 := allRows_boundOut_mulC hdbO Z N Rw hAe
  have h6 : ENNReal.ofReal N.mass * Z.pre * ∏ ρ, (Rw ρ).b ≤ ENNReal.ofReal mass * (Z.pre * ∏ ρ, (Rw ρ).b) := by
    rw [mul_assoc]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hNm) le_rfl
  calc _ ≤ _ := h1.trans (h2.trans h3)
    _ ≤ Regref.traceConst (r := 3) (2 * P.η ^ 8) WaveTurbulence.VineEstS3.chiUnit ^ 2 *
        (‖(coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region‖ₑ *
          (ENNReal.ofReal mass * (Z.pre * ∏ ρ, (Rw ρ).b))) :=
      mul_le_mul' le_rfl (h4.trans (mul_le_mul' le_rfl (h5.trans h6)))
    _ = ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region‖ₑ *
        (ENNReal.ofReal mass * (Regref.traceConst (r := 3) (2 * P.η ^ 8) WaveTurbulence.VineEstS3.chiUnit ^ 2 *
          (Z.pre * ∏ ρ, (Rw ρ).b))) := by ring
    _ ≤ _ := mul_le_mul' le_rfl (mul_le_mul' le_rfl hβ)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WT
open WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS3Par.Eng
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.SumintPar WaveTurbulence.VineEstS3.FS Finset MeasureTheory
open scoped ENNReal
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS5C.P2 WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar MeasureTheory WaveTurbulence.VineEstS5C.P4
open scoped ENNReal
open MeasureTheory DegenVine VineEstS5C VineEstS5C.P2 VineEstS5C.P3 VineEstS5C.P4 RegRed Reg.Skeleton VineParamContract VineEstS2 VineEstS3 VineEstS4 TTree
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence.VineSpaceK (spatialMul freeDict_mul)
open scoped ENNReal
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}
variable {p : ℕ} {kind : Bool} (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
variable {A : ℝ} {P : WTParams}

/-- **T3: absolute convergence of the term from the certificate and an output-dependent pullback** (`Famb.VineEstS5C.P4.W2.habsWΓ`). -/
theorem habsWOutΓ (κ0 : KPar P.d) (hκL : κ0.L = P.L) (lv : Famb.VineEstS5C.LvlΓ B) (s : ℤˣ) (hs : s = G.sign lv.c.a.toNode)
    {Bx : Set (Fin 3 → ℝ)} {K : Set (Fin 4 → Mom P.d)} {β' : ℝ≥0∞} (ψ : PsiT G P.d)
    (hC : Famb.VineEstS5C.P4.W2.TermCertWΓ (A := A) B hG κ0 lv ψ Bx K β')
    (m : (GNode G.tree → Fin P.d → ℤ) → ℂ) {mass : ℝ} (hpull : EnginePullbackOutΓ (γF := γF) lv.region P.L κ0.base m mass) :
    ∀ tt ∈ Bx, ∀ E ∈ K, LkAbs lv.region κ0.L κ0.base (spatialMul m ψ) tt (sumintBoundary s E) := by
  obtain ⟨n', hM9, B', W, wN, wDec, bk, cons, g, g', Z, Rw, hL, hAe, hWs, hbase, hBx, rfl, hind, hD, hβ⟩ := hC
  subst hs
  have hpullW : EnginePullbackOutΓ (γF := γF) lv.region P.L W.wBar m mass := by rw [hbase]; exact hpull
  obtain ⟨N, _, hNe⟩ := hpullW n' hM9 B' hL
  have hD' := termCertW_mulOut_dataΓ B hG κ0 lv ψ n' hM9 B' W wN wDec bk cons g g' Z.Mx Rw hL hD m N hNe
  have hind' : ∀ (t : Fin 3 → ℝ) (β' : Fin 4 → Mom P.d) (κ : CLLocalDecoration lv.region P.L W.wBar β')
      (u : GBranch G.tree → ℝ), u lv.c.a = t 0 →
      spatialMul m ψ (clExtendIndices lv.region κ.1) t u = spatialMul m ψ (clExtendIndices lv.region κ.1)
        (WaveTurbulence.VineEstS3.leafT (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut (Famb.VineEstS5C.P4.W2.LeafPosΓ B lv) (Famb.VineEstS5C.P4.W2.LeafNegΓ B lv) t) u := by
    intro t β'' κ u hu
    simp only [VineSpaceK.spatialMul]
    rw [hind t β'' κ u hu]
  intro tt htt E hE
  set tt' := WaveTurbulence.VineEstS3.leafT (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut (Famb.VineEstS5C.P4.W2.LeafPosΓ B lv) (Famb.VineEstS5C.P4.W2.LeafNegΓ B lv) tt
    with htt'
  have hmem : tt' ∈ outBox (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g') :=
    WaveTurbulence.VineEstS5C.P4.W2.leafT_mem_boxQ (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut _ _ (hBx htt)
  have hAbs := allRows_abs Z.hL Z.hη0 (Famb.VineEstS2.assemblyShape_I_posΓ hM9 B') ((OutCharMix.mulC Z.Mx N).freeze E) Z.hη3 Z.Cph
    Z.hCph0 Z.hCph Z.hreg Rw hAe tt' hmem E hE
  obtain ⟨β, hβ', rfl⟩ := outSet_exists_beta hL (G.sign lv.c.a.toNode) W.wBar E (fun c => (hE.1 c).1) hE.2.1
  rw [hκL, ← hbase]
  have h0 : tt 0 = tt' 0 :=
    (WaveTurbulence.VineEstS3.leafT_zero (Famb.VineEstS5C.P2.engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut _ _ tt).symm
  have hlk := lkRaw_leaf_eq (P := P) lv.region P.L W.wBar (spatialMul m ψ) tt tt' h0
    (by by_cases h : Famb.VineEstS5C.P4.W2.LeafPosΓ B lv
        · exact Or.inl h
        · exact Or.inr (by rw [htt', WaveTurbulence.VineEstS3.leafT_one]; simp [h]))
    (by by_cases h : Famb.VineEstS5C.P4.W2.LeafNegΓ B lv
        · exact Or.inl h
        · exact Or.inr (by rw [htt', WaveTurbulence.VineEstS3.leafT_two]; simp [h]))
    (fun β' κ u hu => hind' tt β' κ u hu) (sumintBoundary (G.sign lv.c.a.toNode) (sumintBoundary (G.sign lv.c.a.toNode)
      (fun j => W.wBar + latticePoint P.L (β j))))
  refine hlk.2.mpr ?_
  exact Famb.VineEstS5C.P4.W2.lkAbs_of_exprAbs_freeΓ hM9 B' hG W hL P.γ P.δ P.η W.wBar β hβ' tt' (spatialMul m ψ) wN wDec bk cons g g' _
    (allCR Rw) (hD' tt htt β hβ' hE) hAbs

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WT
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul)
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final LGSpine
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.DegenVinePar VineParamContract Set
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P2
open scoped ENNReal
open VineEstS5C.P4.Final
open WaveTurbulence.VineEstS5C.P4.Final
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]

/-- Main's `VineSpaceK.VineFlatC2MX` for every selector, with the selector's top layer `p` and presentation
(`rowSel.weighted = true →`; vacuous for an unweighted selector). -/
def VineFlatC2MXOutΓ (P : WTParams) : Prop :=
  ∀ {p : ℕ}, p < P.D →
    (rowSel.weighted = true → rowSel.p = p ∧ Flower.Stage1W.GPresented (32 * P.d) (rowSel.g P.d) rowSel.cψ) →
    ∀ (h : ℕ → Mom P.d → ℝ) (B₀ : ℝ), 0 ≤ B₀ →
    (∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (h r) ≤ ENNReal.ofReal B₀) →
    ∀ {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
      {n : ℕ} (hprime : IsPrimeGarden G) (hM9 : Famb.NormalChartSupply γF) (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G)
      (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (kind : Bool),
      CanonicalObject p kind (layeredReconstruction RD hG layer hLayer) → (∀ x, layer x ≤ p) →
    (RD.garden hG).order ≤ P.N (p + 1) ^ 4 → clLocalOrder1 R ≤ P.N 1 ^ 4 →
    ∀ (centre : Fin 4 → Mom P.d) (wBar : Mom P.d) (lam : ℝ)
      (m : (GNode G.tree → Fin P.d → ℤ) → ℂ) (mass : ℝ), 0 ≤ mass →
    EnginePullbackOutΓ (γF := γF) (Famb.VineEstS5C.LvlΓ.top B).region P.L wBar m mass →
    Famb.VineEstS3.RowCoherentΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.step3WΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      P.L P.γ P.δ h p →
    XNorm00Restr (2 * P.η ^ 8) (Eng.outBox (Famb.VineEstS3.step3DΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar))
      (Eng.outSet (Famb.VineEstS3.step3DΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar) P.L P.γ P.η)
      (flatFnRMXΓ (p := p) (kind := kind) B RD hG layer hLayer m lam (G.sign a.toNode)
        (kparOf P.L P.γ P.δ (truncF p h) wBar) hprime (G.sign a.toNode)) ≤
    ENNReal.ofReal mass * ENNReal.ofReal ((1 + |lam|) ^ (6 * P.η ^ 6) * ((P.C₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R *
      P.L ^ (-(P.η ^ 8 * ((Famb.VineEstS3.cohmolIndexΓ B RD hG layer +
        (Famb.VineEstS3.step3DΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        P.η ^ 2 * ((Finset.univ.filter fun i => (Famb.VineEstS2.assemblyShapeΓ hM9 B).nor i = false).card : ℝ) + P.η ^ 7) *
      regionLeafSize RD hG R layer hLayer (fun _ => B₀) *
      P.C₂ ^ (Finset.univ.filter fun i => (Famb.VineEstS2.assemblyShapeΓ hM9 B).nor i = false).card))

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WT
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul)
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final LGSpine
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.DegenVinePar VineParamContract Set
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P2
open scoped ENNReal
open VineEstS5C.P4.Final
open WaveTurbulence.VineEstS5C.P4.Final
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]

/-- Main's `VineSpaceK.VineFlatHalfMX` for every selector, with the same selector hypothesis. -/
def VineFlatHalfMXOutΓ (P : WTParams) : Prop :=
  ∀ {p : ℕ}, p < P.D →
    (rowSel.weighted = true → rowSel.p = p ∧ Flower.Stage1W.GPresented (32 * P.d) (rowSel.g P.d) rowSel.cψ) →
    ∀ (h : ℕ → Mom P.d → ℝ) (B₀ : ℝ), 0 ≤ B₀ →
    (∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (h r) ≤ ENNReal.ofReal B₀) →
    ∀ {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
      {n : ℕ} (hprime : IsPrimeGarden G) (hM9 : Famb.NormalChartSupply γF) (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G)
      (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (kind : Bool),
      CanonicalObject p kind (layeredReconstruction RD hG layer hLayer) → (∀ x, layer x ≤ p) →
    (RD.garden hG).order ≤ P.N (p + 1) ^ 4 → clLocalOrder1 R ≤ P.N 1 ^ 4 →
    ∀ (centre : Fin 4 → Mom P.d) (wBar : Mom P.d) (lam : ℝ)
      (m : (GNode G.tree → Fin P.d → ℤ) → ℂ) (mass : ℝ), 0 ≤ mass →
    EnginePullbackOutΓ (γF := γF) (Famb.VineEstS5C.LvlΓ.top B).region P.L wBar m mass →
    Famb.VineEstS3.RowCoherentΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.step3WΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      P.L P.γ P.δ h p →
    XNorm00Restr (2 * P.η ^ 8) (Eng.outBox (Famb.VineEstS3.step3DΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar))
      (Eng.outSet (Famb.VineEstS3.step3DΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar) P.L P.γ P.η)
      (flatFnRMXΓ (p := p) (kind := kind) B RD hG layer hLayer m lam (G.sign a.toNode)
        (kparOf P.L P.γ P.δ (truncF p h) wBar) hprime (G.sign a.toNode)) ≤
    ENNReal.ofReal mass * ENNReal.ofReal ((1 + |lam|) ^ (6 * P.η ^ 6) * ((P.C₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R *
      P.L ^ (-(P.η ^ 8 * ((Famb.VineEstS3.cohmolIndexΓ B RD hG layer +
        (Famb.VineEstS3.step3DΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        P.η ^ 2 / 2 * ((Finset.univ.filter fun i => (Famb.VineEstS2.assemblyShapeΓ hM9 B).nor i = false).card : ℝ) + P.η ^ 7) *
      regionLeafSize RD hG R layer hLayer (fun _ => B₀)))

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WT
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul)
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final LGSpine
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.DegenVinePar VineParamContract Set
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P2
open scoped ENNReal
open VineEstS5C.P4.Final
open WaveTurbulence.VineEstS5C.P4.Final
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {kind : Bool}

/-- `VineFlatC2MXOutΓ` with `0 < B₀` (the form the certificate `Famb.VineEstS5C.P4.Final.UniformTermCertAtKΓ` binds, R105 F8). -/
def VineFlatC2MXPosOutΓ (P : WTParams) : Prop :=
  ∀ {p : ℕ}, p < P.D →
    (rowSel.weighted = true → rowSel.p = p ∧ Flower.Stage1W.GPresented (32 * P.d) (rowSel.g P.d) rowSel.cψ) →
    ∀ (h : ℕ → Mom P.d → ℝ) (B₀ : ℝ), 0 < B₀ →
    (∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (h r) ≤ ENNReal.ofReal B₀) →
    ∀ {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
      {n : ℕ} (hprime : IsPrimeGarden G) (hM9 : Famb.NormalChartSupply γF) (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G)
      (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (kind : Bool),
      CanonicalObject p kind (layeredReconstruction RD hG layer hLayer) → (∀ x, layer x ≤ p) →
    (RD.garden hG).order ≤ P.N (p + 1) ^ 4 → clLocalOrder1 R ≤ P.N 1 ^ 4 →
    ∀ (centre : Fin 4 → Mom P.d) (wBar : Mom P.d) (lam : ℝ)
      (m : (GNode G.tree → Fin P.d → ℤ) → ℂ) (mass : ℝ), 0 ≤ mass →
    EnginePullbackOutΓ (γF := γF) (Famb.VineEstS5C.LvlΓ.top B).region P.L wBar m mass →
    Famb.VineEstS3.RowCoherentΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.step3WΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      P.L P.γ P.δ h p →
    XNorm00Restr (2 * P.η ^ 8) (Eng.outBox (Famb.VineEstS3.step3DΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar))
      (Eng.outSet (Famb.VineEstS3.step3DΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar) P.L P.γ P.η)
      (flatFnRMXΓ (p := p) (kind := kind) B RD hG layer hLayer m lam (G.sign a.toNode)
        (kparOf P.L P.γ P.δ (truncF p h) wBar) hprime (G.sign a.toNode)) ≤
    ENNReal.ofReal mass * ENNReal.ofReal ((1 + |lam|) ^ (6 * P.η ^ 6) * ((P.C₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R *
      P.L ^ (-(P.η ^ 8 * ((Famb.VineEstS3.cohmolIndexΓ B RD hG layer +
        (Famb.VineEstS3.step3DΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        P.η ^ 2 * ((Finset.univ.filter fun i => (Famb.VineEstS2.assemblyShapeΓ hM9 B).nor i = false).card : ℝ) + P.η ^ 7) *
      regionLeafSize RD hG R layer hLayer (fun _ => B₀) *
      P.C₂ ^ (Finset.univ.filter fun i => (Famb.VineEstS2.assemblyShapeΓ hM9 B).nor i = false).card))

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WT
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul)
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final LGSpine
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.DegenVinePar VineParamContract Set
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P2
open scoped ENNReal
open VineEstS5C.P4.Final
open WaveTurbulence.VineEstS5C.P4.Final
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {kind : Bool}

theorem vineFlatC2MXPosOut_coreΓ (Pe : WTParams) (C₁ Km Kr Kb : ℝ) (hKm : 1 ≤ Km) (hKr : 1 ≤ Kr) (hKb : 1 ≤ Kb) (hR : RealityAll)
    (hgate : CoherentGateH Pe) (hinc : IncoherentGateH Pe) (hUC : UniformTermCertAtKSΓ (γF := γF) 6561 Pe Km Kr Kb)
    (htop : Flower.Stage1W.TopIncoherentDecayAt Pe) (hdbO : SumintMixParDoubledOutAt 6561 Pe)
    (hc0 : 1 ≤ Pe.C₁) (hη0 : 0 < Pe.η) (hη1 : Pe.η ≤ 1 / 2) (hL : 2 ≤ Pe.L)
    (hC₁ : (Eng.ccη Pe.η + 1).toReal * countKc * engNs Pe.η Pe.C₁ Km Kr ≤ C₁) (hC₂ : (countKp Pe.D : ℝ) * Kb ≤ Pe.C₂) :
    VineFlatC2MXPosOutΓ (γF := γF) ({Pe with C₁ := C₁} : WTParams) := by
  intro p hp hsp h B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre wBar lam m mass hmass hpull hcoh
  have hL1 : 1 ≤ Pe.L := by linarith
  have hB : ProfileBound Pe (truncF p h) (fun _ => B₀) p := fun r hr => ⟨hB₀.le, by rw [truncF_eq h r hr]; exact hh r hr⟩
  have E : GateEnv Pe (kparOf Pe.L Pe.γ Pe.δ (truncF p h) wBar) p (fun _ => B₀) :=
    ⟨hgate, hB, hp, rfl, by linarith, by linarith, hc0⟩
  have hcohE : Famb.VineEstS3.RowCoherentΓ hM9 B RD hG layer hLayer
      (Famb.VineEstS3.step3WΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      Pe.L Pe.γ Pe.δ (truncF p h) p := hcoh
  have hN : ∀ k, Pe.N k = ({Pe with C₁ := C₁} : WTParams).N k := fun k => (LGSpine.N_largeConstants Pe C₁ Pe.C₂ k).symm
  have hordE : (RD.garden hG).order ≤ Pe.N (p + 1) ^ 4 := by rw [hN]; exact hord
  have hl1E : clLocalOrder1 R ≤ Pe.N 1 ^ 4 := by rw [hN]; exact hl1
  obtain ⟨β', hcert, hβ'⟩ := hUC (truncF p h) B₀ wBar hB₀ E hinc (fun hw => ⟨(hsp hw).1, (hsp hw).2, htop⟩) hprime hM9 B RD hG layer hLayer kind hcan hlay hordE hl1E centre lam hR hcohE
  have hKb0 : 0 < Kb := by linarith only [hKb]
  refine le_trans (wpF_flatBMXΓ (C₂ := Pe.C₂ / Kb) (Λ := mass * (1 + |lam|) ^ (6 * Pe.η ^ 6)) (Ns := engNs Pe.η Pe.C₁ Km Kr) (δ := Pe.δ) (C₁ := C₁)
    (Lp := Kb ^ (Finset.univ.filter fun i => (Famb.VineEstS2.assemblyShapeΓ hM9 B).nor i = false).card *
      Pe.L ^ (-(Pe.η ^ 8 * ((Famb.VineEstS3.cohmolIndexΓ B RD hG layer +
        (Famb.VineEstS3.step3DΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        Pe.η ^ 2 * ((Finset.univ.filter fun i => (Famb.VineEstS2.assemblyShapeΓ hM9 B).nor i = false).card : ℝ) + Pe.η ^ 7))
    (lf := regionLeafSize RD hG R layer hLayer (fun _ => B₀)) (p := p) (kind := kind) B RD hG layer hLayer (hprime' := hprime) hM9 hR E hordE m lam (G.sign a.toNode)
    (G.sign a.toNode) (fun c => ((qOutOf RD hG layer a b R c : ℕ) : ℝ))
    (Bx := WaveTurbulence.VineEstS3.Eng.outBox
      (Famb.VineEstS3.step3DΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar))
    (fun tt ht c => ⟨(ht.1 c).1, (ht.1 c).2⟩)
    (K := WaveTurbulence.VineEstS3.Eng.outSet
      (Famb.VineEstS3.step3DΓ hM9 B RD hG layer hLayer (Famb.VineEstS3.canonBadKindΓ hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      Pe.L Pe.γ Pe.η)
    (WaveTurbulence.VineEstS3.Eng.countable_outSet _ _ _ _) (fun tt ht => ⟨(ht.1 0).1, (ht.1 0).2⟩)
    (fun ψ hψ tt htt E' hE' => habsWOutΓ (P := Pe) (A := 6561) B hG _ rfl (Famb.VineEstS5C.LvlΓ.top B) _ rfl (modPsi b lam ψ)
        (hcert ψ hψ) m hpull tt htt E' hE')
    (D := Pe.D) hp.le ?_ ?_ ?_ ?_ ?_ hC₁ ((le_div_iff₀ hKb0).2 hC₂)) (le_of_eq ?_)
  · intro ψ hψ
    exact (termBoundWOutΓ (P := Pe) (A := 6561) B hG hdbO _ rfl rfl rfl (Famb.VineEstS5C.LvlΓ.top B) (G.sign a.toNode) (G.sign a.toNode)
      rfl rfl (modPsi b lam ψ) (hcert ψ hψ) m hpull).trans (by
        calc
          _ = ENNReal.ofReal mass * (‖(coupling Pe.d Pe.L Pe.γ Pe.δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R‖ₑ * β') := by
            ac_rfl
          _ ≤ ENNReal.ofReal mass * _ := mul_le_mul' (le_refl (ENNReal.ofReal mass)) hβ'
          _ = _ := by rw [← ENNReal.ofReal_mul hmass]; congr 1; ring)
  · exact mul_nonneg hmass (Real.rpow_nonneg (by positivity) _)
  · have h1 : 0 < Km := by linarith
    have h2 : 0 < Kr := by linarith
    have h3 : 0 < Pe.C₁ := by linarith
    unfold engNs
    positivity
  · exact mul_nonneg (pow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)
  · exact regionLeafSize_const_nonneg RD hG R layer hLayer hB₀.le
  · rw [← ENNReal.ofReal_mul hmass]
    congr 1
    rw [div_pow]
    field_simp

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WT
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul)
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final LGSpine
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.DegenVinePar VineParamContract Set
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P2
open scoped ENNReal
open VineEstS5C.P4.Final
open WaveTurbulence.VineEstS5C.P4.Final
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {kind : Bool}

/-- **F8 limit argument for the flat form** (copy of `Famb.VineEstS5C.P4.Final.vineEstCanonLayerC2MK_of_posΓ`): `0 ≤ B₀` from `0 < B₀`. -/
theorem vineFlatC2MXOut_of_posΓ (P : WTParams) (H : VineFlatC2MXPosOutΓ (γF := γF) P) : VineFlatC2MXOutΓ (γF := γF) P := by
  intro p hp hsp h B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre wBar lam m mass
    hmass hpull hcoh
  have e : ∀ a b c d e0 : ℝ, mass * (a * (b * c * e0 * d)) = (mass * (a * (b * c * d))) * e0 :=
    fun a b c d e0 => by ring
  rw [← ENNReal.ofReal_mul hmass]
  conv_rhs => rw [e]
  refine le_regionLeafSize_of_forall_pos RD hG layer hLayer (fun _ => B₀) _ (fun ε hε => ?_)
  have key := H hp hsp h (B₀ + ε) (by linarith) (fun r hr => (hh r hr).trans (ENNReal.ofReal_le_ofReal (by linarith)))
    hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre wBar lam m mass hmass hpull hcoh
  rw [← ENNReal.ofReal_mul hmass] at key
  exact le_of_le_of_eq key (congrArg ENNReal.ofReal (e _ _ _ _ _))

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WT
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul)
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final LGSpine
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.DegenVinePar VineParamContract Set
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P2
open scoped ENNReal
open VineEstS5C.P4.Final
open WaveTurbulence.VineEstS5C.P4.Final
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {kind : Bool}

theorem vineFlatC2MXOut_coreΓ (Pe : WTParams) (C₁ Km Kr Kb : ℝ) (hKm : 1 ≤ Km) (hKr : 1 ≤ Kr) (hKb : 1 ≤ Kb) (hR : RealityAll)
    (hgate : CoherentGateH Pe) (hinc : IncoherentGateH Pe) (hUC : UniformTermCertAtKSΓ (γF := γF) 6561 Pe Km Kr Kb)
    (htop : Flower.Stage1W.TopIncoherentDecayAt Pe) (hdbO : SumintMixParDoubledOutAt 6561 Pe)
    (hc0 : 1 ≤ Pe.C₁) (hη0 : 0 < Pe.η) (hη1 : Pe.η ≤ 1 / 2) (hL : 2 ≤ Pe.L)
    (hC₁ : (Eng.ccη Pe.η + 1).toReal * countKc * engNs Pe.η Pe.C₁ Km Kr ≤ C₁) (hC₂ : (countKp Pe.D : ℝ) * Kb ≤ Pe.C₂) :
    VineFlatC2MXOutΓ (γF := γF) ({Pe with C₁ := C₁} : WTParams) :=
  vineFlatC2MXOut_of_posΓ _ (vineFlatC2MXPosOut_coreΓ Pe C₁ Km Kr Kb hKm hKr hKb hR hgate hinc hUC htop hdbO hc0 hη0 hη1 hL hC₁ hC₂)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WT
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul)
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final LGSpine
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.DegenVinePar VineParamContract Set
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P2
open scoped ENNReal
open VineEstS5C.P4.Final
open WaveTurbulence.VineEstS5C.P4.Final
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {kind : Bool}

/-- **R54 (ii) from (i), modulated, for every selector** (the selector is bound after the record). -/
theorem vineFlatHalfMXOut_of_C2MXΓ (H : WTPrefix fun P => ∀ {u : Unit} [_I : VineEst.RowSel u], VineFlatC2MXOutΓ (γF := γF) P) :
    WTPrefix fun P => ∀ {u : Unit} [_I : VineEst.RowSel u], VineFlatHalfMXOutΓ (γF := γF) P := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H1⟩ := H d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin hφin τ hτ φ hsol => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H2⟩ := H1 η hη φin hφin τ hτ φ hsol
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H3⟩ := H2 ν hν
  refine ⟨δ₀, hδ₀, fun δ hδ D hD htime => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H4⟩ := H3 δ hδ D hD htime
  refine ⟨C₂, hC₂, max L₀ (C₂ ^ (2 / η ^ 2)), le_max_of_le_left hL₀, fun L hL => ?_⟩
  have hLL₀ : L₀ ≤ L := (le_max_left _ _).trans hL
  have hLC : C₂ ^ (2 / η ^ 2) ≤ L := (le_max_right _ _).trans hL
  have hLpos : 0 < L := by linarith
  intro u _I
  have key : VineFlatC2MXOutΓ (γF := γF) ⟨d, γ, η, φin, τ, φ, C₁, ν, δ, D, C₂, L⟩ := H4 L hLL₀
  intro p hp hsp h B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre wBar lam m mass hmass hpull hcoh
  refine (key hp hsp h B₀ hB₀ hh hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre wBar lam m mass hmass hpull hcoh).trans ?_
  refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
  have hδ0 : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg _
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by positivity) _)
  exact half_of_C2_real (pow_nonneg (mul_nonneg (by linarith) hδ0) _)
    (regionLeafSize_const_nonneg RD hG R layer hLayer hB₀) hLpos (C2_pow_le _ hη.1 hC₂ hLC)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WT
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul)
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final LGSpine
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.DegenVinePar VineParamContract Set
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P2
open scoped ENNReal
open VineEstS5C.P4.Final
open WaveTurbulence.VineEstS5C.P4.Final
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]

/-- **The weighted flat estimate for every selector, on the prefix** (V5W-A's `vineFlatC2MX_of_uniformCertΓ` with the
selector certificate `UniformTermCertTargetKSΓ` and INC-TOP's gate). -/
theorem vineFlatC2MXOut_of_uniformCertΓ (hU : UniformTermCertTargetKSΓ (γF := γF)) (hG : LeafwiseCoherentApproximationGate)
    (hI : LeafwiseIncoherentDecayGate) (hR : RealityAll) (hT : Flower.Stage1W.TopIncoherentDecayGateR) :
    WTPrefix fun P => ∀ {u : Unit} [_I : VineEst.RowSel u], VineFlatC2MXOutΓ (γF := γF) P := by
  have hI : WTPrefix fun P => LeafwiseIncoherentDecayAt P ∧ Flower.Stage1W.TopIncoherentDecayAtR P :=
    prefix_and hI hT leafwiseIncoherentDecay_largeConstantMonotone
      Flower.Stage1WNoVine.topIncoherentDecayAtR_largeConstantMonotone
  intro d hd γ hγ
  obtain ⟨ηU, hηU, hUa⟩ := hU d hd γ hγ
  obtain ⟨ηS, hηS, hSa⟩ := prefixA_and (Q₁ := SumintMixParDoubledAt) (Q₂ := SumintMixParDoubledOutAt)
    sumintMixParDoubled sumintMixParDoubledOut sumintMixPar_mono sumintMixParOut_mono d hd γ hγ
  obtain ⟨ηG, hηG, hGa⟩ := hG d hd γ hγ
  obtain ⟨ηI, hηI, hIa⟩ := hI d hd γ hγ
  refine ⟨min (min ηU (min ηS (min ηG ηI))) (1 / 5), lt_min (lt_min hηU (lt_min hηS (lt_min hηG hηI))) (by norm_num), ?_⟩
  intro η hη φin hφin τ hτ φ hsol
  have hη0 : 0 < η := hη.1
  have hm : η ≤ min ηU (min ηS (min ηG ηI)) := hη.2.trans (min_le_left _ _)
  have hη5 : η ≤ 1 / 5 := hη.2.trans (min_le_right _ _)
  have hηU' : η ∈ Ioc 0 ηU := ⟨hη0, hm.trans (min_le_left _ _)⟩
  have hηS' : η ∈ Ioc 0 ηS := ⟨hη0, hm.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hηG' : η ∈ Ioc 0 ηG := ⟨hη0, hm.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))⟩
  have hηI' : η ∈ Ioc 0 ηI := ⟨hη0, hm.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))⟩
  obtain ⟨CS, hCS, νS, hνS, hSb⟩ := hSa η hηS' 6561 (by norm_num) φin hφin τ hτ φ hsol
  obtain ⟨CG, hCG, νG, hνG, hGb⟩ := hGa η hηG' φin hφin τ hτ φ hsol
  obtain ⟨CI, hCI, νI, hνI, hIb⟩ := hIa η hηI' φin hφin τ hτ φ hsol
  set c₀ : ℝ := max (max CS CG) CI with hc₀d
  have hc₀ : 1 ≤ c₀ := hCS.trans ((le_max_left _ _).trans (le_max_left _ _))
  have hCSc : CS ≤ c₀ := (le_max_left _ _).trans (le_max_left _ _)
  have hCGc : CG ≤ c₀ := (le_max_right _ _).trans (le_max_left _ _)
  have hCIc : CI ≤ c₀ := le_max_right _ _
  obtain ⟨Km, Kr, hKm, hKr, hUb⟩ := hUa η hηU' φin hφin τ hτ φ hsol c₀ hc₀
  set C₁ : ℝ := max 1 ((Eng.ccη η + 1).toReal * countKc * engNs η c₀ Km Kr) with hC₁d
  refine ⟨C₁, le_max_left _ _, min νS (min νG νI), lt_min hνS (lt_min hνG hνI), ?_⟩
  intro ν hν
  have hνS' : ν ∈ Ioc 0 νS := ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  have hνG' : ν ∈ Ioc 0 νG := ⟨hν.1, hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hνI' : ν ∈ Ioc 0 νI := ⟨hν.1, hν.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  obtain ⟨δS, hδS, hSc⟩ := hSb ν hνS'
  obtain ⟨δG, hδG, hGc⟩ := hGb ν hνG'
  obtain ⟨δI, hδI, hIc⟩ := hIb ν hνI'
  refine ⟨min δS (min δG δI), lt_min hδS (lt_min hδG hδI), ?_⟩
  intro δ hδ D hD htime
  have hδS' : δ ∈ Ioc 0 δS := ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩
  have hδG' : δ ∈ Ioc 0 δG := ⟨hδ.1, hδ.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hδI' : δ ∈ Ioc 0 δI := ⟨hδ.1, hδ.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  obtain ⟨Kb, hKb, hUb'⟩ := hUb ν δ D hδ.1 htime
  obtain ⟨C₂S, hC₂S, LS, hLS, hSd⟩ := hSc δ hδS' D hD htime
  obtain ⟨C₂G, hC₂G, LG, hLG, hGd⟩ := hGc δ hδG' D hD htime
  obtain ⟨C₂I, hC₂I, LI, hLI, hId⟩ := hIc δ hδI' D hD htime
  refine ⟨max (max C₂S (max C₂G C₂I)) (countKp D * Kb), hC₂S.trans ((le_max_left _ _).trans (le_max_left _ _)), max LS (max LG LI),
    hLS.trans (le_max_left _ _), ?_⟩
  intro L hL
  have hLS' : LS ≤ L := (le_max_left _ _).trans hL
  have hLG' : LG ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hL
  have hLI' : LI ≤ L := ((le_max_right _ _).trans (le_max_right _ _)).trans hL
  have hL2 : 2 ≤ L := hLS.trans hLS'
  set C₂ : ℝ := max (max C₂S (max C₂G C₂I)) (countKp D * Kb) with hC₂d
  have hC₂S' : C₂S ≤ C₂ := (le_max_left _ _).trans (le_max_left _ _)
  have hC₂G' : C₂G ≤ C₂ := (le_max_of_le_right (le_max_left _ _)).trans (le_max_left _ _)
  have hC₂I' : C₂I ≤ C₂ := (le_max_of_le_right (le_max_right _ _)).trans (le_max_left _ _)
  have hC₂K : (countKp D : ℝ) * Kb ≤ C₂ := le_max_right _ _
  let PS : WTParams := ⟨d, γ, η, φin, τ, φ, CS, ν, δ, D, C₂S, L⟩
  let PG : WTParams := ⟨d, γ, η, φin, τ, φ, CG, ν, δ, D, C₂G, L⟩
  let PI : WTParams := ⟨d, γ, η, φin, τ, φ, CI, ν, δ, D, C₂I, L⟩
  let Pe : WTParams := ⟨d, γ, η, φin, τ, φ, c₀, ν, δ, D, C₂, L⟩
  have hdb : SumintMixParDoubledAt 6561 Pe :=
    sumintMixPar_mono 6561 PS c₀ C₂ hCS hC₂S hδ.1 hL2 hCSc hC₂S' (hSd L hLS').1
  have hdbO : SumintMixParDoubledOutAt 6561 Pe :=
    sumintMixParOut_mono 6561 PS c₀ C₂ hCS hC₂S hδ.1 hL2 hCSc hC₂S' (hSd L hLS').2
  have hgate : CoherentGateH Pe :=
    coherentGateH_of (leafwiseCoherentAt_largeConstantMonotone PG c₀ C₂ hCG hC₂G hδ.1 (hLG.trans hLG') hCGc hC₂G'
      (hGd L hLG'))
  have hIT := (leafwiseIncoherentDecay_largeConstantMonotone.and
    Flower.Stage1WNoVine.topIncoherentDecayAtR_largeConstantMonotone) PI c₀ C₂ hCI hC₂I hδ.1 (hLI.trans hLI') hCIc hC₂I'
      (hId L hLI')
  have hinc : IncoherentGateH Pe := incoherentGateH_of hIT.1
  have htop : Flower.Stage1W.TopIncoherentDecayAt Pe := Flower.Stage1W.topIncoherentDecayAt_of_R _ hIT.2
  have hη6 : 6 * η ^ 6 ≤ η := by
    have h5 : η ^ 5 ≤ (1 / 5 : ℝ) ^ 5 := pow_le_pow_left₀ hη0.le hη5 5
    calc 6 * η ^ 6 = 6 * η ^ 5 * η := by ring
      _ ≤ 6 * (1 / 5) ^ 5 * η := by gcongr
      _ ≤ η := by nlinarith
  have hAmb : AmbP 6561 Pe :=
    ⟨hdb, by show 0 < L; linarith, hη0, by show η ≤ 1 / 2; linarith, by show η < 1 / 4; linarith,
      by show 0 ≤ c₀; linarith, hδ.1, by show 1 ≤ d; omega, by show 6 * η ^ 6 ≤ 1 - η; linarith, hη6,
      by show 3 * η ≤ 1; linarith⟩
  intro u _I
  have hUC : UniformTermCertAtKSΓ (γF := γF) 6561 Pe Km Kr Kb := hUb' C₂ L hL2 hAmb
  have key : VineFlatC2MXOutΓ (γF := γF) ({Pe with C₁ := C₁} : WTParams) := vineFlatC2MXOut_coreΓ Pe C₁ Km Kr Kb hKm hKr hKb hR hgate
    hinc hUC htop hdbO hc₀ hη0 (by show η ≤ 1 / 2; linarith) hL2 (le_max_right _ _) hC₂K
  exact @key

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WT
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul)
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final LGSpine
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.DegenVinePar VineParamContract Set
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P2
open scoped ENNReal
open VineEstS5C.P4.Final
open WaveTurbulence.VineEstS5C.P4.Final
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]

/-- **`WTPrefix VineFlatHalfMXΓ`** for every selector, from the same inputs. -/
theorem vineFlatHalfMXOut_of_uniformCertΓ (hU : UniformTermCertTargetKSΓ (γF := γF)) (hG : LeafwiseCoherentApproximationGate)
    (hI : LeafwiseIncoherentDecayGate) (hR : RealityAll) (hT : Flower.Stage1W.TopIncoherentDecayGateR) :
    WTPrefix fun P => ∀ {u : Unit} [_I : VineEst.RowSel u], VineFlatHalfMXOutΓ (γF := γF) P :=
  vineFlatHalfMXOut_of_C2MXΓ (vineFlatC2MXOut_of_uniformCertΓ hU hG hI hR hT)

end

end WaveTurbulence.GammaLow.Flower
