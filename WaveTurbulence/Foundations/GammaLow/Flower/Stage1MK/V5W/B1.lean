/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.V5W.A
public import WaveTurbulence.Foundations.Flower.V5WB.K.Defs
public import WaveTurbulence.Foundations.Flower.V5WB.B.Nest
public import WaveTurbulence.Foundations.Flower.V5WB.B.Flat
public import WaveTurbulence.Foundations.Flower.V5WB.K.FlatBound
public import WaveTurbulence.Foundations.Flower.V5WA.Instance
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyShape
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainAssembly
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.BadClause
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.CohmolBound
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.LayerFacts
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.Step3At
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.Step3Data
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.Class
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelAbs2
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelAbs3
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelFlat
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelLoc2
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelRec
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelRecurse
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelTop
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P2.Recentered
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P3.Bound
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P3.Unroll
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.Bot.Family
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.Bot.Terms
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.Family
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.Final.BotCount
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.FlatMod.Flat
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.UnrollR
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W13.SFFam
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W13.WPF
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.WinChain

/-! # FLOWER-LOW (packet L8), item I3 (B1): the weighted vine estimate (V5W) over `𝒱_γ`

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
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul)
open MeasureTheory VineEstS5C VineEstS5C.Cont VineEstS4 LFTwist RegRed Reg.Skeleton
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final LGSpine
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {kind : Bool}
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The weighted flat observable of the top level: `recFac · c ζ · lkRaw (modPsi b λ psiFuel)`. -/
noncomputable def flatFnRMXΓ (m : (GNode G.tree → Fin d → ℤ) → ℂ) (lam : ℝ) (σ : ℤˣ) (κ0 : KPar d) (hprime : IsPrimeGarden G) (s : ℤˣ) :
    (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ :=
  fun tt E => recFac σ s κ0.L κ0.γ κ0.δ tt E * (Famb.VineEstS5C.P3.LvlΓ.cstΓ B κ0 (Famb.VineEstS5C.LvlΓ.top B) *
    lkRaw (Famb.VineEstS5C.LvlΓ.top B).region κ0.L κ0.base
      (spatialMul m (modPsi b lam (Famb.VineEstS5C.LvlΓ.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (Fintype.card (Famb.VineEstS5C.LvlΓ.top B).ι + 1) (Famb.VineEstS5C.LvlΓ.top B))))
      tt (sumintBoundary s E))

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul)
open MeasureTheory VineEstS5C VineEstS5C.Cont VineEstS4 LFTwist RegRed Reg.Skeleton
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final LGSpine
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul)
open MeasureTheory VineEstS5C VineEstS5C.Cont VineEstS4 LFTwist RegRed Reg.Skeleton
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final LGSpine
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
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

/-- **The bond-weighted modulated class sum of a level.** -/
noncomputable def classSumBΓ (lam : ℝ) (ψ : WD d) (lv : Famb.VineEstS5C.LvlΓ B) (κ0 : KPar d) (t0 t1 t2 : ℝ)
    (e f g h : Mom d) : ℂ :=
  ∑ z ∈ canonFinsetK p kind (lv.state B RD hG layer hLayer) lv.c,
    memberB {κ0 with t0 := t0, t1 := t1, t2 := t2, e := e, f := f, g := g, h := h} lam ψ z.1 z.2

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
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
theorem classSumB_nestedΓ (lam : ℝ) (ψ : WD d) (C : ℝ) (hC : 0 ≤ C)
    (hψ : ∀ q q' k, ‖ψ.ψ q q' k‖ ≤ C) (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|)
    (hprime : IsPrimeGarden G) (lv : Famb.VineEstS5C.LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val)
    (hA0 : ∀ j, j ∉ {j | (lv.e j).1.val < (lv.e pstar).1.val} → j ≠ pstar →
      IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j))
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    classSumBΓ (p := p) (kind := kind) B RD hG layer hLayer lam ψ lv κ0 t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 (lv.split B RD hG layer hLayer pstar hk).RS *
        clLocalZeta (lv.split B RD hG layer hLayer pstar hk).RS *
        ∑' x : ExtS (lv.split B RD hG layer hLayer pstar hk).RS κ0.L κ0.base e f,
          ∫ σ : CLInternalTime (lv.split B RD hG layer hLayer pstar hk).RS,
            bWN ψ κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk).sb.U x.1 *
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
  have h1 := tildeJ2_B_canon (p := p) (kind := kind) κ lam ψ C hC hψ A' sp hprime hA0 hL hF
  have hKt := KtilB_eq_canon (p := p) (kind := kind) hc
    (Subtype.val : {j : lv.ι // (lv.e j).1.val < (lv.e pstar).1.val} → lv.ι)
    Subtype.val_injective (fun j => j.2) (fun i hi => ⟨⟨i, hi⟩, rfl⟩) κ lam ψ hprime sp hA0
  have e1 : classSumBΓ (p := p) (kind := kind) B RD hG layer hLayer lam ψ lv κ0 t0 t1 t2 e f g h =
      ∑ G ∈ zpFinset p kind pstar _ A' sp hprime,
        sSumBAt κ ψ G.1 G.2 (ktildeB (p := p) (kind := kind) κ lam ψ A' sp hprime G) := h1
  rw [e1]
  rw [Finset.sum_congr rfl (fun Z hZ => zp_stateBW κ lam ψ A' sp hprime hZ), ← Finset.mul_sum,
    weighted_bundle_sumB κ lam ψ C hC hψ A' sp hprime hA0 hL hF (bWN ψ κ A' sp.sb.U)
      (bWNB ψ A' sp.sb.U C) (bWNB_nonneg _ _ _ hC) (fun x => norm_bWN_le ψ κ A' sp.sb.U C hψ x)]
  congr 1
  refine tsum_congr fun x => integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
  beta_reduce
  rw [hKt]
  rfl

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory WaveTurbulence.VineEstS5C.FlatMod WaveTurbulence.VineEstS5C.Cont VineEstS5C
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {kind : Bool}
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The bond weight of a level region, on the representative chart. -/
noncomputable def lvWΓ (ψ : WD d) (κ0 : KPar d) (lv : Famb.VineEstS5C.LvlΓ B) : (GNode G.tree → Fin d → ℤ) → ℂ :=
  bWN ψ κ0 (lv.state B RD hG layer hLayer) lv.c.U

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory WaveTurbulence.VineEstS5C.FlatMod WaveTurbulence.VineEstS5C.Cont VineEstS5C
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {kind : Bool}
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The base case: no operative member. -/
theorem classSumB_baseΓ (lam : ℝ) (ψ : WD d) (κ0 : KPar d) (hprime : IsPrimeGarden G) (lv : Famb.VineEstS5C.LvlΓ B)
    (hno : ∀ j, IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j))
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    classSumBΓ (p := p) (kind := kind) B RD hG layer hLayer lam ψ lv κ0 t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
        lkRaw lv.region κ0.L κ0.base (spatialMul (lvWΓ B RD hG layer hLayer ψ κ0 lv)
          (modPsi b lam (lv.psiBase B RD hG layer hLayer κ0))) ![t0, t1, t2] ![e, f, g, h] := by
  classical
  have hp' : IsPrimeGarden (lv.state B RD hG layer hLayer).skeleton := hprime
  unfold classSumBΓ
  rw [canonFinset_of_noop (lv.state B RD hG layer hLayer) hp' lv.c hno, Finset.sum_singleton]
  unfold memberB
  have hh := memberMX_eq_lkRaw (lv.state B RD hG layer hLayer).data
    (lv.state B RD hG layer hLayer).plain lv.region lam κ0.L κ0.γ κ0.δ κ0.F
    (stateLayer (lv.state B RD hG layer hLayer)) (stateLayer_isLayering _) κ0.base
    (lvWΓ B RD hG layer hLayer ψ κ0 lv) t0 t1 t2 e f g h
  have hb : modPsi lv.c.b lam (lv.psiBase B RD hG layer hLayer κ0) =
      modPsi b lam (lv.psiBase B RD hG layer hLayer κ0) := by rw [lv.hcb]
  exact hh.trans (congrArg (fun Ψ => (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
    lkRaw lv.region κ0.L κ0.base (spatialMul (lvWΓ B RD hG layer hLayer ψ κ0 lv) Ψ) ![t0,t1,t2] ![e,f,g,h]) hb)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory WaveTurbulence.VineEstS5C.FlatMod WaveTurbulence.VineEstS5C.Cont VineEstS5C
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {kind : Bool}
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The bottom case: one operative bottom vine. -/
theorem classSumB_bottomΓ (lam : ℝ) (ψ : WD d) (C : ℝ) (hC : 0 ≤ C) (hψ : ∀ q q' k, ‖ψ.ψ q q' k‖ ≤ C)
    (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|)
    (hprime : IsPrimeGarden G) (lv : Famb.VineEstS5C.LvlΓ B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0)
    (hup : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j))
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    classSumBΓ (p := p) (kind := kind) B RD hG layer hLayer lam ψ lv κ0 t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
        lkRaw lv.region κ0.L κ0.base
          (spatialMul (lvWΓ B RD hG layer hLayer ψ κ0 lv)
            (modPsi b lam (WaveTurbulence.VineEstS5B2.psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c pstar)))
          ![t0, t1, t2] ![e, f, g, h] := by
  let κ : KPar d := {κ0 with t0 := t0, t1 := t1, t2 := t2, e := e, f := f, g := g, h := h}
  have hh := sum_memberB_bottom_eq_flat (p := p) (kind := kind) κ lam ψ C hC hψ
    (lv.state B RD hG layer hLayer) lv.c hprime
    (Famb.VineEstS5C.LvlΓ.bottom_hb0 B RD hG layer hLayer lv pstar h0) hup hL hF
  have hb : modPsi lv.c.b lam (WaveTurbulence.VineEstS5B2.psiBot p kind κ (lv.state B RD hG layer hLayer) lv.c pstar) =
      modPsi b lam (WaveTurbulence.VineEstS5B2.psiBot p kind κ0 (lv.state B RD hG layer hLayer) lv.c pstar) := by
    rw [lv.hcb]
    rfl
  exact hh.trans (congrArg (fun Ψ => (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
    lkRaw lv.region κ0.L κ0.base (spatialMul (lvWΓ B RD hG layer hLayer ψ κ0 lv) Ψ) ![t0,t1,t2] ![e,f,g,h]) hb)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory WaveTurbulence.VineEstS5C.FlatMod WaveTurbulence.VineEstS5C.Cont VineEstS5C
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {kind : Bool}
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- **One level, flat form, bond-weighted.** -/
theorem classSumB_flat_stepΓ (lam : ℝ) (ψ : WD d) (C : ℝ) (hC : 0 ≤ C) (hψ : ∀ q q' k, ‖ψ.ψ q q' k‖ ≤ C)
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
    classSumBΓ (p := p) (kind := kind) B RD hG layer hLayer lam ψ lv κ0 t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
        lkRaw lv.region κ0.L κ0.base
          (spatialMul (lvWΓ B RD hG layer hLayer ψ κ0 lv)
            (modPsi b lam (Famb.VineEstS5C.LvlΓ.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime Ψ')))
          ![t0, t1, t2] ![e, f, g, h] := by
  have hcomm : psiStepSp (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime (modPsi b lam (spatialMul (lvWΓ B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk)) Ψ')) =
      modPsi b lam (spatialMul (fun x => (lvWΓ B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk)) (rB (lv.split B RD hG layer hLayer pstar hk).RT x))
        (Famb.VineEstS5C.LvlΓ.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime Ψ')) := by
    exact (psiStepSp_modPsi κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime b lam _).trans
      (congrArg (modPsi b lam) (psiStepSp_spatialMul κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime (lvWΓ B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk)) Ψ'))
  have hbT : b ∈ (lv.split B RD hG layer hLayer pstar hk).tb.U := Famb.VineEstS5C.LvlΓ.b_mem B (lv.next B RD hG layer hLayer pstar hk)
  rw [classSumB_nestedΓ (p := p) (kind := kind) B RD hG layer hLayer lam ψ C hC hψ κ0 hL hF hprime lv pstar hk hA0
    t0 t1 t2 e f g h]
  have hAbs' : GlueAbsConv (lv.split B RD hG layer hLayer pstar hk).RU (lv.split B RD hG layer hLayer pstar hk).RS (lv.split B RD hG layer hLayer pstar hk).RT κ0.L κ0.base t0 t1 t2 e f g h
      (psiStepSp (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime (modPsi b lam (spatialMul (lvWΓ B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk)) Ψ'))) := by
    rw [hcomm]
    refine glueAbsConv_modPsi _ _ _ κ0.L κ0.base t0 t1 t2 e f g h _ ?_ b lam
    exact glueAbsConv_spatialMul (lv.split B RD hG layer hLayer pstar hk).RU (lv.split B RD hG layer hLayer pstar hk).RS (lv.split B RD hG layer hLayer pstar hk).RT κ0.L κ0.base t0 t1 t2 e f g h _ hAbs
      (fun x => (lvWΓ B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk)) (rB (lv.split B RD hG layer hLayer pstar hk).RT x)) (bWNB ψ ((lv.next B RD hG layer hLayer pstar hk).state B RD hG layer hLayer) (lv.next B RD hG layer hLayer pstar hk).c.U C)
      (fun x => norm_bWN_le ψ κ0 ((lv.next B RD hG layer hLayer pstar hk).state B RD hG layer hLayer) (lv.next B RD hG layer hLayer pstar hk).c.U C hψ _)
  have hmerge := flat_merge_W (p := p) (kind := kind) κ0 hL (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime (bWN ψ κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk).sb.U)
    (bWNB ψ (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk).sb.U C) (fun x => norm_bWN_le ψ κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk).sb.U C hψ x)
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
  have hw : ∀ x : GNode G.tree → Fin d → ℤ, lvWΓ B RD hG layer hLayer ψ κ0 lv x =
      bWN ψ κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk).sb.U (rA (lv.split B RD hG layer hLayer pstar hk).RS x) * (lvWΓ B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk)) (rB (lv.split B RD hG layer hLayer pstar hk).RT x) := by
    intro x
    unfold lvWΓ bWN
    rw [hcU, bondWD_union (ΨX ψ (lv.state B RD hG layer hLayer)) κ0.L κ0.base (layX (lv.state B RD hG layer hLayer)) (lv.split B RD hG layer hLayer pstar hk).sb.block (lv.split B RD hG layer hLayer pstar hk).hT (lv.split B RD hG layer hLayer pstar hk).hi (lv.split B RD hG layer hLayer pstar hk).hU x,
      bondWD_rA (ΨX ψ (lv.state B RD hG layer hLayer)) κ0.L κ0.base (layX (lv.state B RD hG layer hLayer)) (lv.split B RD hG layer hLayer pstar hk).RS x]
    congr 1
    exact (bondWD_rB (ΨX ψ (lv.state B RD hG layer hLayer)) κ0.L κ0.base (layX (lv.state B RD hG layer hLayer)) (lv.split B RD hG layer hLayer pstar hk).RT x).symm
  have hΨ := spatialMul_combine (G' := G) (lvWΓ B RD hG layer hLayer ψ κ0 lv) (bWN ψ κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk).sb.U) (lvWΓ B RD hG layer hLayer ψ κ0 (lv.next B RD hG layer hLayer pstar hk))
    (rA (lv.split B RD hG layer hLayer pstar hk).RS) (rB (lv.split B RD hG layer hLayer pstar hk).RT) b lam (Famb.VineEstS5C.LvlΓ.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime Ψ') hw
  refine hmerge.trans ((congrArg (fun Ψ => (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region *
    clLocalZeta lv.region * lkRaw lv.region κ0.L κ0.base
      (spatialMul (fun x => bWN ψ κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk).sb.U (rA (lv.split B RD hG layer hLayer pstar hk).RS x)) Ψ) ![t0, t1, t2] ![e, f, g, h]) hcomm).trans ?_)
  exact congrArg (fun Ψ => (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
    lkRaw lv.region κ0.L κ0.base Ψ ![t0, t1, t2] ![e, f, g, h]) hΨ

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory WaveTurbulence.VineEstS5C.FlatMod WaveTurbulence.VineEstS5C.Cont VineEstS5C
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {kind : Bool}
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- **The bond-weighted modulated induction over the core vines.** -/
theorem classSumB_flatΓ (lam : ℝ) (ψ : WD d) (C : ℝ) (hC : 0 ≤ C) (hψ : ∀ q q' k, ‖ψ.ψ q q' k‖ ≤ C)
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
      classSumBΓ (p := p) (kind := kind) B RD hG layer hLayer lam ψ lv κ0 t0 t1 t2 e f g h =
        (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
          lkRaw lv.region κ0.L κ0.base
            (spatialMul (lvWΓ B RD hG layer hLayer ψ κ0 lv)
              (modPsi b lam (Famb.VineEstS5C.LvlΓ.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1) lv)))
            ![t0, t1, t2] ![e, f, g, h] := by
  intro m
  induction m with
  | zero =>
    intro lv hc t0 t1 t2 e f g h
    have hno : ∀ j, IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j) := by
      intro j
      have : Fintype.card lv.ι = 0 := Nat.le_zero.mp hc
      exact ((Fintype.card_eq_zero_iff.mp this).false j).elim
    have hnop : ¬ ∃ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j := fun ⟨j, hj⟩ => (hno j).false hj.some
    rw [classSumB_baseΓ (p := p) (kind := kind) B RD hG layer hLayer lam ψ κ0 hprime lv hno]
    simp only [Famb.VineEstS5C.LvlΓ.psiFuel, hnop, dite_false]
  | succ m ih =>
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
        exact classSumB_bottomΓ (p := p) (kind := kind) B RD hG layer hLayer lam ψ C hC hψ κ0 hL hF hprime lv pstar h0 hup
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
      have hIH := fun t0 t1 t2 e f g h => ih (lv.next B RD hG layer hLayer pstar hk) hcard t0 t1 t2 e f g h
      have hstep : Famb.VineEstS5C.LvlΓ.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1 + 1) lv =
          Famb.VineEstS5C.LvlΓ.psiStep (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar hk hprime
            (Famb.VineEstS5C.LvlΓ.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (m + 1) (lv.next B RD hG layer hLayer pstar hk)) := by
        rw [Famb.VineEstS5C.LvlΓ.psiFuel, dite_eq_left hop]
        exact dite_eq_left hk
      rw [hstep]
      exact classSumB_flat_stepΓ (p := p) (kind := kind) B RD hG layer hLayer lam ψ C hC hψ κ0 hL hF hprime lv pstar hk hA0 _
        hIH (hlocS lv pstar hk) (fun x t' u u' hu => hlocPsi (m + 1) (lv.next B RD hG layer hLayer pstar hk) x t' u u' hu)
        t0 t1 t2 e f g h (hAbs (m + 1) lv pstar hk t0 t1 t2 e f g h)
    · have hno : ∀ j, IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j) :=
        fun j => ⟨fun op => hop ⟨j, ⟨op⟩⟩⟩
      rw [classSumB_baseΓ (p := p) (kind := kind) B RD hG layer hLayer lam ψ κ0 hprime lv hno]
      simp only [Famb.VineEstS5C.LvlΓ.psiFuel, hop, dite_false]

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory WaveTurbulence.VineEstS5C.FlatMod WaveTurbulence.VineEstS5C.Cont VineEstS5C
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {kind : Bool}
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

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
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
variable {κ0 : KPar d} {hprime : IsPrimeGarden G}
variable (BE : Famb.VineEstS5C.P3.BundleExpFamΓ (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime) (BX : Famb.VineEstS5C.P4.Bot.BotExpFamΓ (p := p) (kind := kind) B RD hG layer hLayer κ0)

/-- **The modulated top-level bound** (`top_boundRB` with `modPsi b λ`). -/
theorem top_boundRBMXΓ (m : (GNode G.tree → Fin d → ℤ) → ℂ) (hW : Famb.VineEstS5C.P4.WinOfExtΓ B RD hG layer hLayer BE) (hWB : Famb.VineEstS5C.P4.Bot.WinOfExtBotΓ B RD hG layer hLayer BX) (lam : ℝ) (σ : ℤˣ)
    (s : ℤˣ) {θ : ℝ} (hθ : 0 ≤ θ) (q : Fin 3 → ℝ) {Bx : Set (Fin 3 → ℝ)} (hBx : Bx ⊆ cell q)
    {K : Set (Fin 4 → Mom d)} (hK : K.Countable)
    (hq : ∀ tt ∈ Bx, (layer (RD.coreBranch hG a).toNode : ℝ) ≤ tt 0 ∧ tt 0 ≤ layer (RD.coreBranch hG a).toNode + 1)
    (habs : ∀ ψ ∈ Famb.VineEstS5C.P4.Bot.LvlΓ.termsBΓ (p := p) (kind := kind) B RD hG layer hLayer BE BX (Fintype.card (Famb.VineEstS5C.LvlΓ.top B).ι + 1) (Famb.VineEstS5C.LvlΓ.top B),
      ∀ tt ∈ openTop Bx (layer (RD.coreBranch hG a).toNode : ℝ), ∀ E ∈ K,
      LkAbs (Famb.VineEstS5C.LvlΓ.top B).region κ0.L κ0.base (spatialMul m (modPsi b lam ψ)) tt (sumintBoundary s E))
    (β : ℝ≥0∞)
    (TermBoundR : ∀ ψ ∈ Famb.VineEstS5C.P4.Bot.LvlΓ.termsBΓ (p := p) (kind := kind) B RD hG layer hLayer BE BX (Fintype.card (Famb.VineEstS5C.LvlΓ.top B).ι + 1) (Famb.VineEstS5C.LvlΓ.top B),
      XNorm00Restr θ (openTop Bx (layer (RD.coreBranch hG a).toNode : ℝ)) K (Famb.VineEstS5C.P2.termFnRΓ B σ κ0 (Famb.VineEstS5C.LvlΓ.top B) (spatialMul m (modPsi b lam ψ)) s) ≤ β) :
    XNorm00Restr θ Bx K (flatFnRMXΓ (p := p) (kind := kind) B RD hG layer hLayer m lam σ κ0 hprime s) ≤
      (cutoffMultiplierConstant θ (cutQ q) + 1) *
        ((Multiset.card (Famb.VineEstS5C.P4.Bot.LvlΓ.termsBΓ (p := p) (kind := kind) B RD hG layer hLayer BE BX (Fintype.card (Famb.VineEstS5C.LvlΓ.top B).ι + 1) (Famb.VineEstS5C.LvlΓ.top B)) : ℝ≥0∞) * β) := by
  classical
  set q₀ : ℝ := (layer (RD.coreBranch hG a).toNode : ℝ) with hq₀
  refine (XNorm00Restr_le_openTop θ Bx q₀ K _).trans ?_
  have hsub := openTop_subset Bx q₀
  set T := Famb.VineEstS5C.P4.Bot.LvlΓ.termsBΓ (p := p) (kind := kind) B RD hG layer hLayer BE BX (Fintype.card (Famb.VineEstS5C.LvlΓ.top B).ι + 1) (Famb.VineEstS5C.LvlΓ.top B) with hT
  have hmem : ∀ j : Fin T.toList.length, T.toList[j] ∈ T := fun j => Multiset.mem_toList.mp (List.getElem_mem j.2)
  have hExt : ∀ tt ∈ openTop Bx q₀, (layOf ((Famb.VineEstS5C.LvlΓ.top B).state B RD hG layer hLayer) (Famb.VineEstS5C.LvlΓ.top B).c.a : ℝ) < tt 0 ∧
      tt 0 < layOf ((Famb.VineEstS5C.LvlΓ.top B).state B RD hG layer hLayer) (Famb.VineEstS5C.LvlΓ.top B).c.a + 1 := by
    intro tt htt
    rw [Famb.VineEstS5C.P4.layOf_topΓ]
    exact strict_of_openTop hq tt htt
  have h1 := XNorm00Restr_finsum_le hθ q (hsub.trans hBx) hK
    (fun j : Fin T.toList.length => Famb.VineEstS5C.P2.termFnRΓ B σ κ0 (Famb.VineEstS5C.LvlΓ.top B) (spatialMul m (modPsi b lam T.toList[j])) s)
    (flatFnRMXΓ (p := p) (kind := kind) B RD hG layer hLayer m lam σ κ0 hprime s) (fun tt htt E hE => by
      unfold flatFnRMXΓ Famb.VineEstS5C.P2.termFnRΓ Famb.VineEstS5C.P3.termFnΓ
      have hlk := lkRaw_finsum (Famb.VineEstS5C.LvlΓ.top B).region κ0.L κ0.base
        (spatialMul m (modPsi b lam (Famb.VineEstS5C.LvlΓ.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (Fintype.card (Famb.VineEstS5C.LvlΓ.top B).ι + 1) (Famb.VineEstS5C.LvlΓ.top B))))
        (fun j : Fin T.toList.length => spatialMul m (modPsi b lam T.toList[j])) tt (sumintBoundary s E)
        (fun κ => Filter.Eventually.of_forall fun τ => by
          have := Famb.VineEstS5C.P4.Bot.LvlΓ.psiFuel_eq_termsB_extΓ (p := p) (kind := kind) B RD hG layer hLayer BE BX hW hWB
            (Fintype.card (Famb.VineEstS5C.LvlΓ.top B).ι + 1) (Famb.VineEstS5C.LvlΓ.top B) (clExtendIndices (Famb.VineEstS5C.LvlΓ.top B).region κ.1) tt
            (clLocalClock (Famb.VineEstS5C.LvlΓ.top B).region tt τ)
            ((Famb.VineEstS5C.P4.extOf_clock_iffΓ B RD hG layer hLayer (Famb.VineEstS5C.LvlΓ.top B) tt τ).2 (hExt tt htt))
          unfold spatialMul modPsi
          rw [this, multiset_sum_eq_fin, Finset.mul_sum, Finset.mul_sum])
        (fun j => habs _ (hmem j) tt htt E hE)
      rw [hlk, Finset.mul_sum, Finset.mul_sum])
  refine h1.trans (mul_le_mul' le_rfl ?_)
  calc ∑ j : Fin T.toList.length, XNorm00Restr θ (openTop Bx q₀) K (Famb.VineEstS5C.P2.termFnRΓ B σ κ0 (Famb.VineEstS5C.LvlΓ.top B) (spatialMul m (modPsi b lam T.toList[j])) s)
      ≤ ∑ _j : Fin T.toList.length, β := Finset.sum_le_sum fun j _ => TermBoundR _ (hmem j)
    _ = (Multiset.card T : ℝ≥0∞) * β := by
        simp [Finset.sum_const, nsmul_eq_mul, Multiset.length_toList]

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
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
variable {κ0 : KPar d} {hprime : IsPrimeGarden G}
variable (BE : Famb.VineEstS5C.P3.BundleExpFamΓ (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime) (BX : Famb.VineEstS5C.P4.Bot.BotExpFamΓ (p := p) (kind := kind) B RD hG layer hLayer κ0)
variable {P : WTParams} {κ0' : KPar P.d} {Bh : ℕ → ℝ} {hprime' : IsPrimeGarden G}

/-- The weighted flat bound after the finite term count; `Λ` includes mass and temporal loss. -/
theorem wpF_flatBMXΓ (hM9 : Famb.NormalChartSupply γF) (hR : RealityAll) (E : GateEnv P κ0' p Bh) (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4)
    (m : (GNode G.tree → Fin P.d → ℤ) → ℂ) (lam : ℝ) (σ : ℤˣ) (s : ℤˣ) {η : ℝ} (q : Fin 3 → ℝ) {Bx : Set (Fin 3 → ℝ)} (hBx : Bx ⊆ cell q)
    {K : Set (Fin 4 → Mom P.d)} (hK : K.Countable)
    (hq : ∀ tt ∈ Bx, (layer (RD.coreBranch hG a).toNode : ℝ) ≤ tt 0 ∧ tt 0 ≤ layer (RD.coreBranch hG a).toNode + 1)
    (habs : ∀ ψ ∈ Famb.VineEstS5C.P4.Bot.LvlΓ.termsBΓ (p := p) (kind := kind) B RD hG layer hLayer
        (Famb.VineEstS5C.P4.bundleFamOfΓ B RD hG layer hLayer hR (Famb.VineEstS5C.P4.W13.sffOfΓ (hprime := hprime') B RD hG layer hLayer E hord))
        (Famb.VineEstS5C.P4.Bot.bundleBotFamOfΓ B RD hG layer hLayer hprime' hR (Famb.VineEstS5C.P4.Final.botSffOfΓ B RD hG layer hLayer hprime' E hord))
        (Fintype.card (Famb.VineEstS5C.LvlΓ.top B).ι + 1) (Famb.VineEstS5C.LvlΓ.top B), ∀ tt ∈ openTop Bx (layer (RD.coreBranch hG a).toNode : ℝ), ∀ E' ∈ K,
      LkAbs (Famb.VineEstS5C.LvlΓ.top B).region κ0'.L κ0'.base (spatialMul m (modPsi b lam ψ)) tt (sumintBoundary s E'))
    {Λ Ns δ Lp lf C₁ C₂ : ℝ} {D : ℕ} (hpD : p ≤ D)
    (hTB : ∀ ψ ∈ Famb.VineEstS5C.P4.Bot.LvlΓ.termsBΓ (p := p) (kind := kind) B RD hG layer hLayer
        (Famb.VineEstS5C.P4.bundleFamOfΓ B RD hG layer hLayer hR (Famb.VineEstS5C.P4.W13.sffOfΓ (hprime := hprime') B RD hG layer hLayer E hord))
        (Famb.VineEstS5C.P4.Bot.bundleBotFamOfΓ B RD hG layer hLayer hprime' hR (Famb.VineEstS5C.P4.Final.botSffOfΓ B RD hG layer hLayer hprime' E hord))
        (Fintype.card (Famb.VineEstS5C.LvlΓ.top B).ι + 1) (Famb.VineEstS5C.LvlΓ.top B),
      XNorm00Restr (2 * η ^ 8) (openTop Bx (layer (RD.coreBranch hG a).toNode : ℝ)) K (Famb.VineEstS5C.P2.termFnRΓ B σ κ0' (Famb.VineEstS5C.LvlΓ.top B) (spatialMul m (modPsi b lam ψ)) s) ≤
        ENNReal.ofReal (Λ * ((Ns * Real.sqrt δ) ^ clLocalOrder2 RD hG R * Lp * lf)))
    (hΛ : 0 ≤ Λ) (hNs : 0 ≤ Ns) (hLp : 0 ≤ Lp) (hlf : 0 ≤ lf)
    (hC₁ : (Eng.ccη η + 1).toReal * countKc * Ns ≤ C₁) (hC₂ : (countKp D : ℝ) ≤ C₂) :
    XNorm00Restr (2 * η ^ 8) Bx K (flatFnRMXΓ (p := p) (kind := kind) B RD hG layer hLayer m lam σ κ0' hprime' s) ≤
      ENNReal.ofReal (Λ * ((C₁ * Real.sqrt δ) ^ clLocalOrder2 RD hG R * Lp * lf *
        C₂ ^ (Finset.univ.filter fun i => (Famb.VineEstS2.assemblyShapeΓ hM9 B).nor i = false).card)) := by
  have hX := top_boundRBMXΓ (p := p) (kind := kind) B RD hG layer hLayer
    (Famb.VineEstS5C.P4.bundleFamOfΓ B RD hG layer hLayer hR (Famb.VineEstS5C.P4.W13.sffOfΓ (hprime := hprime') B RD hG layer hLayer E hord))
    (Famb.VineEstS5C.P4.Bot.bundleBotFamOfΓ B RD hG layer hLayer hprime' hR (Famb.VineEstS5C.P4.Final.botSffOfΓ B RD hG layer hLayer hprime' E hord))
    m (Famb.VineEstS5C.P4.winOfExt_bundleFamOfΓ B RD hG layer hLayer hR _) (Famb.VineEstS5C.P4.Bot.winOfExtBot_bundleBotFamOfΓ B RD hG layer hLayer hprime' hR _)
    lam σ s (θ := 2 * η ^ 8) (by positivity) q hBx hK hq habs _ hTB
  exact Famb.VineEstS5C.P4.W13.wpF_topΓ B RD hG layer hLayer hM9 q hpD (Famb.VineEstS5C.LvlΓ.top B)
    (Famb.VineEstS5C.P4.Final.card_termsB_le_wtΓ B RD hG layer hLayer hprime' hR E hord _ (Famb.VineEstS5C.LvlΓ.top B) (Nat.le_succ _))
    hX le_rfl hΛ hNs hLp hlf hC₁ hC₂

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open TTree Twist LFTwist RegRed Reg.Skeleton MeasureTheory VineEstS2 VineEstS3 VineEstS4 VineEstS5C VineEstS5C.Cont VineEstS5C.P4.Final VineEstS5C.P4
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {kind : Bool}
variable {w d p : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
  {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
variable (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open TTree Twist LFTwist RegRed Reg.Skeleton MeasureTheory VineEstS2 VineEstS3 VineEstS4 VineEstS5C VineEstS5C.Cont VineEstS5C.P4.Final VineEstS5C.P4
variable {γF : ℝ}
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
variable {kind : Bool}
variable {w d p : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
  {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
variable (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
open WaveTurbulence.Flower.V5W
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open WaveTurbulence.VineSpaceK WaveTurbulence.VineSpaceB WaveTurbulence.VineC WaveTurbulence.Represents
open WaveTurbulence.Flower.Stage1W
open scoped ENNReal FourierTransform
open Set
open VineEstS5C.P4.Final LGSpine Cut2A
variable {γF : ℝ}

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
open WaveTurbulence.Flower.V5W
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open WaveTurbulence.VineSpaceK WaveTurbulence.VineSpaceB WaveTurbulence.VineC WaveTurbulence.Represents
open WaveTurbulence.Flower.Stage1W
open scoped ENNReal FourierTransform
open Set
open VineEstS5C.P4.Final LGSpine Cut2A
variable {γF : ℝ}

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
open WaveTurbulence.Flower.V5W
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open WaveTurbulence.VineSpaceK WaveTurbulence.VineSpaceB WaveTurbulence.VineC WaveTurbulence.Represents
open WaveTurbulence.Flower.Stage1W
open scoped ENNReal FourierTransform
open Set
open VineEstS5C.P4.Final LGSpine Cut2A
variable {γF : ℝ}

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
open WaveTurbulence.Flower.V5W
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open WaveTurbulence.VineSpaceK WaveTurbulence.VineSpaceB WaveTurbulence.VineC WaveTurbulence.Represents
open WaveTurbulence.Flower.Stage1W
open scoped ENNReal FourierTransform
open Set
open VineEstS5C.P4.Final LGSpine Cut2A
variable {γF : ℝ}

end

end WaveTurbulence.GammaLow.Flower
