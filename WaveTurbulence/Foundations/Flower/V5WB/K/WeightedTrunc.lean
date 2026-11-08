/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.V5WB.Common

public import WaveTurbulence.Foundations.Flower.V5WB.K.Kernel
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Final.Trunc
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.WinChain
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.Cont.Member
public import WaveTurbulence.Foundations.Spine.PL234Draft.SameLayerApprox

/-! Native weighted kernels read profiles only at the source layers.
The multiplier is unaffected by profile truncation. -/

/-! Copied by source (V5W-B-WORLD) from V5W-A's port `Flower/V5WA/VineSpaceK/WeightedTrunc.lean` (see `COPIED-SHA256SUMS`): namespace `WaveTurbulence.Flower.V5WB`, every row selector (`variable [RowSel]`), the bond weight `bW` replaced by the masked, normalized `bWN` (`ψ : WD d`, bound `bWNB`). -/

@[expose] public section
namespace WaveTurbulence.Flower.V5WB
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract WaveTurbulence.LGSpine
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2
  WaveTurbulence.VineEstS5C.P4 WaveTurbulence.PL234 WaveTurbulence.VineEstS5C.FlatMod VineEstS5C.P4.Final

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {d : ℕ}

theorem memberMX_congr_F (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b) (L γ δ : ℝ)
    (F F' : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
    (lam : ℝ) (m : (GNode G.tree → Fin d → ℤ) → ℂ) (t0 t1 t2 : ℝ) (e f g h : Mom d) {p : ℕ} (hlay : ∀ x, layer x ≤ p) (hFF : ∀ r ≤ p, F r = F' r) :
    memberMX D hG R L γ δ F layer hLayer base lam m t0 t1 t2 e f g h =
      memberMX D hG R L γ δ F' layer hLayer base lam m t0 t1 t2 e f g h := by
  unfold memberMX
  -- main 416902c8: `congr 1` times out on the selected rows (generic `RowSel` instance); name the factor instead
  refine congrArg (HMul.hMul _) (tsum_congr fun κ => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  simp only
  rw [clLocalSummand_congr_F D hG R L γ δ F F' layer hLayer base _ _ κ τ hlay hFF]

/-- **F-trunc for the modulated class integrand**: it depends on `F` only at layers `≤ p`. -/
theorem twistedRecenteredModCX_congr_F {ι : Type*} [Fintype ι] {p : ℕ} (A : FamilyReconstruction w ι) (hA : IsPrimeGarden A.skeleton)
    (c : ChainAt A.skeleton A.family) (hAl : ∀ x, stateLayer A x ≤ p) (a : GBranch A.skeleton.tree)
    (L γ δ : ℝ) (F F' : ℕ → Mom d → ℝ) (base : Mom d) (lam : ℝ)
    (m : (z : ClassMember w ι) → (GNode z.1.skeleton.tree → Fin d → ℤ) → ℂ) (t0 t1 t2 : ℝ) (e f g h : Mom d)
    (hFF : ∀ r ≤ p, F r = F' r) :
    twistedRecenteredModCX A.skeleton a (canonFinsetK p kind A c) m L γ δ F base lam t0 t1 t2 e f g h =
      twistedRecenteredModCX A.skeleton a (canonFinsetK p kind A c) m L γ δ F' base lam t0 t1 t2 e f g h := by
  unfold twistedRecenteredModCX
  refine congrArg (HMul.hMul _) (Finset.sum_congr rfl fun x hx => ?_)
  obtain ⟨M, _, hr⟩ := (mem_canonFinset hA).1 hx
  exact memberMX_congr_F _ _ _ L γ δ F F' _ _ base lam (m x) t0 t1 t2 e f g h
    (Cont.reach_stateLayer_le hr hAl) hFF

end WaveTurbulence.Flower.V5WB
