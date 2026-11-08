/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.V5WB.Common
public import WaveTurbulence.Foundations.Flower.V5WB.B.Member

public import WaveTurbulence.Foundations.Flower.V5WB.B.LowerBundle
public import WaveTurbulence.Foundations.Flower.V5WB.B.SState
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp19Canon
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp15SokOp
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelRec

/-! # V5-SPACE-EXT: one level of TARGET Step 4 with the bond weight, nested form

`memberB_eq_sSumBAt`: a weighted member is its weighted S-side with the weighted lower kernel (the bond weight of
the union block splits, `bondW_union`). `tildeJ2_B_canon`: the weighted class sum is the sum over the `p*`-states
of the weighted S-sides with the weighted common lower factor. `zp_stateBW`: each state's S-side in the chart of
the level state, with the level state's upper bond weight. `classSumB_nested`: the weighted class sum of a level is
the S-side with the upper bond weight, the bundle `psiSB` and the lower factor the WEIGHTED class sum of the next
level. Adapted from `VineSpaceK.WeightedCanon/ZP/Bundle/LevelNest`. -/

/-! Copied by source (V5W-B-WORLD) from V5W-A's port `Flower/V5WA/VineSpaceB/Nest.lean` (see `COPIED-SHA256SUMS`): namespace `WaveTurbulence.Flower.V5WB`, every row selector (`variable [RowSel]`), the bond weight `bW` replaced by the masked, normalized `bWN` (`ψ : WD d`, bound `bWNB`). -/

@[expose] public section
namespace WaveTurbulence.Flower.V5WB
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS2
  WaveTurbulence.VineEstS3 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS5C.FlatMod
  TTree MeasureTheory

variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {pstar : ι} {J : Set ι}

theorem memberB_eq_sSumBAt (κ : KPar d) (lam : ℝ) (ψ : WD d) (C : ℝ) (hC : 0 ≤ C)
    (hψ : ∀ q q' k, ‖ψ.ψ q q' k‖ ≤ C) (X : FamilyReconstruction w ι) (sp : SplitAt X.skeleton X.family pstar J)
    (hL : κ.L ≠ 0) (hF : HF X.data X.plain κ.L κ.F (stateLayer X) κ.base) :
    memberB κ lam ψ X sp.c = sSumBAt κ ψ X sp (kTB κ lam ψ X sp) := by
  have hex : sp.RT.excluded = sp.RS.kept := split_excluded_b sp.sb.block sp.hT sp.hi sp.hU sp.RS sp.RT
  have hμ : ∀ p : Σ xS : ExtS sp.RS κ.L κ.base κ.e κ.f,
      CLLocalDecoration sp.RT κ.L κ.base (bdT sp.RT κ.L κ.base xS.1 κ.g κ.h),
      bWN ψ κ X (sp.sb.U ∪ sp.tb.U) (glue sp.RS p.1.1 (clExtendIndices sp.RT p.2.1)) =
        bWN ψ κ X sp.sb.U p.1.1 * bWN ψ κ X sp.tb.U (clExtendIndices sp.RT p.2.1) := by
    intro p
    unfold bWN
    rw [bondWD_union (ΨX ψ X) κ.L κ.base (layX X) sp.sb.block sp.hT sp.hi sp.hU, bondWD_glue_S (ΨX ψ X) κ.L κ.base (layX X) sp.RS,
      bondWD_glue_T (ΨX ψ X) κ.L κ.base (layX X) sp.sb.block sp.hT sp.hi sp.hU sp.RS sp.RT hL p.2.2.2.2]
  have h1 := memberMX_split_KT_bond sp.sb.block sp.hT sp.hi sp.hU sp.RU sp.RS sp.RT X.data X.plain κ.L κ.γ κ.δ κ.F
    (stateLayer X) (stateLayer_isLayering X) κ.base lam κ.t0 κ.t1 κ.t2 κ.e κ.f κ.g κ.h
    (bWN ψ κ X (sp.sb.U ∪ sp.tb.U)) (bWN ψ κ X sp.sb.U) (bWN ψ κ X sp.tb.U) hL hF hμ
    (bWNB ψ X sp.sb.U C) (bWNB ψ X sp.tb.U C)
    (bWNB_nonneg _ _ _ hC) (bWNB_nonneg _ _ _ hC) (fun x => norm_bWN_le ψ κ X sp.sb.U C hψ x)
    (fun x => norm_bWN_le ψ κ X sp.tb.U C hψ x)
  unfold memberB
  rw [memberMX_idx sp.union sp.sa.symm sp.tbb.symm (clRegionData X.skeleton sp.c.block sp.c.cl) sp.RU, sp.union]
  rw [h1]
  unfold sSumBAt sSumW kTB
  have hb0 : clBoundaryNodes sp.RT 0 = sp.sb.b.toNode := rfl
  have hb1 : clBoundaryNodes sp.RT 1 = sp.sb.b.child sp.RS.kept := by
    change sp.sb.b.child sp.RT.excluded = _
    rw [hex]
  rw [hb0, hb1]

variable [Fintype ι] [DecidableEq ι]

/-- **(tildeJ2) for an abstract split, weighted.** -/
theorem tildeJ2_B_of_split (κ : KPar d) (lam : ℝ) (ψ : WD d) (C : ℝ) (hC : 0 ≤ C)
    (hψ : ∀ q q' k, ‖ψ.ψ q q' k‖ ≤ C) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton)
    (hA0 : ∀ j, j ∉ J → j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j))
    (hL : κ.L ≠ 0) (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|) :
    ∑ x ∈ canonSpFinset p kind pstar J A sp0 hA, memberB κ lam ψ x.1 x.2.c =
      ∑ G ∈ zpFinset p kind pstar J A sp0 hA,
        sSumBAt κ ψ G.1 G.2 (ktildeB (p := p) (kind := kind) κ lam ψ A sp0 hA G) := by
  classical
  have hc : Stage1.OpsCommute p kind w ι := Stage1.opsCommute_all
  rw [sum_canon hc hA]
  refine Finset.sum_congr rfl fun G hG => ?_
  have hr := (mem_zpFinset hA).mp hG
  have ha : ∀ x ∈ yFinset p kind pstar J A sp0 hA G,
      memberB κ lam ψ x.1 x.2.c = sSumBAt κ ψ G.1 G.2 (kTB κ lam ψ x.1 x.2) := by
    intro x hx
    obtain ⟨M, hM, hxr⟩ := (mem_yFinset hA hr).mp hx
    rw [memberB_eq_sSumBAt κ lam ψ C hC hψ x.1 x.2 hL (HF_of_all _ _ _ _ _ _ hF)]
    exact sSumBAt_reachBelow hc κ ψ hA0 hxr hr.batch (Lpre := [pstar]) (nodup_pre hM) (List.mem_singleton_self pstar) _
  rw [Finset.sum_congr rfl ha]
  have hsok : ∀ x ∈ yFinset p kind pstar J A sp0 hA G, SOKAt κ G.1 G.2 (kTB κ lam ψ x.1 x.2) := by
    intro x hx
    obtain ⟨M, hM, hxr⟩ := (mem_yFinset hA hr).mp hx
    exact (SOKAt_reachBelow hc κ hA0 hxr hr.batch (Lpre := [pstar]) (nodup_pre hM) (List.mem_singleton_self pstar) _).mp
      (SOKAt_kTB κ lam ψ x.1 x.2 hL (HF_of_all _ _ _ _ _ _ hF) C hC hψ)
  have hlin := sSumW_finsetSum (bWN ψ κ G.1 G.2.sb.U) G.2.RS G.1.data G.1.plain κ.L κ.γ κ.δ κ.F (stateLayer G.1)
    (stateLayer_isLayering G.1) κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f G.2.sb.b.toNode (G.2.sb.b.child G.2.RS.kept)
    (yFinset p kind pstar J A sp0 hA G) (fun x => kTB κ lam ψ x.1 x.2) hsok
    (bWNB ψ G.1 G.2.sb.U C) (bWNB_nonneg _ _ _ hC) (fun x => norm_bWN_le ψ κ G.1 G.2.sb.U C hψ x)
  unfold sSumBAt at hlin ⊢
  rw [← hlin]
  congr 1
  funext t E F'
  unfold ktildeB
  refine sum_yG_eq_yA hc hA hG (fun x => kTB κ lam ψ x.1 x.2 t E F') (fun y => kTorB κ lam ψ A G.1 pstar y t E F') ?_
  intro x hx y hy hxy
  obtain ⟨M, hM, hxr⟩ := (mem_yFinset hA hr).mp hx
  obtain ⟨My, hMy, hyr⟩ := (mem_yA hA).mp hy
  exact kTB_rel κ lam ψ hA hr hM hMy hxr hyr hxy t E F'

/-- **(tildeJ2) over the canonical representatives, weighted.** -/
theorem tildeJ2_B_canon (κ : KPar d) (lam : ℝ) (ψ : WD d) (C : ℝ) (hC : 0 ≤ C)
    (hψ : ∀ q q' k, ‖ψ.ψ q q' k‖ ≤ C) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton)
    (hA0 : ∀ j, j ∉ J → j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j))
    (hL : κ.L ≠ 0) (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|) :
    ∑ y ∈ canonFinsetK p kind A sp0.c, memberB κ lam ψ y.1 y.2 =
      ∑ G ∈ zpFinset p kind pstar J A sp0 hA,
        sSumBAt κ ψ G.1 G.2 (ktildeB (p := p) (kind := kind) κ lam ψ A sp0 hA G) := by
  rw [← sum_canonSp_eq_canon A sp0 hA (fun y => memberB κ lam ψ y.1 y.2)]
  exact tildeJ2_B_of_split κ lam ψ C hC hψ A sp0 hA hA0 hL hF

/-- Each `p*`-state's weighted S-side, in the chart of `A` with `A`'s upper bond weight. -/
theorem zp_stateBW (κ : KPar d) (lam : ℝ) (ψ : WD d) (A : FamilyReconstruction w ι)
    (sp0 : SplitAt A.skeleton A.family pstar J) (hA : IsPrimeGarden A.skeleton)
    {G : ST w ι pstar J} (hG : G ∈ zpFinset p kind pstar J A sp0 hA) :
    sSumBAt κ ψ G.1 G.2 (ktildeB (p := p) (kind := kind) κ lam ψ A sp0 hA G) =
      (coupling d κ.L κ.γ κ.δ : ℂ) ^ clLocalOrder1 sp0.RS * clLocalZeta sp0.RS *
        (∑' x : ExtS sp0.RS κ.L κ.base κ.e κ.f, ∫ σ : CLInternalTime sp0.RS,
          bWN ψ κ A sp0.sb.U x.1 * stIntB (p := p) (kind := kind) κ lam ψ A sp0 hA G.1 x σ) := by
  classical
  have hr := (mem_zpFinset hA).mp hG
  obtain ⟨G1, G2⟩ := G
  simp only at hr ⊢
  cases hr with
  | skip _ h =>
    cases h
    have hn : ¬ twAt A A pstar := not_twAt_of_eq rfl
    have e : stIntB (p := p) (kind := kind) κ lam ψ A sp0 hA A =
        bundleInt κ A sp0 (KtilB (p := p) (kind := kind) κ lam ψ A sp0 hA) false (nuOf A pstar)
          (rowQ κ A pstar) (rowT κ A pstar) := by
      funext x σ; simp [stIntB, epsOf, hn]
    rw [e]
    exact sSumBAt_skip κ ψ A sp0 _
  | apply op h =>
    cases h
    obtain ⟨hcan, hel, htc, hcc, ε, con⟩ := op
    cases ε
    · have hn := tw_false A hcan hel htc hcc con
      have hk : ktildeB (p := p) (kind := kind) κ lam ψ A sp0 hA
          ⟨opOut A pstar hcan hel htc hcc con, SplitAt.nextA A sp0 pstar false⟩ =
            KtilB (p := p) (kind := kind) κ lam ψ A sp0 hA := by
        rw [ktildeB_eq]; funext t E F'; simp [hn]
      have e : stIntB (p := p) (kind := kind) κ lam ψ A sp0 hA (opOut A pstar hcan hel htc hcc con) =
          bundleInt κ A sp0 (KtilB (p := p) (kind := kind) κ lam ψ A sp0 hA) false
            (nuOf (opOut A pstar hcan hel htc hcc con) pstar)
            (rowQ κ (opOut A pstar hcan hel htc hcc con) pstar) (rowT κ (opOut A pstar hcan hel htc hcc con) pstar) := by
        funext x σ; simp [stIntB, epsOf, hn]
      rw [hk, e]
      exact sSumBAt_false κ ψ A sp0 hcan hel htc hcc con _
    · have ht := tw_true A hcan hel htc hcc con
      have hk : ktildeB (p := p) (kind := kind) κ lam ψ A sp0 hA
          ⟨opOut A pstar hcan hel htc hcc con, SplitAt.nextA A sp0 pstar true⟩ =
          fun t E F' => KtilB (p := p) (kind := kind) κ lam ψ A sp0 hA t F' E := by
        rw [ktildeB_eq]; funext t E F'; simp [ht]
      have e : stIntB (p := p) (kind := kind) κ lam ψ A sp0 hA (opOut A pstar hcan hel htc hcc con) = fun x σ =>
          -bundleInt κ A sp0 (fun t E Fr => (fun t E F' => KtilB (p := p) (kind := kind) κ lam ψ A sp0 hA t F' E) t Fr E)
            true (nuOf (opOut A pstar hcan hel htc hcc con) pstar)
            (rowQ κ (opOut A pstar hcan hel htc hcc con) pstar) (rowT κ (opOut A pstar hcan hel htc hcc con) pstar) x σ := by
        funext x σ; simp [stIntB, epsOf, ht]
      rw [hk, e]
      rw [sSumBAt_true κ ψ A sp0 hcan hel htc hcc con]
      simp only [mul_neg, integral_neg, tsum_neg]

/-- The class in the common S chart equals the weighted bundle kernel with the weighted lower factor. -/
theorem weighted_bundle_sumB (κ : KPar d) (lam : ℝ) (ψ : WD d) (C : ℝ) (hC : 0 ≤ C)
    (hψ : ∀ q q' k, ‖ψ.ψ q q' k‖ ≤ C) (A : FamilyReconstruction w ι)
    (sp : SplitAt A.skeleton A.family pstar J) (hA : IsPrimeGarden A.skeleton)
    (hA0 : ∀ j, j ∉ J → j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j))
    (hL : κ.L ≠ 0) (hF : ∀ r : ℕ, Summable fun n : Fin d → ℤ => |κ.F r (κ.base + latticePoint κ.L n)|)
    (m : (GNode A.skeleton.tree → Fin d → ℤ) → ℂ) (M : ℝ) (hM : 0 ≤ M) (hm : ∀ x, ‖m x‖ ≤ M) :
    (∑ Z ∈ zpFinset p kind pstar J A sp hA,
      ∑' x : ExtS sp.RS κ.L κ.base κ.e κ.f,
        ∫ σ : CLInternalTime sp.RS, m x.val * stIntB (p := p) (kind := kind) κ lam ψ A sp hA Z.1 x σ) =
    ∑' x : ExtS sp.RS κ.L κ.base κ.e κ.f, ∫ σ : CLInternalTime sp.RS,
      m x.val * (psiSB (p := p) (kind := kind) κ A sp hA x.val (clLocalClock sp.RS ![κ.t0, κ.t1, κ.t2] σ) *
        KtilB (p := p) (kind := kind) κ lam ψ A sp hA (clLocalClock sp.RS ![κ.t0, κ.t1, κ.t2] σ sp.sb.b)
          (κ.base + latticePoint κ.L (x.val (A.family.placement pstar).lower.toNode))
          (κ.base + latticePoint κ.L (x.val (A.family.placement pstar).retained.toNode))) := by
  classical
  have hz := fun Z (hZ : Z ∈ zpFinset p kind pstar J A sp hA) => zp_stateB_bok κ lam ψ C hC hψ A sp hA hA0 hL hF hZ
  rw [← Summable.tsum_finsetSum (fun Z hZ =>
    summable_weighted_integrals volume _ (hz Z hZ).2 (fun x => m x.val) M hM (fun x => hm x.val))]
  apply tsum_congr
  intro x
  rw [← integral_finsetSum _ (fun Z hZ => ((hz Z hZ).1 x).const_mul (m x.val))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
  beta_reduce
  rw [← Finset.mul_sum]
  exact congrArg (m x.val * ·) (sum_stIntB_eq κ lam ψ A sp hA x σ)

section Level
variable {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- **The bond-weighted modulated class sum of a level.** -/
noncomputable def classSumB (lam : ℝ) (ψ : WD d) (lv : Lvl B) (κ0 : KPar d) (t0 t1 t2 : ℝ)
    (e f g h : Mom d) : ℂ :=
  ∑ z ∈ canonFinsetK p kind (lv.state B RD hG layer hLayer) lv.c,
    memberB {κ0 with t0 := t0, t1 := t1, t2 := t2, e := e, f := f, g := g, h := h} lam ψ z.1 z.2

/-- **One level of TARGET Step 4, nested form, with the bond weight.** -/
theorem classSumB_nested (lam : ℝ) (ψ : WD d) (C : ℝ) (hC : 0 ≤ C)
    (hψ : ∀ q q' k, ‖ψ.ψ q q' k‖ ≤ C) (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|)
    (hprime : IsPrimeGarden G) (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val)
    (hA0 : ∀ j, j ∉ {j | (lv.e j).1.val < (lv.e pstar).1.val} → j ≠ pstar →
      IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j))
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    classSumB (p := p) (kind := kind) B RD hG layer hLayer lam ψ lv κ0 t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 (lv.split B RD hG layer hLayer pstar hk).RS *
        clLocalZeta (lv.split B RD hG layer hLayer pstar hk).RS *
        ∑' x : ExtS (lv.split B RD hG layer hLayer pstar hk).RS κ0.L κ0.base e f,
          ∫ σ : CLInternalTime (lv.split B RD hG layer hLayer pstar hk).RS,
            bWN ψ κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk).sb.U x.1 *
            (psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk)
              hprime x.1 (clLocalClock (lv.split B RD hG layer hLayer pstar hk).RS ![t0, t1, t2] σ) *
            classSumB (p := p) (kind := kind) B RD hG layer hLayer lam ψ (lv.next B RD hG layer hLayer pstar hk) κ0
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
  have e1 : classSumB (p := p) (kind := kind) B RD hG layer hLayer lam ψ lv κ0 t0 t1 t2 e f g h =
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

end Level

end WaveTurbulence.Flower.V5WB
