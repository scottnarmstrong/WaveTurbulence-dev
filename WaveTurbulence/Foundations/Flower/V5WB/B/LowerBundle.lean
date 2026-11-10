/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.V5WB.B.Member

public import WaveTurbulence.Foundations.Flower.V5WB.B.LowerKernel
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.Bundle
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.LevelNest

/-! # V5-SPACE-EXT: the weighted common lower factor and the weighted fibre combinatorics

`kTorB`, `ktildeB`, `KtilB` (the lower factor of `p*`: the weighted lower class), `kTB_rel` (the fibre kernel is the
exchanged kernel), the summability `SOKAt_kTB`/`sok_ktildeB`, the common-chart integrand `stIntB` with its
integrability `zp_stateB_bok`, the bundle identity `sum_stIntB_eq`, and `KtilB_eq_canon`: the weighted lower factor
is the weighted class sum of the restricted problem. Verbatim adaptations of `FlatMod.Canon/Bundle/LevelNest`
with `kTM` replaced by the weighted `kTB`. -/

/-! Copied by source (V5W-B-WORLD) from V5W-A's port `Flower/V5WA/VineSpaceB/LowerBundle.lean` (see `COPIED-SHA256SUMS`): namespace `WaveTurbulence.Flower.V5WB`, every row selector (`variable [RowSel]`), the bond weight `bW` replaced by the masked, normalized `bWN` (`ψ : WD d`, bound `bWNB`). -/

@[expose] public section
namespace WaveTurbulence.Flower.V5WB
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS2
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS5C.FlatMod TTree MeasureTheory

variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι}

section State
variable (κ : KPar d) (lam : ℝ) (ψ : WD d) (X : FamilyReconstruction w ι)
  (sp : SplitAt X.skeleton X.family pstar J)

theorem SOKAt_kTB (hL : κ.L ≠ 0) (hF : HF X.data X.plain κ.L κ.F (stateLayer X) κ.base)
    (C : ℝ) (hC : 0 ≤ C) (hψ : ∀ q q' k, ‖ψ.ψ q q' k‖ ≤ C) :
    SOKAt κ X sp (kTB κ lam ψ X sp) := by
  have hex : sp.RT.excluded = sp.RS.kept := split_excluded_b sp.sb.block sp.hT sp.hi sp.hU sp.RS sp.RT
  have h := sok_memberMX sp.sb.block sp.hT sp.hi sp.hU sp.RU sp.RS sp.RT X.data X.plain κ.L κ.γ κ.δ κ.F (stateLayer X)
    (stateLayer_isLayering X) κ.base lam κ.t0 κ.t1 κ.t2 κ.e κ.f κ.g κ.h (bWN ψ κ X sp.tb.U) hL hF
    (bWNB ψ X sp.tb.U C) (bWNB_nonneg _ _ _ hC) (fun x => norm_bWN_le ψ κ X sp.tb.U C hψ x)
  have hb0 : clBoundaryNodes sp.RT 0 = sp.sb.b.toNode := rfl
  have hb1 : clBoundaryNodes sp.RT 1 = sp.sb.b.child sp.RS.kept := by
    change sp.sb.b.child sp.RT.excluded = _
    rw [hex]
  unfold SOKAt kTB
  exact (SOK_nodes_congr sp.RS X.data X.plain κ.L κ.γ κ.δ κ.F (stateLayer X) (stateLayer_isLayering X) κ.base κ.t0 κ.t1
    κ.t2 κ.e κ.f hb0 hb1 _).mp h

end State

open Classical in
/-- The weighted lower kernel of `y`, with the first two boundary momenta exchanged iff `G` is a twist at `pstar`. -/
noncomputable def kTorB (κ : KPar d) (lam : ℝ) (ψ : WD d) (A G : FamilyReconstruction w ι) (pstar : ι)
    (y : ST w ι pstar J) : ℝ → Mom d → Mom d → ℂ := fun t E F' =>
  if twAt A G pstar then kTB κ lam ψ y.1 y.2 t F' E else kTB κ lam ψ y.1 y.2 t E F'

/-- The weighted common lower factor `K̃_T` for the twist `G` of `A` at `pstar`. -/
noncomputable def ktildeB [Fintype ι] [DecidableEq ι] (κ : KPar d) (lam : ℝ) (ψ : WD d)
    (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) (G : ST w ι pstar J) : ℝ → Mom d → Mom d → ℂ := fun t E F' =>
  ∑ y ∈ yFinset p kind pstar J A sp0 hA ⟨A, sp0⟩, kTorB κ lam ψ A G.1 pstar y t E F'

variable [Fintype ι] [DecidableEq ι]

section Rel
variable (κ : KPar d) (lam : ℝ) (ψ : WD d) {A : FamilyReconstruction w ι}
  {sp0 : SplitAt A.skeleton A.family pstar J}

/-- **The weighted fibre kernel is the exchanged kernel of `y`.** -/
theorem kTB_rel (hA : IsPrimeGarden A.skeleton) {G : ST w ι pstar J}
    (hG : ReachSp p kind pstar J [pstar] A sp0 G.1 G.2) {x y : ST w ι pstar J}
    {M My : List ι} (hM : M.Perm (Finset.univ.erase pstar).toList) (hMy : My.Perm (Finset.univ.erase pstar).toList)
    (hx : ReachSp p kind pstar J M G.1 G.2 x.1 x.2) (hy : ReachSp p kind pstar J My A sp0 y.1 y.2)
    (hxy : FamilyBatch p kind [pstar] y.1 x.1) (t : ℝ) (E F' : Mom d) :
    kTB κ lam ψ x.1 x.2 t E F' = kTorB κ lam ψ A G.1 pstar y t E F' := by
  classical
  have hsy : sigStar y.1 pstar = sigStar A pstar := sigStar_batch hy.batch (not_mem_erase hMy)
  have hsx : sigStar x.1 pstar = sigStar G.1 pstar := sigStar_batch hx.batch (not_mem_erase hM)
  have hxA : ReachSp p kind pstar J ([pstar] ++ M) A sp0 x.1 x.2 := ReachSp.append hG hx
  obtain ⟨X, sx⟩ := x
  simp only at hxy hsx hxA ⊢
  cases hxy with
  | skip _ h1 =>
    cases h1
    have hy' : ReachSp p kind pstar J (My ++ [pstar]) A sp0 y.1 y.2 := ReachSp.append hy (ReachSp.skips y.2 _)
    have e : sx = y.2 := ReachSp.unique (nodup_pre hM) (by
      refine List.nodup_append.mpr ⟨nodup_erase hMy, List.nodup_singleton _, ?_⟩
      intro a ha b hb hab
      simp at hb
      subst hb
      exact not_mem_erase hMy (hab ▸ ha)) hxA hy'
    subst e
    have hn : ¬ twAt A G.1 pstar := not_twAt_of_eq (hsx.symm.trans hsy)
    unfold kTorB
    rw [if_neg hn]
  | apply op h1 =>
    cases h1
    obtain ⟨hcan, hel, htc, hcc, ε, con⟩ := op
    have hy' : ReachSp p kind pstar J (My ++ [pstar]) A sp0
        (FamilyOperation.output (⟨hcan, hel, htc, hcc, ε, con⟩ : FamilyOperation (p := p) (kind := kind) y.1 pstar))
        (SplitAt.nextA y.1 y.2 pstar ε) := ReachSp.append hy (.apply _ (.nil _ _))
    have e : sx = SplitAt.nextA y.1 y.2 pstar ε := ReachSp.unique (nodup_pre hM) (by
      refine List.nodup_append.mpr ⟨nodup_erase hMy, List.nodup_singleton _, ?_⟩
      intro a ha b hb hab
      simp at hb
      subst hb
      exact not_mem_erase hMy (hab ▸ ha)) hxA hy'
    subst e
    have hs := sigStar_output y.1 pstar hcan hel htc hcc con
    cases ε
    · have h0 : (sigStar y.1 pstar).1 = (sigStar A pstar).1 := congrArg Prod.fst hsy
      have h1 : (sigStar (opOut y.1 pstar hcan hel htc hcc con) pstar).1 = (sigStar A pstar).1 := by
        rw [hs]
        exact h0
      have hn : ¬ twAt A G.1 pstar := fun hh => hh (hsx ▸ h1)
      unfold kTorB
      rw [if_neg hn]
      exact kTB_op_false κ lam ψ y.1 y.2 hcan hel htc hcc con t E F'
    · have h0 : (sigStar y.1 pstar).1 = (sigStar A pstar).1 := congrArg Prod.fst hsy
      have h1 : (sigStar (opOut y.1 pstar hcan hel htc hcc con) pstar).1 = -(sigStar A pstar).1 := by
        rw [hs]
        refine (sign_out_true y.1 pstar hcan hel htc hcc con).trans ?_
        exact congrArg (fun z => -z) h0
      have hn : twAt A G.1 pstar := by
        intro hh
        apply units_ne_neg (sigStar A pstar).1
        rw [← h1, hsx, hh]
      unfold kTorB
      rw [if_pos hn]
      exact kTB_op_true κ lam ψ y.1 y.2 hcan hel htc hcc con t E F'

end Rel

/-- The weighted common lower factor at the state `A`. -/
noncomputable def KtilB (κ : KPar d) (lam : ℝ) (ψ : WD d) (A : FamilyReconstruction w ι)
    (sp0 : SplitAt A.skeleton A.family pstar J) (hA : IsPrimeGarden A.skeleton) : ℝ → Mom d → Mom d → ℂ :=
  ktildeB (p := p) (kind := kind) κ lam ψ A sp0 hA ⟨A, sp0⟩

open Classical in
theorem ktildeB_eq (κ : KPar d) (lam : ℝ) (ψ : WD d) (A : FamilyReconstruction w ι)
    (sp0 : SplitAt A.skeleton A.family pstar J) (hA : IsPrimeGarden A.skeleton) (G : ST w ι pstar J) :
    ktildeB (p := p) (kind := kind) κ lam ψ A sp0 hA G = fun t E F' =>
      if twAt A G.1 pstar then KtilB (p := p) (kind := kind) κ lam ψ A sp0 hA t F' E
      else KtilB (p := p) (kind := kind) κ lam ψ A sp0 hA t E F' := by
  classical
  funext t E F'
  have hnA : ¬ twAt A A pstar := not_twAt_of_eq rfl
  simp only [KtilB, ktildeB, kTorB]
  by_cases htw : twAt A G.1 pstar
  · simp only [htw, hnA, if_true, if_false]
  · simp only [htw, hnA, if_false]

theorem ktildeB_sum (κ : KPar d) (lam : ℝ) (ψ : WD d) (A : FamilyReconstruction w ι)
    (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) {G : ST w ι pstar J} (hG : G ∈ zpFinset p kind pstar J A sp0 hA) :
    ktildeB (p := p) (kind := kind) κ lam ψ A sp0 hA G =
      fun t E F' => ∑ x ∈ yFinset p kind pstar J A sp0 hA G, kTB κ lam ψ x.1 x.2 t E F' := by
  classical
  have hc : Stage1.OpsCommute p kind w ι := Stage1.opsCommute_all
  have hr := (mem_zpFinset hA).mp hG
  funext t E F'
  unfold ktildeB
  refine (sum_yG_eq_yA hc hA hG (fun x => kTB κ lam ψ x.1 x.2 t E F')
    (fun y => kTorB κ lam ψ A G.1 pstar y t E F') ?_).symm
  intro x hx y hy hxy
  obtain ⟨M, hM, hxr⟩ := (mem_yFinset hA hr).mp hx
  obtain ⟨My, hMy, hyr⟩ := (mem_yA hA).mp hy
  exact kTB_rel κ lam ψ hA hr hM hMy hxr hyr hxy t E F'

theorem sok_ktildeB (κ : KPar d) (lam : ℝ) (ψ : WD d) (C : ℝ) (hC : 0 ≤ C)
    (hψ : ∀ q q' k, ‖ψ.ψ q q' k‖ ≤ C) (A : FamilyReconstruction w ι)
    (sp0 : SplitAt A.skeleton A.family pstar J) (hA : IsPrimeGarden A.skeleton)
    (hA0 : ∀ j, j ∉ J → j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j))
    (hL : κ.L ≠ 0) (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|)
    {G : ST w ι pstar J} (hG : G ∈ zpFinset p kind pstar J A sp0 hA) :
    SOKAt κ G.1 G.2 (ktildeB (p := p) (kind := kind) κ lam ψ A sp0 hA G) := by
  classical
  have hc : Stage1.OpsCommute p kind w ι := Stage1.opsCommute_all
  have hr := (mem_zpFinset hA).mp hG
  have hsok : ∀ x ∈ yFinset p kind pstar J A sp0 hA G, SOKAt κ G.1 G.2 (kTB κ lam ψ x.1 x.2) := by
    intro x hx
    obtain ⟨M, hM, hxr⟩ := (mem_yFinset hA hr).mp hx
    exact (SOKAt_reachBelow hc κ hA0 hxr hr.batch (Lpre := [pstar]) (nodup_pre hM) (List.mem_singleton_self pstar) _).mp
      (SOKAt_kTB κ lam ψ x.1 x.2 hL (HF_of_all _ _ _ _ _ _ hF) C hC hψ)
  rw [ktildeB_sum κ lam ψ A sp0 hA hG]
  exact sok_sum G.2.RS G.1.data G.1.plain κ.L κ.γ κ.δ κ.F (stateLayer G.1) (stateLayer_isLayering G.1) κ.base κ.t0 κ.t1
    κ.t2 κ.e κ.f G.2.sb.b.toNode (G.2.sb.b.child G.2.RS.kept) (yFinset p kind pstar J A sp0 hA G)
    (fun x t E F' => kTB κ lam ψ x.1 x.2 t E F') hsok

open Classical in
/-- The integrand of the state `G` in the chart of `A`, with the weighted lower factor. -/
noncomputable def stIntB (κ : KPar d) (lam : ℝ) (ψ : WD d) (A : FamilyReconstruction w ι)
    (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) (G : FamilyReconstruction w ι)
    (x : ExtS sp0.RS κ.L κ.base κ.e κ.f) (σ : CLInternalTime sp0.RS) : ℂ :=
  epsOf A pstar G * bundleInt κ A sp0 (KtilB (p := p) (kind := kind) κ lam ψ A sp0 hA) (decide (twAt A G pstar))
    (nuOf G pstar) (rowQ κ G pstar) (rowT κ G pstar) x σ

theorem zp_stateB_bok (κ : KPar d) (lam : ℝ) (ψ : WD d) (C : ℝ) (hC : 0 ≤ C)
    (hψ : ∀ q q' k, ‖ψ.ψ q q' k‖ ≤ C) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton)
    (hA0 : ∀ j, j ∉ J → j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j))
    (hL : κ.L ≠ 0) (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|)
    {G : ST w ι pstar J} (hG : G ∈ zpFinset p kind pstar J A sp0 hA) :
    BOK sp0.RS κ.L κ.base κ.e κ.f (stIntB (p := p) (kind := kind) κ lam ψ A sp0 hA G.1) := by
  classical
  have hok := sok_ktildeB κ lam ψ C hC hψ A sp0 hA hA0 hL hF hG
  have hr := (mem_zpFinset hA).mp hG
  obtain ⟨G1, G2⟩ := G
  simp only at hok hr ⊢
  cases hr with
  | skip _ h =>
    cases h
    have hn : ¬ twAt A A pstar := not_twAt_of_eq rfl
    have e : stIntB (p := p) (kind := kind) κ lam ψ A sp0 hA A =
        bundleInt κ A sp0 (KtilB (p := p) (kind := kind) κ lam ψ A sp0 hA) false (nuOf A pstar)
          (rowQ κ A pstar) (rowT κ A pstar) := by
      funext x σ; simp [stIntB, epsOf, hn]
    rw [e]
    exact bok_skip κ A sp0 _ hok
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
      rw [hk] at hok
      rw [e]
      exact bok_false κ A sp0 hcan hel htc hcc con _ hok
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
      rw [hk] at hok
      rw [e]
      obtain ⟨h1, h2⟩ := bok_true κ A sp0 hcan hel htc hcc con _ hok
      exact ⟨fun x => (h1 x).neg, by simpa [norm_neg] using h2⟩

open Classical in
theorem sum_stIntB_eq (κ : KPar d) (lam : ℝ) (ψ : WD d) (A : FamilyReconstruction w ι)
    (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) (x : ExtS sp0.RS κ.L κ.base κ.e κ.f) (σ : CLInternalTime sp0.RS) :
    ∑ G ∈ zpFinset p kind pstar J A sp0 hA, stIntB (p := p) (kind := kind) κ lam ψ A sp0 hA G.1 x σ =
      psiSB (p := p) (kind := kind) κ A sp0 hA x.1 (clLocalClock sp0.RS ![κ.t0, κ.t1, κ.t2] σ) *
        KtilB (p := p) (kind := kind) κ lam ψ A sp0 hA (clLocalClock sp0.RS ![κ.t0, κ.t1, κ.t2] σ sp0.sb.b)
          (κ.base + latticePoint κ.L (x.1 (A.family.placement pstar).lower.toNode))
          (κ.base + latticePoint κ.L (x.1 (A.family.placement pstar).retained.toNode)) := by
  unfold psiSB
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun G _ => ?_
  simp only [stIntB, bundleInt_eq_kernel]
  ring

section Canon
variable {ι' : Type*} [Fintype ι'] [DecidableEq ι']

open Classical in
/-- **The weighted common lower factor of `pstar` is the weighted class sum of the restricted problem.** -/
theorem KtilB_eq_canon (hc : Stage1.OpsCommute p kind w ι) (e : ι' → ι) (he : Function.Injective e)
    (hJ : ∀ j, e j ∈ J) (hJ' : ∀ i ∈ J, ∃ j, e j = i) (κ : KPar d) (lam : ℝ) (ψ : WD d)
    {A : FamilyReconstruction w ι} (hA : IsPrimeGarden A.skeleton) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA0 : ∀ j, j ∉ J → j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j)) :
    KtilB (p := p) (kind := kind) κ lam ψ A sp0 hA = fun t E F' =>
      ∑ z ∈ canonFinsetK p kind (restrictState A e he) (chainOfSplit A sp0 e he hJ),
        memberMX z.1.data z.1.plain (clRegionData z.1.skeleton z.2.block z.2.cl) κ.L κ.γ κ.δ κ.F
          (stateLayer z.1) (stateLayer_isLayering z.1) κ.base lam (bWN ψ κ z.1 z.2.U) t κ.t1 κ.t2 E F' κ.g κ.h := by
  funext t E F'
  rw [← sum_yA_eq_canon (g := fun X c => memberMX X.data X.plain (clRegionData X.skeleton c.block c.cl) κ.L κ.γ κ.δ κ.F
    (stateLayer X) (stateLayer_isLayering X) κ.base lam (bWN ψ κ X c.U) t κ.t1 κ.t2 E F' κ.g κ.h)
    hc e he hJ hJ' hA sp0 hA0]
  unfold KtilB ktildeB
  refine Finset.sum_congr rfl fun y hy => ?_
  have hn : ¬ twAt A A pstar := not_twAt_of_eq rfl
  unfold kTorB
  rw [ite_eq_right_iff.mpr (fun h => absurd h hn)]
  unfold kTB
  exact memberMX_idx rfl y.2.joint rfl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

end Canon

end WaveTurbulence.Flower.V5WB
