/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B2.Bot11

/-! # V5 Step 4d-B2: the bottom vine, part 12 (the FALSE-choice output)

`botState_false`: the output of a FALSE-choice LF operation at the bottom member `pstar` (same skeleton, same chain region).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {kind : Bool} {pstar : ι} [Fintype ι] [DecidableEq ι]

section Ops
variable (κ : KPar d) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
  (hcan : CanonicalObject p kind A.layered)
  (hel : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement pstar) (A.family.kind pstar)
    (A.family.atoms pstar) (A.family.upper pstar))
  (htc : CohOn A.layered ((A.data.tree (A.family.placement pstar).lower).linksAt
    (nodeSign A.skeleton.sig (A.family.placement pstar).lower.1)
    (inflatedPosition A.skeleton A.data.tree (A.family.placement pstar).lower.toNode)))
  (hcc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)).linksAt
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).firstLeaf A.plain).toNode)
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).secondLeaf A.plain).toNode)))

open Classical in
theorem botState_false (hb0 : c0.b = (A.family.placement pstar).lower)
    (con : LFConstruction (A.source pstar hcan hel htc hcc) false) (hL : κ.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|) :
    BotGoal κ A c0 pstar ⟨opOut A pstar hcan hel htc hcc con, ChainAt.nextA A c0 pstar false⟩ := by
  have hS := chain_slow c0 pstar hb0
  have hn := tw_false A hcan hel htc hcc con
  have hCq : ∀ q ∈ (clRegionalPairs A.plain c0.U).erase (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained),
      nativeCoupleLayered A.data A.plain (stateLayer A) (stateLayer_isLayering A) q =
        nativeCoupleLayered con.data A.plain (stateLayer (opOut A pstar hcan hel htc hcc con))
          (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) q := by
    intro q hq
    obtain ⟨hq0, _⟩ := Finset.mem_erase.mp hq
    have := native_couple_eq con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
      (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
      (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) q hq0
    have hp : (A.source pstar hcan hel htc hcc).pairs false q = q := pairOfLeaf_firstLeaf A.skeleton A.plain q
    rw [hp] at this
    exact this.symm
  have hCt : ∀ v ∈ (c0.U.erase c0.a).erase c0.b,
      nativeChainLayered A.data A.plain (stateLayer A) (stateLayer_isLayering A) v =
        nativeChainLayered con.data A.plain (stateLayer (opOut A pstar hcan hel htc hcc con))
          (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) v := by
    intro v hv
    exact (native_tree_eq con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
      (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
      (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) v (hb0 ▸ (Finset.mem_erase.mp hv).1)).symm
  have hCl : ∀ v ∈ c0.U.erase c0.a, stateLayer A (A.data.coreBranch A.plain v).toNode =
      stateLayer (opOut A pstar hcan hel htc hcc con) (con.data.coreBranch A.plain v).toNode := by
    intro v _
    exact (coreLayer_eq con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
      (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
      (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) v).symm
  have hd : decide (twAt A (opOut A pstar hcan hel htc hcc con) pstar) = false := by simp [hn]
  have hint : ∀ (κd : CLLocalDecoration (botR A c0) κ.L κ.base ![κ.e, κ.f, κ.g, κ.h]) (τ : CLInternalTime (botR A c0)),
      stBot κ A c0 pstar (opOut A pstar hcan hel htc hcc con) (clExtendIndices (botR A c0) κd.1) ![κ.t0, κ.t1, κ.t2]
        (clLocalClock (botR A c0) ![κ.t0, κ.t1, κ.t2] τ) =
      clLocalSummand con.data A.plain (botR A c0) κ.L κ.γ κ.δ κ.F
        (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
        κ.base ![κ.e, κ.f, κ.g, κ.h] ![κ.t0, κ.t1, κ.t2] κd τ := by
    intro κd τ
    have hFree : FreeDec (botR A c0) (clExtendIndices (botR A c0) κd.1) :=
      ⟨fun y hy => clExtendIndices_of_notMem _ _ hy, κd.2.1, κd.2.2.1⟩
    have hpx : PairedAt (A.family.placement pstar) (clExtendIndices (botR A c0) κd.1) :=
      hFree.2.2 _ hS.retained_internal
    refine Eq.trans ?_ (summand_same A.plain A.data con.data κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A)
      (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
      κ.base (botR A c0) (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)
      hS.b_mem_erase hS.p0_mem hCq hCt hCl _ _ κd τ).symm
    rw [sameIntB_eq_botKernel κ A c0 hb0 (opOut A pstar hcan hel htc hcc con) con.data
      (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
      (sigStar_false A hcan hel htc hcc con) _ hpx]
    unfold stBot epsOf
    rw [hd, if_neg hn, one_mul]
  have hfun : (fun (κd : CLLocalDecoration (botR A c0) κ.L κ.base ![κ.e, κ.f, κ.g, κ.h]) (τ : CLInternalTime (botR A c0)) =>
      stBot κ A c0 pstar (opOut A pstar hcan hel htc hcc con) (clExtendIndices (botR A c0) κd.1)
        ![κ.t0, κ.t1, κ.t2] (clLocalClock (botR A c0) ![κ.t0, κ.t1, κ.t2] τ)) =
      fun κd τ => clLocalSummand con.data A.plain (botR A c0) κ.L κ.γ κ.δ κ.F
        (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
        κ.base ![κ.e, κ.f, κ.g, κ.h] ![κ.t0, κ.t1, κ.t2] κd τ := funext fun κd => funext fun τ => hint κd τ
  refine ⟨?_, ?_⟩
  · have hk : twistedLocalKernel (opOut A pstar hcan hel htc hcc con) (ChainAt.nextA A c0 pstar false) κ.L κ.γ κ.δ κ.F
        κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f κ.g κ.h =
        clLocalKernel con.data A.plain (botR A c0) κ.L κ.γ κ.δ κ.F (stateLayer (opOut A pstar hcan hel htc hcc con))
          (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f κ.g κ.h :=
      clLocalKernel_idx (nextA_false_U A c0 pstar) (nextA_false_a A c0 pstar) (nextA_false_b A c0 pstar) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    rw [hk]
    unfold clLocalKernel
    congr 1
    refine tsum_congr fun κd => integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    exact (hint κd τ).symm
  · refine BOKd.congr ?_ hfun.symm
    exact BOKd_of_inputs c0.block (botR A c0) con.data A.plain κ.L κ.γ κ.δ κ.F
      (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
      κ.base hL (HF_of_all _ _ _ _ _ _ hF) _ _

end Ops

end WaveTurbulence.VineEstS5B2
