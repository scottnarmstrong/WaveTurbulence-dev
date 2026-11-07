/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RowSel.RowDataLF
public import WaveTurbulence.Foundations.VineEst.RowSel.SelDataLF
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.BotStateSkip

/-! # FLAT-MOD (R60), the bottom vine, states of the class, FALSE and TRUE choices (modulated `Bot12`-`Bot14`)

`BotGoalM`: the modulated per-state conclusion, `K^{U,λ}_z = c ζ ∑' ∫ lowModC · stBot`, with `BOKd`.  `botStateM_skip`, `botStateM_false`,
`botStateM_true`: the three kinds of state reached by a batch over the bottom member.  The pointwise identities (`stBot` against the
summand of the state, `hint` / `hpt`) are those of `Bot11`-`Bot14`; the modulation is a common factor (`lowModC_tw` at the twisted state).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C.FlatMod
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton
  WaveTurbulence.VineEstS5C.Cont TTree MeasureTheory

variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {kind : Bool} {kind : Bool} {pstar : ι} [Fintype ι] [DecidableEq ι]

section Ops
variable (κ : KPar d) (lam : ℝ) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
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
theorem botStateM_false (hb0 : c0.b = (A.family.placement pstar).lower)
    (con : LFConstruction (A.source pstar hcan hel htc hcc) false) (hL : κ.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|) :
    BotGoalM κ lam A c0 pstar ⟨opOut A pstar hcan hel htc hcc con, ChainAt.nextA A c0 pstar false⟩ := by
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
      hS.b_mem_erase hS.p0_mem hCq hCt hCl
      (VineEst.selDataEq_LF_false con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
        (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
        (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) _ _ (fun q hq => (Finset.mem_erase.mp hq).1)
        (fun v hv => hb0 ▸ (Finset.mem_erase.mp hv).1)).symm _ _ κd τ).symm
    rw [sameIntB_eq_botKernel κ A c0 hb0 (opOut A pstar hcan hel htc hcc con) con.data
      (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
      (sigStar_false A hcan hel htc hcc con) (rowQ_false_eq κ A hcan hel htc hcc con)
      (rowT_false_eq κ A hcan hel htc hcc con) _ hpx]
    unfold stBot epsOf
    rw [hd, if_neg hn, one_mul]
  have hfun : (fun (κd : CLLocalDecoration (botR A c0) κ.L κ.base ![κ.e, κ.f, κ.g, κ.h]) (τ : CLInternalTime (botR A c0)) =>
      stBot κ A c0 pstar (opOut A pstar hcan hel htc hcc con) (clExtendIndices (botR A c0) κd.1)
        ![κ.t0, κ.t1, κ.t2] (clLocalClock (botR A c0) ![κ.t0, κ.t1, κ.t2] τ)) =
      fun κd τ => clLocalSummand con.data A.plain (botR A c0) κ.L κ.γ κ.δ κ.F
        (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
        κ.base ![κ.e, κ.f, κ.g, κ.h] ![κ.t0, κ.t1, κ.t2] κd τ := funext fun κd => funext fun τ => hint κd τ
  refine ⟨?_, ?_⟩
  · have hk : twistedLocalKernelM lam (opOut A pstar hcan hel htc hcc con) (ChainAt.nextA A c0 pstar false) κ.L κ.γ κ.δ κ.F
        κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f κ.g κ.h =
        clLocalKernelModC con.data A.plain (botR A c0) κ.L κ.γ κ.δ κ.F (stateLayer (opOut A pstar hcan hel htc hcc con))
          (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) κ.base lam κ.t0 κ.t1 κ.t2 κ.e κ.f κ.g κ.h :=
      clLocalKernelModC_idx (nextA_false_U A c0 pstar) (nextA_false_a A c0 pstar) (nextA_false_b A c0 pstar) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    rw [hk]
    unfold clLocalKernelModC
    congr 1
    refine tsum_congr fun κd => integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    exact congrArg (fun y => lowModC (botR A c0) lam ![κ.t0, κ.t1, κ.t2] τ * y) (hint κd τ).symm
  · refine BOKd.congr (BOKd.lowMod (BOKd_of_inputs c0.block (botR A c0) con.data A.plain κ.L κ.γ κ.δ κ.F
      (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
      κ.base hL (HF_of_all _ _ _ _ _ _ hF) ![κ.e, κ.f, κ.g, κ.h] ![κ.t0, κ.t1, κ.t2]) lam ![κ.t0, κ.t1, κ.t2]) ?_
    funext κd τ
    exact congrArg (fun y => lowModC (botR A c0) lam ![κ.t0, κ.t1, κ.t2] τ * y) (hint κd τ).symm

end Ops

section Ops
variable (κ : KPar d) (lam : ℝ) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
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
theorem botStateM_true (hb0 : c0.b = (A.family.placement pstar).lower)
    (con : LFConstruction (A.source pstar hcan hel htc hcc) true) (hL : κ.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|) :
    BotGoalM κ lam A c0 pstar ⟨opOut A pstar hcan hel htc hcc con, ChainAt.nextA A c0 pstar true⟩ := by
  have hS := chain_slow c0 pstar hb0
  have hT := chain_stw c0 pstar hb0
  have ht := tw_true A hcan hel htc hcc con
  have hCq : ∀ q ∈ clRegionalPairs A.plain c0.U, q ≠ pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained →
      nativeCoupleLayered con.data (unitTwistGarden_plain A.skeleton (A.family.placement pstar) A.plain)
        (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
        (tp (A.family.placement pstar) A.plain q) =
      nativeCoupleLayered A.data A.plain (stateLayer A) (stateLayer_isLayering A) q :=
    fun q _ hq => native_couple_eq con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
      (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
      (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) q hq
  have hCt : ∀ v ∈ c0.U.erase c0.a, v ≠ c0.b →
      nativeChainLayered con.data (unitTwistGarden_plain A.skeleton (A.family.placement pstar) A.plain)
        (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
        (eB (A.family.placement pstar) v) =
      nativeChainLayered A.data A.plain (stateLayer A) (stateLayer_isLayering A) v :=
    fun v _ hv => native_tree_eq con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
      (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
      (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) v (hb0 ▸ hv)
  have hCl : ∀ v ∈ c0.U.erase c0.a,
      stateLayer (opOut A pstar hcan hel htc hcc con)
        (con.data.coreBranch (unitTwistGarden_plain A.skeleton (A.family.placement pstar) A.plain)
          (eB (A.family.placement pstar) v)).toNode =
      stateLayer A (A.data.coreBranch A.plain v).toNode :=
    fun v _ => coreLayer_eq con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
      (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
      (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) v
  have hd : decide (twAt A (opOut A pstar hcan hel htc hcc con) pstar) = true := by simp [ht]
  have hε : epsOf A pstar (opOut A pstar hcan hel htc hcc con) = -1 := by
    unfold epsOf; rw [if_pos ht]
  have hpt : ∀ (κd : CLLocalDecoration (botR A c0) κ.L κ.base ![κ.e, κ.f, κ.g, κ.h]) (τ : CLInternalTime (botR A c0)),
      stBot κ A c0 pstar (opOut A pstar hcan hel htc hcc con) (clExtendIndices (botR A c0) κd.1) ![κ.t0, κ.t1, κ.t2]
        (clLocalClock (botR A c0) ![κ.t0, κ.t1, κ.t2] τ) =
      -twIntB (RS := botR A c0) (A.family.placement pstar) A.plain A.data con.data κ.L κ.γ κ.δ κ.F (stateLayer A)
        (stateLayer_isLayering A) (stateLayer (opOut A pstar hcan hel htc hcc con))
        (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) κ.base ![κ.t0, κ.t1, κ.t2]
        (clExtendIndices (botR A c0) κd.1) (clLocalClock (botR A c0) ![κ.t0, κ.t1, κ.t2] τ)
        (clLocalClock (clRegionData (chosenSkeleton A.skeleton (A.family.placement pstar) true) (c0.next pstar true).block
          (c0.next pstar true).cl) ![κ.t0, κ.t1, κ.t2]
          (tEquivS (A.family.placement pstar) (botR A c0)
            (clRegionData (chosenSkeleton A.skeleton (A.family.placement pstar) true) (c0.next pstar true).block
              (c0.next pstar true).cl) τ)) := by
    intro κd τ
    have hu := fun v (hv : v ∈ c0.U) => clockS_corr (A.family.placement pstar) (botR A c0)
      (clRegionData (chosenSkeleton A.skeleton (A.family.placement pstar) true) (c0.next pstar true).block
        (c0.next pstar true).cl) ![κ.t0, κ.t1, κ.t2] τ hv
    have h1 := twIntB_eq_botKernel κ A c0 hb0 (opOut A pstar hcan hel htc hcc con) con.data
      (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
      (sigStar_true A hcan hel htc hcc con) (rowQ_true_eq κ A hcan hel htc hcc con)
      (rowT_true_eq κ A hcan hel htc hcc con) (clExtendIndices (botR A c0) κd.1) ![κ.t0, κ.t1, κ.t2]
      (clLocalClock (botR A c0) ![κ.t0, κ.t1, κ.t2] τ)
      (clLocalClock (clRegionData (chosenSkeleton A.skeleton (A.family.placement pstar) true) (c0.next pstar true).block
          (c0.next pstar true).cl) ![κ.t0, κ.t1, κ.t2]
          (tEquivS (A.family.placement pstar) (botR A c0)
            (clRegionData (chosenSkeleton A.skeleton (A.family.placement pstar) true) (c0.next pstar true).block
              (c0.next pstar true).cl) τ))
      (hu _ hS.block.2.2.1) (hu _ hS.qb_mem) (hu _ hS.qr_mem)
    unfold stBot
    rw [hε, hd, neg_one_mul]
    exact congrArg Neg.neg h1.symm
  have hptM : ∀ (κd : CLLocalDecoration (botR A c0) κ.L κ.base ![κ.e, κ.f, κ.g, κ.h]) (τ : CLInternalTime (botR A c0)),
      lowModC (botR A c0) lam ![κ.t0, κ.t1, κ.t2] τ *
        stBot κ A c0 pstar (opOut A pstar hcan hel htc hcc con) (clExtendIndices (botR A c0) κd.1) ![κ.t0, κ.t1, κ.t2]
          (clLocalClock (botR A c0) ![κ.t0, κ.t1, κ.t2] τ) =
      -(lowModC (botR A c0) lam ![κ.t0, κ.t1, κ.t2] τ *
        twIntB (RS := botR A c0) (A.family.placement pstar) A.plain A.data con.data κ.L κ.γ κ.δ κ.F (stateLayer A)
          (stateLayer_isLayering A) (stateLayer (opOut A pstar hcan hel htc hcc con))
          (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) κ.base ![κ.t0, κ.t1, κ.t2]
          (clExtendIndices (botR A c0) κd.1) (clLocalClock (botR A c0) ![κ.t0, κ.t1, κ.t2] τ)
          (clLocalClock (clRegionData (chosenSkeleton A.skeleton (A.family.placement pstar) true) (c0.next pstar true).block
            (c0.next pstar true).cl) ![κ.t0, κ.t1, κ.t2]
            (tEquivS (A.family.placement pstar) (botR A c0)
              (clRegionData (chosenSkeleton A.skeleton (A.family.placement pstar) true) (c0.next pstar true).block
                (c0.next pstar true).cl) τ))) := by
    intro κd τ
    rw [hpt κd τ]
    ring
  refine ⟨?_, ?_⟩
  · have hk : twistedLocalKernelM lam (opOut A pstar hcan hel htc hcc con) (ChainAt.nextA A c0 pstar true) κ.L κ.γ κ.δ κ.F
        κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f κ.g κ.h =
        clLocalKernelModC con.data (unitTwistGarden_plain A.skeleton (A.family.placement pstar) A.plain)
          (clRegionData (chosenSkeleton A.skeleton (A.family.placement pstar) true) (c0.next pstar true).block
            (c0.next pstar true).cl) κ.L κ.γ κ.δ κ.F (stateLayer (opOut A pstar hcan hel htc hcc con))
          (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) κ.base lam κ.t0 κ.t1 κ.t2 κ.e κ.f κ.g κ.h :=
      clLocalKernelModC_idx (nextA_true_U A c0 pstar) (nextA_true_a A c0 pstar) (nextA_true_b A c0 pstar) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    rw [hk]
    refine (clLocalKernelModC_tw A.plain κ.L κ.γ κ.δ κ.F κ.base lam (A.family.placement pstar) hT A.data con.data
      (stateLayer A) (stateLayer_isLayering A) (stateLayer (opOut A pstar hcan hel htc hcc con))
      (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) hCq hCt hCl
      (fun q _ hq => Flower.V5W.coupleIncoh_LF con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
        (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
        (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) q hq)
      (fun v _ hv => Flower.V5W.treeIncoh_LF con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
        (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
        (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) v (hb0 ▸ hv))
      (fun v _ => coreLayer_eq con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
        (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
        (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) v) _ _ _ _ _ _ _).trans ?_
    dsimp only
    simp_rw [hptM, integral_neg, tsum_neg]
    simp only [mul_neg]
    rfl
  · have hg : BOKd (clRegionData (chosenSkeleton A.skeleton (A.family.placement pstar) true) (c0.next pstar true).block
        (c0.next pstar true).cl) κ.L κ.base ![κ.e, κ.f, κ.g, κ.h]
        (fun κ' τ' => lowModC (clRegionData (chosenSkeleton A.skeleton (A.family.placement pstar) true)
          (c0.next pstar true).block (c0.next pstar true).cl) lam ![κ.t0, κ.t1, κ.t2] τ' *
          clLocalSummand con.data (unitTwistGarden_plain A.skeleton (A.family.placement pstar) A.plain)
          (clRegionData (chosenSkeleton A.skeleton (A.family.placement pstar) true) (c0.next pstar true).block
            (c0.next pstar true).cl) κ.L κ.γ κ.δ κ.F (stateLayer (opOut A pstar hcan hel htc hcc con))
          (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) κ.base ![κ.e, κ.f, κ.g, κ.h]
          ![κ.t0, κ.t1, κ.t2] κ' τ') :=
      BOKd.lowMod (BOKd_of_inputs (c0.next pstar true).block _ con.data
        (unitTwistGarden_plain A.skeleton (A.family.placement pstar) A.plain) κ.L κ.γ κ.δ κ.F
        (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
        κ.base hL (HF_of_all _ _ _ _ _ _ hF) ![κ.e, κ.f, κ.g, κ.h] ![κ.t0, κ.t1, κ.t2]) lam ![κ.t0, κ.t1, κ.t2]
    have h2 := BOKd_twM A.plain κ.L κ.γ κ.δ κ.F κ.base lam (A.family.placement pstar) hT A.data con.data (stateLayer A)
      (stateLayer_isLayering A) (stateLayer (opOut A pstar hcan hel htc hcc con))
      (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) hCq hCt hCl
      (fun q _ hq => Flower.V5W.coupleIncoh_LF con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
        (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
        (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) q hq)
      (fun v _ hv => Flower.V5W.treeIncoh_LF con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
        (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
        (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) v (hb0 ▸ hv))
      (fun v _ => coreLayer_eq con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
        (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
        (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) v) _ _ hg
    refine BOKd.congr (h2.const_mul (-1)) ?_
    funext κd τ
    beta_reduce
    rw [hpt κd τ, neg_one_mul, mul_neg]
    rfl

end Ops

end WaveTurbulence.VineEstS5C.FlatMod
