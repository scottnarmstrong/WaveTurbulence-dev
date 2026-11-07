/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B2.Bot13

/-! # V5 Step 4d-B2: the bottom vine, part 14 (`botState_true`)

See `Bot13`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {kind : Bool} {pstar : ι} [Fintype ι] [DecidableEq ι]

/-- TRUE-choice states: `twIntB` is `botKernel` with the pattern `tw = true`. -/
theorem twIntB_eq_botKernel (κ : KPar d) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
    (hb0 : c0.b = (A.family.placement pstar).lower) (G : FamilyReconstruction w ι)
    (D' : ReconstructionData (unitTwistGarden A.skeleton (A.family.placement pstar)))
    (layer' : GNode (D'.forest (unitTwistGarden_plain A.skeleton (A.family.placement pstar) A.plain)) → ℕ)
    (hLayer' : IsLayering (D'.garden (unitTwistGarden_plain A.skeleton (A.family.placement pstar) A.plain)) layer')
    (hσ : sigStar G pstar = ((unitTwistGarden A.skeleton (A.family.placement pstar)).sign
        (eB (A.family.placement pstar) (A.family.placement pstar).lower).toNode,
      nativeCoupleLayered D' (unitTwistGarden_plain A.skeleton (A.family.placement pstar) A.plain) layer' hLayer'
        (tp (A.family.placement pstar) A.plain (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)),
      nativeChainLayered D' (unitTwistGarden_plain A.skeleton (A.family.placement pstar) A.plain) layer' hLayer'
        (eB (A.family.placement pstar) (A.family.placement pstar).lower)))
    (x : GNode A.skeleton.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (u : GBranch A.skeleton.tree → ℝ)
    (u' : GBranch (unitTwistGarden A.skeleton (A.family.placement pstar)).tree → ℝ)
    (hub : u' (eB (A.family.placement pstar) c0.b) = u c0.b)
    (hqb : u' (eB (A.family.placement pstar) (qbOf (A.family.placement pstar))) = u (qbOf (A.family.placement pstar)))
    (hqr : u' (eB (A.family.placement pstar) (qrOf (A.family.placement pstar))) = u (qrOf (A.family.placement pstar))) :
    twIntB (RS := botR A c0) (A.family.placement pstar) A.plain A.data D' κ.L κ.γ κ.δ κ.F (stateLayer A)
        (stateLayer_isLayering A) layer' hLayer' κ.base t x u u' =
      botKernel κ A c0 pstar true (nuOf G pstar) (rowQ κ G pstar) (rowT κ G pstar) x t u := by
  have hex := exc_tw (A.family.placement pstar) A.plain D' κ.L κ.γ κ.δ κ.F layer' hLayer' κ.base c0.U (a := c0.a)
    hb0 x u' u hub hqb hqr
  unfold twIntB botKernel
  rw [hex]
  unfold nuOf rowQ rowT
  rw [hσ]
  simp only [if_true]
  have e1 : eB (A.family.placement pstar) c0.b = eB (A.family.placement pstar) (A.family.placement pstar).lower := by
    rw [hb0]
  have e2 : u c0.b = u c0.b := rfl
  rw [e1]

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
theorem botState_true (hb0 : c0.b = (A.family.placement pstar).lower)
    (con : LFConstruction (A.source pstar hcan hel htc hcc) true) (hL : κ.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|) :
    BotGoal κ A c0 pstar ⟨opOut A pstar hcan hel htc hcc con, ChainAt.nextA A c0 pstar true⟩ := by
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
      (sigStar_true A hcan hel htc hcc con) (clExtendIndices (botR A c0) κd.1) ![κ.t0, κ.t1, κ.t2]
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
  refine ⟨?_, ?_⟩
  · have hk : twistedLocalKernel (opOut A pstar hcan hel htc hcc con) (ChainAt.nextA A c0 pstar true) κ.L κ.γ κ.δ κ.F
        κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f κ.g κ.h =
        clLocalKernel con.data (unitTwistGarden_plain A.skeleton (A.family.placement pstar) A.plain)
          (clRegionData (chosenSkeleton A.skeleton (A.family.placement pstar) true) (c0.next pstar true).block
            (c0.next pstar true).cl) κ.L κ.γ κ.δ κ.F (stateLayer (opOut A pstar hcan hel htc hcc con))
          (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f κ.g κ.h :=
      clLocalKernel_idx (nextA_true_U A c0 pstar) (nextA_true_a A c0 pstar) (nextA_true_b A c0 pstar) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    rw [hk]
    refine (clLocalKernel_tw A.plain κ.L κ.γ κ.δ κ.F κ.base (A.family.placement pstar) hT A.data con.data
      (stateLayer A) (stateLayer_isLayering A) (stateLayer (opOut A pstar hcan hel htc hcc con))
      (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) hCq hCt hCl _ _ _ _ _ _ _).trans ?_
    dsimp only
    simp_rw [hpt, integral_neg, tsum_neg]
    simp only [mul_neg]
    rfl
  · have hg : BOKd (clRegionData (chosenSkeleton A.skeleton (A.family.placement pstar) true) (c0.next pstar true).block
        (c0.next pstar true).cl) κ.L κ.base ![κ.e, κ.f, κ.g, κ.h]
        (fun κ' τ' => clLocalSummand con.data (unitTwistGarden_plain A.skeleton (A.family.placement pstar) A.plain)
          (clRegionData (chosenSkeleton A.skeleton (A.family.placement pstar) true) (c0.next pstar true).block
            (c0.next pstar true).cl) κ.L κ.γ κ.δ κ.F (stateLayer (opOut A pstar hcan hel htc hcc con))
          (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) κ.base ![κ.e, κ.f, κ.g, κ.h]
          ![κ.t0, κ.t1, κ.t2] κ' τ') :=
      BOKd_of_inputs (c0.next pstar true).block _ con.data
        (unitTwistGarden_plain A.skeleton (A.family.placement pstar) A.plain) κ.L κ.γ κ.δ κ.F
        (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
        κ.base hL (HF_of_all _ _ _ _ _ _ hF) _ _
    have h2 := BOKd_tw (A.family.placement pstar) hT A.plain A.data con.data κ.L κ.γ κ.δ κ.F (stateLayer A)
      (stateLayer_isLayering A) (stateLayer (opOut A pstar hcan hel htc hcc con))
      (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) κ.base hCq hCt hCl _ _ hg
    refine BOKd.congr (h2.const_mul (-1)) ?_
    funext κd τ
    rw [neg_one_mul]
    exact (hpt κd τ).symm

end Ops

end WaveTurbulence.VineEstS5B2
