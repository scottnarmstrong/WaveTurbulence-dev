/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.BotAbs1
public import WaveTurbulence.Foundations.VineEst.VineEstS5B2.Bot19

/-! # `UAbs` of the bottom bundle, per state (V5 Step 4d part C, 4d-B2 integration)

`stBot_skip_eq`, `stBot_false_eq`, `stBot_true_eq`: the signed A-chart integrand `stBot` of a state of the class is the native CL local
summand of the state (skip, FALSE choice) or the negative of the CL local summand of the twisted garden at the transported decoration and
time (TRUE choice).  `uAbs_stBot_skip/false/true`: the corresponding uniform `UAbs` bounds.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.VineEstS5B2 WaveTurbulence.VineEstS2 WaveTurbulence.LGSpine WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {kind : Bool} {pstar : ι} [Fintype ι] [DecidableEq ι]

/-- The parameters with the exterior times and boundary momenta replaced. -/
def kparAt (κ : KPar d) (t : Fin 3 → ℝ) (β : Fin 4 → Mom d) : KPar d :=
  { κ with t0 := t 0, t1 := t 1, t2 := t 2, e := β 0, f := β 1, g := β 2, h := β 3 }

theorem vec4_eta {d : ℕ} (β : Fin 4 → Mom d) : β = ![β 0, β 1, β 2, β 3] := by
  ext i; fin_cases i <;> rfl

open Classical in
theorem stBot_skip_eq (κ : KPar d) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
    (hb0 : c0.b = (A.family.placement pstar).lower)
    (κd : CLLocalDecoration (botR A c0) κ.L κ.base ![κ.e, κ.f, κ.g, κ.h]) (τ : CLInternalTime (botR A c0)) :
    stBot κ A c0 pstar A (clExtendIndices (botR A c0) κd.1) ![κ.t0, κ.t1, κ.t2]
        (clLocalClock (botR A c0) ![κ.t0, κ.t1, κ.t2] τ) =
      clLocalSummand A.data A.plain (botR A c0) κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A) κ.base
        ![κ.e, κ.f, κ.g, κ.h] ![κ.t0, κ.t1, κ.t2] κd τ := by
  have hS := chain_slow c0 pstar hb0
  have hn : ¬ twAt A A pstar := not_twAt_of_eq rfl
  have hFree : FreeDec (botR A c0) (clExtendIndices (botR A c0) κd.1) :=
    ⟨fun y hy => clExtendIndices_of_notMem _ _ hy, κd.2.1, κd.2.2.1⟩
  have hpx : PairedAt (A.family.placement pstar) (clExtendIndices (botR A c0) κd.1) :=
    hFree.2.2 _ hS.retained_internal
  rw [summand_same A.plain A.data A.data κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A) (stateLayer A)
    (stateLayer_isLayering A) κ.base (botR A c0) (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)
    hS.b_mem_erase hS.p0_mem (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)]
  rw [sameIntB_eq_botKernel κ A c0 hb0 A A.data (stateLayer A) (stateLayer_isLayering A) rfl _ hpx]
  unfold stBot epsOf
  have hd : decide (twAt A A pstar) = false := by simp [hn]
  rw [hd, if_neg hn, one_mul]

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
theorem stBot_false_eq (hb0 : c0.b = (A.family.placement pstar).lower)
    (con : LFConstruction (A.source pstar hcan hel htc hcc) false)
    (κd : CLLocalDecoration (botR A c0) κ.L κ.base ![κ.e, κ.f, κ.g, κ.h]) (τ : CLInternalTime (botR A c0)) :
    stBot κ A c0 pstar (opOut A pstar hcan hel htc hcc con) (clExtendIndices (botR A c0) κd.1) ![κ.t0, κ.t1, κ.t2]
        (clLocalClock (botR A c0) ![κ.t0, κ.t1, κ.t2] τ) =
      clLocalSummand con.data A.plain (botR A c0) κ.L κ.γ κ.δ κ.F
        (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
        κ.base ![κ.e, κ.f, κ.g, κ.h] ![κ.t0, κ.t1, κ.t2] κd τ := by
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

open Classical in
theorem stBot_true_eq (hb0 : c0.b = (A.family.placement pstar).lower)
    (con : LFConstruction (A.source pstar hcan hel htc hcc) true)
    (κd : CLLocalDecoration (botR A c0) κ.L κ.base ![κ.e, κ.f, κ.g, κ.h]) (τ : CLInternalTime (botR A c0)) :
    stBot κ A c0 pstar (opOut A pstar hcan hel htc hcc con) (clExtendIndices (botR A c0) κd.1) ![κ.t0, κ.t1, κ.t2]
        (clLocalClock (botR A c0) ![κ.t0, κ.t1, κ.t2] τ) =
      -clLocalSummand con.data (unitTwistGarden_plain A.skeleton (A.family.placement pstar) A.plain)
        (clRegionData (chosenSkeleton A.skeleton (A.family.placement pstar) true) (c0.next pstar true).block
          (c0.next pstar true).cl) κ.L κ.γ κ.δ κ.F (stateLayer (opOut A pstar hcan hel htc hcc con))
        (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) κ.base ![κ.e, κ.f, κ.g, κ.h] ![κ.t0, κ.t1, κ.t2]
        (VineEstS5B2.decEquiv (A.family.placement pstar) (chain_stw c0 pstar hb0) κ.L κ.base ![κ.e, κ.f, κ.g, κ.h] κd)
        (tEquivS (A.family.placement pstar) (botR A c0)
          (clRegionData (chosenSkeleton A.skeleton (A.family.placement pstar) true) (c0.next pstar true).block
            (c0.next pstar true).cl) τ) := by
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
  have h2 := summand_tw (A.family.placement pstar) hT A.plain A.data con.data κ.L κ.γ κ.δ κ.F (stateLayer A)
    (stateLayer_isLayering A) (stateLayer (opOut A pstar hcan hel htc hcc con))
    (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) κ.base hCq hCt hCl ![κ.e, κ.f, κ.g, κ.h]
    ![κ.t0, κ.t1, κ.t2] κd τ
  have h3 := congrArg Neg.neg h1.symm
  unfold stBot
  rw [hε, hd, neg_one_mul]
  exact h3.trans (congrArg Neg.neg h2.symm)

end Ops

end WaveTurbulence.VineEstS5C
