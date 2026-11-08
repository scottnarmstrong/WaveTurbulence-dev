/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.V5WB.Common
public import WaveTurbulence.Foundations.Flower.V5WB.B.Member

public import WaveTurbulence.Foundations.Flower.V5WB.B.LowerKernel
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceK.Engine
public import WaveTurbulence.Foundations.Flower.V5WB.K.WeightedBundle
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.BotSum
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.BotKernel
public import WaveTurbulence.Foundations.VineEst.RowSel.SelDataLF
public import WaveTurbulence.Foundations.VineEst.RowSel.RowDataLF

/-! # V5-SPACE-EXT: weighted FLAT-MOD for the class with one operative bottom vine

Each member carries the bond weight of its own region. Under the bottom vine's TRUE operation the region's bond
weight is transported exactly (molecule isomorphism, `bWN_twist`), under a FALSE one it is unchanged (same core
layers), so every member's weighted kernel is the common-chart weighted bottom kernel of the start state. Adapted
from `VineSpaceK.WeightedNative/BottomStates/Bottom`. -/

/-! Copied by source (V5W-B-WORLD) from V5W-A's port `Flower/V5WA/VineSpaceB/Bottom.lean` (see `COPIED-SHA256SUMS`): namespace `WaveTurbulence.Flower.V5WB`, every row selector (`variable [RowSel]`), the bond weight `bW` replaced by the masked, normalized `bWN` (`ψ : WD d`, bound `bWNB`). -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.Flower.V5WB
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
variable {kind : Bool}
open Classical TTree Twist LFTwist Links RegRed Reg.Skeleton MeasureTheory Finset
  VineEstS4 VineEstS5B VineEstS5B2 VineEstS5C VineEstS5C.Cont VineEstS5C.FlatMod

section Native
variable {w d : ℕ} {G : Garden w} (P : CorePlacement G)
  {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G S a b}
  {R' : CLRegionData (unitTwistGarden G P) (twistedAtoms G P S) (eB P a) (eB P b)}
  (h : STw P R R')

include h in
theorem memberMX_tw_W (hG : G.IsPlain) (D : ReconstructionData G)
    (D' : ReconstructionData (unitTwistGarden G P))
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer)
    (layer' : GNode (D'.forest (unitTwistGarden_plain G P hG)) → ℕ)
    (hLayer' : IsLayering (D'.garden (unitTwistGarden_plain G P hG)) layer')
    (hC : ∀ q ∈ clRegionalPairs hG S, q ≠ pairOfLeaf G hG P.retained →
      nativeCoupleLayered D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG q) =
        nativeCoupleLayered D hG layer hLayer q)
    (hT : ∀ v ∈ S.erase a, v ≠ b →
      nativeChainLayered D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
        nativeChainLayered D hG layer hLayer v)
    (hl : ∀ v ∈ S.erase a, layer' (D'.coreBranch (unitTwistGarden_plain G P hG) (eB P v)).toNode =
      layer (D.coreBranch hG v).toNode)
    (hCi : ∀ q ∈ clRegionalPairs hG S, q ≠ pairOfLeaf G hG P.retained →
      Flower.V5W.coupleIncoh D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG q) =
        Flower.V5W.coupleIncoh D hG layer hLayer q)
    (hTi : ∀ v ∈ S.erase a, v ≠ b →
      Flower.V5W.treeIncoh D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
        Flower.V5W.treeIncoh D hG layer hLayer v)
    (hlS : ∀ v ∈ S, layer' (D'.coreBranch (unitTwistGarden_plain G P hG) (eB P v)).toNode =
      layer (D.coreBranch hG v).toNode)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (lam : ℝ)
    (m : (GNode G.tree → Fin d → ℤ) → ℂ) (m' : (GNode (unitTwistGarden G P).tree → Fin d → ℤ) → ℂ)
    (t0 t1 t2 : ℝ) (e f g h' : Mom d)
    (hm : ∀ κ : CLLocalDecoration R L base ![e, f, g, h'],
      m' (clExtendIndices R' (VineEstS5B2.decEquiv P h L base ![e, f, g, h'] κ).1) = m (clExtendIndices R κ.1)) :
    memberMX D' (unitTwistGarden_plain G P hG) R' L γ δ F layer' hLayer' base lam m' t0 t1 t2 e f g h' =
    -((coupling d L γ δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R *
      ∑' κ : CLLocalDecoration R L base ![e, f, g, h'], ∫ τ : CLInternalTime R,
        m (clExtendIndices R κ.1) *
        (lowModC R lam ![t0, t1, t2] τ *
          twIntB (RS := R) P hG D D' L γ δ F layer hLayer layer' hLayer' base ![t0, t1, t2]
            (clExtendIndices R κ.1) (clLocalClock R ![t0, t1, t2] τ)
            (clLocalClock R' ![t0, t1, t2] (tEquivS P R R' τ)))) := by
  unfold memberMX
  rw [order1_rigid P R R', h.zeta]
  suffices key : (∑' κ' : CLLocalDecoration R' L base ![e, f, g, h'], ∫ τ' : CLInternalTime R',
      m' (clExtendIndices R' κ'.1) *
        (lowModC R' lam ![t0, t1, t2] τ' *
          clLocalSummand D' (unitTwistGarden_plain G P hG) R' L γ δ F layer' hLayer' base
            ![e, f, g, h'] ![t0, t1, t2] κ' τ')) =
      ∑' κ : CLLocalDecoration R L base ![e, f, g, h'], ∫ τ : CLInternalTime R,
        m (clExtendIndices R κ.1) *
          (lowModC R lam ![t0, t1, t2] τ *
          twIntB (RS := R) P hG D D' L γ δ F layer hLayer layer' hLayer' base ![t0, t1, t2]
            (clExtendIndices R κ.1) (clLocalClock R ![t0, t1, t2] τ)
            (clLocalClock R' ![t0, t1, t2] (tEquivS P R R' τ))) by
    rw [key]
    ring
  rw [← (VineEstS5B2.decEquiv P h L base ![e, f, g, h']).tsum_eq]
  refine tsum_congr fun κ => ?_
  rw [← (tEquivS_measurePreserving P R R').integral_comp'
    (g := fun τ' => m' (clExtendIndices R' (VineEstS5B2.decEquiv P h L base ![e, f, g, h'] κ).1) *
      (lowModC R' lam ![t0, t1, t2] τ' *
        clLocalSummand D' (unitTwistGarden_plain G P hG) R' L γ δ F layer' hLayer' base
          ![e, f, g, h'] ![t0, t1, t2] (VineEstS5B2.decEquiv P h L base ![e, f, g, h'] κ) τ'))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  beta_reduce
  rw [hm κ, lowModC_tw P h.block.2.2.1 lam _ τ,
    summand_tw P h hG D D' L γ δ F layer hLayer layer' hLayer' base hC hT hl hCi hTi hlS _ _ κ τ]

end Native

variable {w d p : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {pstar : ι}

def weightedBotKernelB (κ : KPar d) (lam : ℝ) (ψ : WD d)
    (A : FamilyReconstruction w ι) (c : ChainAt A.skeleton A.family)
    (i : ι) (Z : FamilyReconstruction w ι) : ℂ :=
  (coupling d κ.L κ.γ κ.δ : ℂ) ^ clLocalOrder1 (botR A c) * clLocalZeta (botR A c) *
    ∑' kd : CLLocalDecoration (botR A c) κ.L κ.base ![κ.e, κ.f, κ.g, κ.h],
      ∫ τ : CLInternalTime (botR A c),
        bWN ψ κ A c.U (clExtendIndices (botR A c) kd.1) *
        (lowModC (botR A c) lam ![κ.t0, κ.t1, κ.t2] τ *
        stBot κ A c i Z (clExtendIndices (botR A c) kd.1) ![κ.t0, κ.t1, κ.t2]
          (clLocalClock (botR A c) ![κ.t0, κ.t1, κ.t2] τ))

theorem memberB_skip_eq (κ : KPar d) (lam : ℝ) (ψ : WD d)
    (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
    (hb0 : c0.b = (A.family.placement pstar).lower) :
    memberB κ lam ψ A c0 = weightedBotKernelB κ lam ψ A c0 pstar A := by
  have hS := chain_slow c0 pstar hb0
  have hn : ¬ twAt A A pstar := not_twAt_of_eq rfl
  have hint : ∀ (κd : CLLocalDecoration (botR A c0) κ.L κ.base ![κ.e, κ.f, κ.g, κ.h]) (τ : CLInternalTime (botR A c0)),
      stBot κ A c0 pstar A (clExtendIndices (botR A c0) κd.1) ![κ.t0, κ.t1, κ.t2]
        (clLocalClock (botR A c0) ![κ.t0, κ.t1, κ.t2] τ) =
      clLocalSummand A.data A.plain (botR A c0) κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A) κ.base
        ![κ.e, κ.f, κ.g, κ.h] ![κ.t0, κ.t1, κ.t2] κd τ := by
    intro κd τ
    have hFree : FreeDec (botR A c0) (clExtendIndices (botR A c0) κd.1) :=
      ⟨fun y hy => clExtendIndices_of_notMem _ _ hy, κd.2.1, κd.2.2.1⟩
    have hpx : PairedAt (A.family.placement pstar) (clExtendIndices (botR A c0) κd.1) :=
      hFree.2.2 _ hS.retained_internal
    rw [summand_same A.plain A.data A.data κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A) (stateLayer A)
      (stateLayer_isLayering A) κ.base (botR A c0) (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)
      hS.b_mem_erase hS.p0_mem (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (VineEst.SelDataEq.refl _ _ _ _ _ _)]
    rw [sameIntB_eq_botKernel κ A c0 hb0 A A.data (stateLayer A) (stateLayer_isLayering A) rfl rfl rfl _ hpx]
    unfold stBot epsOf
    have hd : decide (twAt A A pstar) = false := by simp [hn]
    rw [hd, ite_eq_right hn, one_mul]
  unfold memberB memberMX weightedBotKernelB
  congr 1
  refine tsum_congr fun kd => integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  exact congrArg (fun y => bWN ψ κ A c0.U (clExtendIndices (botR A c0) kd.1) *
    (lowModC (botR A c0) lam ![κ.t0, κ.t1, κ.t2] τ * y)) (hint kd τ).symm

section Ops
variable (κ : KPar d) (lam : ℝ) (ψ : WD d) (A : FamilyReconstruction w ι)
  (c0 : ChainAt A.skeleton A.family)
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

theorem memberB_false_eq (hb0 : c0.b = (A.family.placement pstar).lower)
    (con : LFConstruction (A.source pstar hcan hel htc hcc) false) :
    memberB κ lam ψ (opOut A pstar hcan hel htc hcc con) (ChainAt.nextA A c0 pstar false) =
      weightedBotKernelB κ lam ψ A c0 pstar (opOut A pstar hcan hel htc hcc con) := by
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
    rw [hd, ite_eq_right hn, one_mul]
  have hw : bWN ψ κ (opOut A pstar hcan hel htc hcc con) (ChainAt.nextA A c0 pstar false).U = bWN ψ κ A c0.U := by
    rw [nextA_false_U A c0 pstar]
    exact bWN_false A pstar hcan hel htc hcc ψ κ con c0.U
  unfold memberB
  rw [hw]
  refine (memberMX_idx (nextA_false_U A c0 pstar) (nextA_false_a A c0 pstar)
    (nextA_false_b A c0 pstar) _ (botR A c0) con.data _ κ.L κ.γ κ.δ κ.F
    (stateLayer (opOut A pstar hcan hel htc hcc con))
    (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) κ.base lam (bWN ψ κ A c0.U)
    κ.t0 κ.t1 κ.t2 κ.e κ.f κ.g κ.h).trans ?_
  unfold memberMX weightedBotKernelB
  congr 1
  refine tsum_congr fun kd => integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  exact congrArg (fun y => bWN ψ κ A c0.U (clExtendIndices (botR A c0) kd.1) *
    (lowModC (botR A c0) lam ![κ.t0, κ.t1, κ.t2] τ * y)) (hint kd τ).symm

theorem memberB_true_eq (hb0 : c0.b = (A.family.placement pstar).lower)
    (con : LFConstruction (A.source pstar hcan hel htc hcc) true) :
    memberB κ lam ψ (opOut A pstar hcan hel htc hcc con) (ChainAt.nextA A c0 pstar true) =
      weightedBotKernelB κ lam ψ A c0 pstar (opOut A pstar hcan hel htc hcc con) := by
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
    unfold epsOf; rw [ite_eq_left ht]
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
  have hw : bWN ψ κ (opOut A pstar hcan hel htc hcc con) (ChainAt.nextA A c0 pstar true).U =
      bWN ψ κ (opOut A pstar hcan hel htc hcc con) (twistedAtoms A.skeleton (A.family.placement pstar) c0.U) := by
    rw [nextA_true_U A c0 pstar]
  unfold memberB
  rw [hw]
  refine (memberMX_idx (nextA_true_U A c0 pstar) (nextA_true_a A c0 pstar)
    (nextA_true_b A c0 pstar) _ (clRegionData (chosenSkeleton A.skeleton (A.family.placement pstar) true)
      (c0.next pstar true).block (c0.next pstar true).cl) con.data _ κ.L κ.γ κ.δ κ.F
    (stateLayer (opOut A pstar hcan hel htc hcc con))
    (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) κ.base lam _
    κ.t0 κ.t1 κ.t2 κ.e κ.f κ.g κ.h).trans ?_
  refine (memberMX_tw_W (A.family.placement pstar) hT A.plain A.data con.data
    (stateLayer A) (stateLayer_isLayering A)
    (stateLayer (opOut A pstar hcan hel htc hcc con))
    (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) hCq hCt hCl
    (fun q _ hq => Flower.V5W.coupleIncoh_LF con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
      (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
      (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) q hq)
    (fun v _ hv => Flower.V5W.treeIncoh_LF con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
      (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
      (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) v (hb0 ▸ hv))
    (fun v _ => coreLayer_eq con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
      (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
      (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) v)
    κ.L κ.γ κ.δ κ.F κ.base lam (bWN ψ κ A c0.U) _ κ.t0 κ.t1 κ.t2 κ.e κ.f κ.g κ.h ?_).trans ?_
  · intro κd
    have hFree : FreeDec (botR A c0) (clExtendIndices (botR A c0) κd.1) :=
      ⟨fun y hy => clExtendIndices_of_notMem _ _ hy, κd.2.1, κd.2.2.1⟩
    convert bWN_twist A pstar hcan hel htc hcc ψ κ con c0.U _ (stw_paired_of_free (A.family.placement pstar) hT hFree)
      using 2
    exact congrArg _ (VineEstS5B2.decEquiv_val (A.family.placement pstar) hT κ.L κ.base ![κ.e, κ.f, κ.g, κ.h] κd)
  have he := congrArg
    (fun (f : CLLocalDecoration (botR A c0) κ.L κ.base ![κ.e, κ.f, κ.g, κ.h] →
        CLInternalTime (botR A c0) → ℂ) =>
      (coupling d κ.L κ.γ κ.δ : ℂ) ^ clLocalOrder1 (botR A c0) * clLocalZeta (botR A c0) *
      ∑' kd, ∫ τ, bWN ψ κ A c0.U (clExtendIndices (botR A c0) kd.1) *
        (lowModC (botR A c0) lam ![κ.t0, κ.t1, κ.t2] τ * f kd τ))
    (funext fun kd => funext fun τ => hpt kd τ)
  simp only [mul_neg, integral_neg, tsum_neg] at he
  exact he.symm

end Ops

theorem memberB_bottom_eq (κ : KPar d) (lam : ℝ) (ψ : WD d)
    (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
    (hA : IsPrimeGarden A.skeleton) (hb0 : c0.b = (A.family.placement pstar).lower)
    (hup : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j))
    {z : ClassMember w ι} (hz : z ∈ canonFinsetK p kind A c0) :
    memberB κ lam ψ z.1 z.2 = weightedBotKernelB κ lam ψ A c0 pstar z.1 := by
  obtain ⟨Z,cZ⟩ := z
  have hr := (mem_canonFinset_iff_bottom hA hup).mp hz
  rcases reach_single hr with he | ⟨op,he⟩
  · rw [he]
    exact memberB_skip_eq κ lam ψ A c0 hb0
  · rw [he]
    obtain ⟨hcan,hel,htc,hcc,ε,con⟩ := op
    cases ε
    · exact memberB_false_eq κ lam ψ A c0 hcan hel htc hcc hb0 con
    · exact memberB_true_eq κ lam ψ A c0 hcan hel htc hcc hb0 con

/-- **Weighted FLAT-MOD at an operative bottom vine**, including momentum-sum convergence. -/
theorem sum_memberB_bottom_eq_flat (κ : KPar d) (lam : ℝ) (ψ : WD d) (C : ℝ) (hC : 0 ≤ C)
    (hψ : ∀ q q' k, ‖ψ.ψ q q' k‖ ≤ C)
    (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
    (hA : IsPrimeGarden A.skeleton) (hb0 : c0.b = (A.family.placement pstar).lower)
    (hup : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j))
    (hL : κ.L ≠ 0) (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|) :
    (∑ z ∈ canonFinsetK p kind A c0, memberB κ lam ψ z.1 z.2) =
      (coupling d κ.L κ.γ κ.δ : ℂ) ^ clLocalOrder1 (botR A c0) * clLocalZeta (botR A c0) *
        lkRaw (botR A c0) κ.L κ.base
          (spatialMul (bWN ψ κ A c0.U) (modPsi c0.b lam (psiBot p kind κ A c0 pstar)))
          ![κ.t0, κ.t1, κ.t2] ![κ.e, κ.f, κ.g, κ.h] := by
  have hz := fun z (hz : z ∈ canonFinsetK p kind A c0) =>
    (botGoalM_of_mem (p := p) (kind := kind) κ lam A c0 hA hb0 hup hL hF hz).2
  rw [sum_congr rfl (fun z hz => memberB_bottom_eq κ lam ψ A c0 hA hb0 hup hz)]
  simp only [weightedBotKernelB]
  rw [← mul_sum]
  congr 1
  rw [← Summable.tsum_finsetSum (fun z hz' => summable_weighted_integrals volume _
    (hz z hz').2 (fun kd => bWN ψ κ A c0.U (clExtendIndices (botR A c0) kd.1))
    (bWNB ψ A c0.U C) (bWNB_nonneg _ _ _ hC) (fun kd => norm_bWN_le ψ κ A c0.U C hψ _))]
  unfold lkRaw spatialMul modPsi
  apply tsum_congr
  intro kd
  rw [← integral_finsetSum _ (fun z hz' => ((hz z hz').1 kd).const_mul _)]
  apply integral_congr_ae
  filter_upwards [] with τ
  rw [← mul_sum, ← mul_sum]
  rfl

end WaveTurbulence.Flower.V5WB
