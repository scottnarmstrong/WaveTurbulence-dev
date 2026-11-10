/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.V5WB.B.Member

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Rg4Time
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Tw10Final
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Rg5SSum
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp11Lin
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp1Geom
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Class
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Op1Step
public import WaveTurbulence.Foundations.VineEst.VineEstS5B.Sum
public import WaveTurbulence.Foundations.VineEst.VineEstS5B.Same
public import WaveTurbulence.Foundations.VineEst.VineEstS5B.Low
public import WaveTurbulence.Foundations.Flower.V5WB.K.WeightedBundle
public import WaveTurbulence.Foundations.VineEst.RowSel.SelDataLF
public import WaveTurbulence.Foundations.VineEst.RowSel.RowDataLF
public import WaveTurbulence.Foundations.VineEst.RowSel.RowTransport

/-! # V5-SPACE-EXT: the S-side with an arbitrary spatial weight of the upper block

`sSumW m`: the S-side of the factorized kernel with the weight `m` inside each spatial sum and outside all coherent
rows. Every transport lemma of the upper-node S-side (`VineSpaceK.WeightedSSum/SSame/STwist/SLin/SLF/SOp`) holds
for an arbitrary weight, given the corresponding covariance of `m` as a hypothesis (rigid transport, same chart,
twist at the lower joint). Proofs follow the upper-node versions, with the weight lemma replaced by the hypothesis. -/

/-! Copied by source (V5W-B-WORLD) from V5W-A's port `Flower/V5WA/VineSpaceB/SSum.lean` (see `COPIED-SHA256SUMS`): namespace `WaveTurbulence.Flower.V5WB`, every row selector (`variable [RowSel]`), the bond weight `bW` replaced by the masked, normalized `bWN` (`ψ : WD d`, bound `bWNB`). -/

public section
namespace WaveTurbulence.Flower.V5WB
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.Reg
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory VineEstS4 VineEstS5B

/-- The S-side of the factorized kernel with an arbitrary weight `m` and lower factor `Φ`. -/
@[expose] noncomputable def sSumW {w d : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (m : (GNode G.tree → Fin d → ℤ) → ℂ) (RS : CLRegionData G S a b) (D : ReconstructionData G) (hG : G.IsPlain)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (t0 t1 t2 : ℝ)
    (e f : Mom d) (n0 n1 : GNode G.tree) (Φ : ℝ → Mom d → Mom d → ℂ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ clLocalOrder1 RS * clLocalZeta RS *
    ∑' xS : ExtS RS L base e f, ∫ σ : CLInternalTime RS,
      m xS.1 * (spart D hG L γ δ F layer hLayer base S a b xS.1 (clLocalClock RS ![t0, t1, t2] σ) *
        Φ (clLocalClock RS ![t0, t1, t2] σ b) (base + latticePoint L (xS.1 n0)) (base + latticePoint L (xS.1 n1)))

section Rigid
variable {w d : ℕ} {G : Garden w} (P : CorePlacement G) {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  (hS : G.molecule.IsBlock S a b) (hR : RigidAt P S b) (RS : CLRegionData G S a b)
  (RS' : CLRegionData (unitTwistGarden G P) (twistedAtoms G P S) (eB P a) (eB P b))
  (hG : G.IsPlain) (D : ReconstructionData G) (D' : ReconstructionData (unitTwistGarden G P))
  (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer)
  (layer' : GNode (D'.forest (unitTwistGarden_plain G P hG)) → ℕ)
  (hLayer' : IsLayering (D'.garden (unitTwistGarden_plain G P hG)) layer') (base : Mom d)
  (hC : ∀ p ∈ clRegionalPairs hG S, nativeCoupleLayered D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) =
      nativeCoupleLayered D hG layer hLayer p)
  (hT : ∀ v ∈ S.erase a, nativeChainLayered D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
      nativeChainLayered D hG layer hLayer v)
  (hl : ∀ v ∈ S.erase a, layer' (D'.coreBranch (unitTwistGarden_plain G P hG) (eB P v)).toNode =
      layer (D.coreBranch hG v).toNode)
  (hCi : ∀ p ∈ clRegionalPairs hG S, Flower.V5W.coupleIncoh D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) =
      Flower.V5W.coupleIncoh D hG layer hLayer p)
  (hTi : ∀ v ∈ S.erase a, Flower.V5W.treeIncoh D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
      Flower.V5W.treeIncoh D hG layer hLayer v)
  (hlS : ∀ v ∈ S, layer' (D'.coreBranch (unitTwistGarden_plain G P hG) (eB P v)).toNode =
      layer (D.coreBranch hG v).toNode)

include hS hR hC hT hl hCi hTi hlS in
/-- **The weighted S-side is invariant under a rigid twist**, given the rigid covariance of the weight. -/
theorem sSumW_rigid (m : (GNode G.tree → Fin d → ℤ) → ℂ) (m' : (GNode (unitTwistGarden G P).tree → Fin d → ℤ) → ℂ)
    (hm : ∀ x', m' x' = m (fun y => x' (naiveNodeEquiv G P y)))
    (t0 t1 t2 : ℝ) (e f : Mom d) (n0 n1 : GNode G.tree) (Φ : ℝ → Mom d → Mom d → ℂ) :
    sSumW m' RS' D' (unitTwistGarden_plain G P hG) L γ δ F layer' hLayer' base t0 t1 t2 e f
        (naiveNodeEquiv G P n0) (naiveNodeEquiv G P n1) Φ =
      sSumW m RS D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 Φ := by
  unfold sSumW
  rw [order1_rigid P RS RS', zeta_rigid P RS RS' hR]
  congr 1
  rw [← (extSEquiv P RS RS' L base e f hS hR).tsum_eq]
  refine tsum_congr fun xS' => ?_
  rw [← (tEquivS_measurePreserving P RS RS').integral_comp'
    (g := fun σ' => m' xS'.1 *
      (spart D' (unitTwistGarden_plain G P hG) L γ δ F layer' hLayer' base (twistedAtoms G P S) (eB P a)
      (eB P b) xS'.1 (clLocalClock RS' ![t0, t1, t2] σ') *
        Φ (clLocalClock RS' ![t0, t1, t2] σ' (eB P b)) (base + latticePoint L (xS'.1 (naiveNodeEquiv G P n0)))
          (base + latticePoint L (xS'.1 (naiveNodeEquiv G P n1)))))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  have hu : ∀ v ∈ S, clLocalClock RS' ![t0, t1, t2] (tEquivS P RS RS' τ) (eB P v) = clLocalClock RS ![t0, t1, t2] τ v :=
    fun v hv => clockS_corr P RS RS' _ τ hv
  have hsp := spart_rigid P hS hR hG D D' L γ δ F layer hLayer layer' hLayer' base hC hT hCi hTi hlS RS xS'.1
    (clLocalClock RS' ![t0, t1, t2] (tEquivS P RS RS' τ)) (clLocalClock RS ![t0, t1, t2] τ) hu hl
  change m' xS'.1 * (_ * _) = m (fun y => xS'.1 (naiveNodeEquiv G P y)) * (_ * _)
  rw [hm, hsp, hu b hS.2.2.1]
  rfl

end Rigid

section LF
variable {w : ℕ} {p : ℕ} {kind : Bool} {LG : LayeredGarden w} (s : LFSource p kind LG)

/-- **Weighted S-side invariance for a TRUE-choice LF construction at a member below the split.** -/
theorem sSumW_rigid_LF {d : ℕ} (m : (GNode s.skeleton.tree → Fin d → ℤ) → ℂ)
    (m' : (GNode (unitTwistGarden s.skeleton s.placement).tree → Fin d → ℤ) → ℂ)
    (hm : ∀ x', m' x' = m (fun y => x' (naiveNodeEquiv s.skeleton s.placement y)))
    (h : LFConstruction s true) {S : Finset (GBranch s.skeleton.tree)} {a b : GBranch s.skeleton.tree}
    (hS : s.skeleton.molecule.IsBlock S a b) (hR : RigidAt s.placement S b) (RS : CLRegionData s.skeleton S a b)
    (RS' : CLRegionData (unitTwistGarden s.skeleton s.placement) (twistedAtoms s.skeleton s.placement S)
      (eB s.placement a) (eB s.placement b))
    (layer : GNode (s.data.forest s.plain) → ℕ) (hLayer : IsLayering (s.data.garden s.plain) layer)
    (hspec : layeredReconstruction s.data s.plain layer hLayer = LG)
    (layer' : GNode (h.data.forest (s.chosen_plain true)) → ℕ)
    (hLayer' : IsLayering (h.data.garden (s.chosen_plain true)) layer')
    (hspec' : layeredReconstruction h.data (s.chosen_plain true) layer' hLayer' = h.output)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (t0 t1 t2 : ℝ) (e f : Mom d) (n0 n1 : GNode s.skeleton.tree)
    (Φ : ℝ → Mom d → Mom d → ℂ) :
    sSumW m' RS' h.data (s.chosen_plain true) L γ δ F layer' hLayer' base t0 t1 t2 e f
        (naiveNodeEquiv s.skeleton s.placement n0) (naiveNodeEquiv s.skeleton s.placement n1) Φ =
      sSumW m RS s.data s.plain L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 Φ := by
  refine sSumW_rigid s.placement hS hR RS RS' s.plain s.data h.data L γ δ F layer hLayer layer' hLayer' base ?_ ?_ ?_
    ?_ ?_ ?_ m m' hm t0 t1 t2 e f n0 n1 Φ
  · intro q hq
    have hint := (mem_clRegionalPairs s.skeleton).mp hq
    have hne : q ≠ s.exceptional := by
      intro hqe
      have hqe' : q = pairOfLeaf s.skeleton s.plain s.placement.retained := hqe
      subst hqe'
      rcases pairOfLeaf_first_or_partner s.skeleton s.plain s.placement.retained with hq' | hq'
      · exact not_internal_retained_of s.placement hR.lower_notMem (hq' ▸ hint)
      · exact not_internal_pair_of s.placement hR.lower_notMem (hq' ▸ hint)
    exact native_couple_eq h layer hLayer hspec layer' hLayer' hspec' q hne
  · intro v hv
    exact native_tree_eq h layer hLayer hspec layer' hLayer' hspec' v (hR.ne_lower (Finset.mem_of_mem_erase hv))
  · intro v _
    exact coreLayer_eq h layer hLayer hspec layer' hLayer' hspec' v
  · intro q hq
    have hint := (mem_clRegionalPairs s.skeleton).mp hq
    have hne : q ≠ s.exceptional := by
      intro hqe
      have hqe' : q = pairOfLeaf s.skeleton s.plain s.placement.retained := hqe
      subst hqe'
      rcases pairOfLeaf_first_or_partner s.skeleton s.plain s.placement.retained with hq' | hq'
      · exact not_internal_retained_of s.placement hR.lower_notMem (hq' ▸ hint)
      · exact not_internal_pair_of s.placement hR.lower_notMem (hq' ▸ hint)
    exact Flower.V5W.coupleIncoh_LF h layer hLayer hspec layer' hLayer' hspec' q hne
  · intro v hv
    exact Flower.V5W.treeIncoh_LF h layer hLayer hspec layer' hLayer' hspec' v (hR.ne_lower (Finset.mem_of_mem_erase hv))
  · intro v _
    exact coreLayer_eq h layer hLayer hspec layer' hLayer' hspec' v

/-- **Weighted S-side invariance for a FALSE-choice LF construction** (same skeleton and region). -/
theorem sSumW_false_LF {d : ℕ} (m : (GNode s.skeleton.tree → Fin d → ℤ) → ℂ)
    (h : LFConstruction s false) {S : Finset (GBranch s.skeleton.tree)} {a b : GBranch s.skeleton.tree}
    (hlow : s.placement.lower ∉ S) (RS : CLRegionData s.skeleton S a b)
    (layer : GNode (s.data.forest s.plain) → ℕ) (hLayer : IsLayering (s.data.garden s.plain) layer)
    (hspec : layeredReconstruction s.data s.plain layer hLayer = LG)
    (layer' : GNode (h.data.forest (s.chosen_plain false)) → ℕ)
    (hLayer' : IsLayering (h.data.garden (s.chosen_plain false)) layer')
    (hspec' : layeredReconstruction h.data (s.chosen_plain false) layer' hLayer' = h.output)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (t0 t1 t2 : ℝ) (e f : Mom d) (n0 n1 : GNode s.skeleton.tree)
    (Φ : ℝ → Mom d → Mom d → ℂ) :
    sSumW m RS h.data (s.chosen_plain false) L γ δ F layer' hLayer' base t0 t1 t2 e f n0 n1 Φ =
      sSumW m RS s.data s.plain L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 Φ := by
  unfold sSumW
  congr 1
  refine tsum_congr fun xS => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
  have hsp := spart_congr_data (a := a) (S := S) s.plain h.data s.data L γ δ F layer' hLayer' layer hLayer base ?_ ?_ ?_ ?_ ?_ ?_ ?_ b
    xS.1 (clLocalClock RS ![t0, t1, t2] σ)
  · simp only []
    rw [hsp]
  · intro q hq
    have hint := (mem_clRegionalPairs s.skeleton).mp hq
    have hne : q ≠ s.exceptional := by
      intro hqe
      have hqe' : q = pairOfLeaf s.skeleton s.plain s.placement.retained := hqe
      subst hqe'
      rcases pairOfLeaf_first_or_partner s.skeleton s.plain s.placement.retained with hq' | hq'
      · exact not_internal_retained_of s.placement hlow (hq' ▸ hint)
      · exact not_internal_pair_of s.placement hlow (hq' ▸ hint)
    have := native_couple_eq h layer hLayer hspec layer' hLayer' hspec' q hne
    have hp : s.pairs false q = q := pairOfLeaf_firstLeaf s.skeleton s.plain q
    rwa [hp] at this
  · intro v hv
    exact native_tree_eq h layer hLayer hspec layer' hLayer' hspec' v (fun e => hlow (e ▸ (Finset.mem_of_mem_erase hv)))
  · intro v _
    exact coreLayer_eq h layer hLayer hspec layer' hLayer' hspec' v
  · intro q hq
    have hint := (mem_clRegionalPairs s.skeleton).mp hq
    have hne : q ≠ s.exceptional := by
      intro hqe
      have hqe' : q = pairOfLeaf s.skeleton s.plain s.placement.retained := hqe
      subst hqe'
      rcases pairOfLeaf_first_or_partner s.skeleton s.plain s.placement.retained with hq' | hq'
      · exact not_internal_retained_of s.placement hlow (hq' ▸ hint)
      · exact not_internal_pair_of s.placement hlow (hq' ▸ hint)
    have := Flower.V5W.coupleIncoh_LF h layer hLayer hspec layer' hLayer' hspec' q hne
    have hp : s.pairs false q = q := pairOfLeaf_firstLeaf s.skeleton s.plain q
    rwa [hp] at this
  · intro v hv
    exact Flower.V5W.treeIncoh_LF h layer hLayer hspec layer' hLayer' hspec' v
      (fun e => hlow (e ▸ (Finset.mem_of_mem_erase hv)))
  · intro pp q _ i
    exact VineEst.coupleRootParents_congr_all s.plain h.data s.data layer' hLayer' layer hLayer
      (fun v => coreLayer_eq h layer hLayer hspec layer' hLayer' hspec' v) pp q i
  · intro pp v _
    exact VineEst.treeRootParent_congr_all s.plain h.data s.data layer' hLayer' layer hLayer
      (fun v => coreLayer_eq h layer hLayer hspec layer' hLayer' hspec' v) pp v

end LF

section Same
variable {w d : ℕ} {G : Garden w} (hG : G.IsPlain) (D1 D2 : ReconstructionData G) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer1 : GNode (D1.forest hG) → ℕ) (hLayer1 : IsLayering (D1.garden hG) layer1)
  (layer2 : GNode (D2.forest hG) → ℕ) (hLayer2 : IsLayering (D2.garden hG) layer2) (base : Mom d)
  {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} (p0 : SourcePair G)
  (RS : CLRegionData G S a b) (t0 t1 t2 : ℝ) (e f : Mom d) (n0 n1 : GNode G.tree)
  (Φ : ℝ → Mom d → Mom d → ℂ)

theorem sSumW_same (m : (GNode G.tree → Fin d → ℤ) → ℂ) (hb : b ∈ S.erase a) (hp0 : p0 ∈ clRegionalPairs hG S)
    (hC : ∀ p ∈ (clRegionalPairs hG S).erase p0, nativeCoupleLayered D1 hG layer1 hLayer1 p =
      nativeCoupleLayered D2 hG layer2 hLayer2 p)
    (hT : ∀ v ∈ (S.erase a).erase b, nativeChainLayered D1 hG layer1 hLayer1 v = nativeChainLayered D2 hG layer2 hLayer2 v)
    (hl : ∀ v ∈ S.erase a, layer1 (D1.coreBranch hG v).toNode = layer2 (D2.coreBranch hG v).toNode)
    (hsel : VineEst.SelDataEq hG D1 D2 layer1 hLayer1 layer2 hLayer2 ((clRegionalPairs hG S).erase p0)
      ((S.erase a).erase b)) :
    sSumW m RS D2 hG L γ δ F layer2 hLayer2 base t0 t1 t2 e f n0 n1 Φ =
      (coupling d L γ δ : ℂ) ^ clLocalOrder1 RS * clLocalZeta RS *
        ∑' x : ExtS RS L base e f, ∫ σ : CLInternalTime RS,
          m x.1 * sameInt hG D1 D2 L γ δ F layer1 hLayer1 layer2 hLayer2 base p0 RS t0 t1 t2 e f n0 n1 Φ x σ := by
  unfold sSumW
  congr 1
  refine tsum_congr fun x => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
  exact congrArg (m x.1 * ·)
    (sInt_same hG D1 D2 L γ δ F layer1 hLayer1 layer2 hLayer2 base p0 RS
      t0 t1 t2 e f n0 n1 Φ hb hp0 hC hT hl hsel x σ)

end Same

section Tw
variable {w : ℕ} {G : Garden w} {P : CorePlacement G} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  {RS : CLRegionData G S a b}
  {RS' : CLRegionData (unitTwistGarden G P) (twistedAtoms G P S) (eB P a) (eB P b)} (h : STw P RS RS')
  {d : ℕ} (hG : G.IsPlain) (D : ReconstructionData G) (D' : ReconstructionData (unitTwistGarden G P))
  (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer)
  (layer' : GNode (D'.forest (unitTwistGarden_plain G P hG)) → ℕ)
  (hLayer' : IsLayering (D'.garden (unitTwistGarden_plain G P hG)) layer') (base : Mom d)
  (t0 t1 t2 : ℝ) (e f : Mom d) (Φ' : ℝ → Mom d → Mom d → ℂ)
  (hC : ∀ p ∈ clRegionalPairs hG S, p ≠ pairOfLeaf G hG P.retained →
    nativeCoupleLayered D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) =
      nativeCoupleLayered D hG layer hLayer p)
  (hT : ∀ v ∈ S.erase a, v ≠ b →
    nativeChainLayered D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
      nativeChainLayered D hG layer hLayer v)
  (hl : ∀ v ∈ S.erase a, layer' (D'.coreBranch (unitTwistGarden_plain G P hG) (eB P v)).toNode =
    layer (D.coreBranch hG v).toNode)
  (hCi : ∀ p ∈ clRegionalPairs hG S, p ≠ pairOfLeaf G hG P.retained →
    Flower.V5W.coupleIncoh D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) =
      Flower.V5W.coupleIncoh D hG layer hLayer p)
  (hTi : ∀ v ∈ S.erase a, v ≠ b →
    Flower.V5W.treeIncoh D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
      Flower.V5W.treeIncoh D hG layer hLayer v)
  (hlS : ∀ v ∈ S, layer' (D'.coreBranch (unitTwistGarden_plain G P hG) (eB P v)).toNode =
    layer (D.coreBranch hG v).toNode)

include h hC hT hl hCi hTi hlS in
/-- **The weighted S-side of a twist at the lower joint**, given the twist covariance of the weight. -/
theorem sSumW_tw (m : (GNode G.tree → Fin d → ℤ) → ℂ) (m' : (GNode (unitTwistGarden G P).tree → Fin d → ℤ) → ℂ)
    (hm : ∀ x : GNode G.tree → Fin d → ℤ, PairedAt P x → m' (twistNodeLabels G P x) = m x) :
    sSumW m' RS' D' (unitTwistGarden_plain G P hG) L γ δ F layer' hLayer' base t0 t1 t2 e f (eB P b).toNode
        ((eB P b).child RS'.kept) Φ' =
      -((coupling d L γ δ : ℂ) ^ clLocalOrder1 RS * clLocalZeta RS *
        ∑' x : ExtS RS L base e f, ∫ σ : CLInternalTime RS,
          m x.1 * twInt (RS' := RS') hG D D' L γ δ F layer hLayer layer' hLayer' base t0 t1 t2 e f Φ' x σ) := by
  unfold sSumW
  rw [order1_rigid P RS RS', h.zeta]
  suffices key : (∑' x : ExtS RS' L base e f, ∫ σ : CLInternalTime RS',
      m' x.1 *
        sInt RS' D' (unitTwistGarden_plain G P hG) L γ δ F layer' hLayer' base t0 t1 t2 e f
          (eB P b).toNode ((eB P b).child RS'.kept) Φ' x σ) =
      ∑' x : ExtS RS L base e f, ∫ σ : CLInternalTime RS,
        m x.1 *
          twInt (RS' := RS') hG D D' L γ δ F layer hLayer layer' hLayer' base t0 t1 t2 e f Φ' x σ by
    change _ * _ * (∑' x, ∫ σ, m' x.1 *
      sInt RS' D' (unitTwistGarden_plain G P hG) L γ δ F layer' hLayer' base t0 t1 t2 e f
        (eB P b).toNode ((eB P b).child RS'.kept) Φ' x σ) = _
    rw [key]
    ring
  rw [← (h.extEquiv L base e f).tsum_eq]
  refine tsum_congr fun x => ?_
  rw [← (tEquivS_measurePreserving P RS RS').integral_comp'
    (g := fun σ' => m' (h.extEquiv L base e f x).1 *
      sInt RS' D' (unitTwistGarden_plain G P hG) L γ δ F layer' hLayer' base t0 t1 t2 e f
        (eB P b).toNode ((eB P b).child RS'.kept) Φ' (h.extEquiv L base e f x) σ')]
  apply integral_congr_ae
  filter_upwards [] with σ
  have hw : m' (h.extEquiv L base e f x).1 = m x.1 := by
    rw [h.extEquiv_val]
    exact hm x.1 (h.pairedAt_ext x)
  rw [hw, sInt_tw h hG D D' L γ δ F layer hLayer layer' hLayer' base t0 t1 t2 e f Φ' hC hT hl hCi hTi hlS x σ]

end Tw

section LFTw
variable {w : ℕ} {p : ℕ} {kind : Bool} {LG : LayeredGarden w} (s : LFSource p kind LG)

theorem sSumW_twLF (h : LFConstruction s true) {S : Finset (GBranch s.skeleton.tree)} {a b : GBranch s.skeleton.tree}
    (RS : CLRegionData s.skeleton S a b)
    (RS' : CLRegionData (unitTwistGarden s.skeleton s.placement) (twistedAtoms s.skeleton s.placement S)
      (eB s.placement a) (eB s.placement b))
    (hS : STw s.placement RS RS')
    (layer : GNode (s.data.forest s.plain) → ℕ) (hLayer : IsLayering (s.data.garden s.plain) layer)
    (hspec : layeredReconstruction s.data s.plain layer hLayer = LG)
    (layer' : GNode (h.data.forest (s.chosen_plain true)) → ℕ)
    (hLayer' : IsLayering (h.data.garden (s.chosen_plain true)) layer')
    (hspec' : layeredReconstruction h.data (s.chosen_plain true) layer' hLayer' = h.output)
    {d : ℕ} (m : (GNode s.skeleton.tree → Fin d → ℤ) → ℂ)
    (m' : (GNode (unitTwistGarden s.skeleton s.placement).tree → Fin d → ℤ) → ℂ)
    (hm : ∀ x : GNode s.skeleton.tree → Fin d → ℤ, PairedAt s.placement x →
      m' (twistNodeLabels s.skeleton s.placement x) = m x)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (t0 t1 t2 : ℝ) (e f : Mom d)
    (Φ' : ℝ → Mom d → Mom d → ℂ) :
    sSumW m' RS' h.data (s.chosen_plain true) L γ δ F layer' hLayer' base t0 t1 t2 e f (eB s.placement b).toNode
        ((eB s.placement b).child RS'.kept) Φ' =
      -((coupling d L γ δ : ℂ) ^ clLocalOrder1 RS * clLocalZeta RS *
        ∑' x : ExtS RS L base e f, ∫ σ : CLInternalTime RS,
          m x.1 * twInt (RS' := RS') s.plain s.data h.data L γ δ F layer hLayer layer' hLayer' base t0 t1 t2 e f Φ' x σ) := by
  refine sSumW_tw hS s.plain s.data h.data L γ δ F layer hLayer layer' hLayer' base t0 t1 t2 e f Φ' ?_ ?_ ?_ ?_ ?_ ?_
    m m' hm
  · intro q _ hq
    exact native_couple_eq h layer hLayer hspec layer' hLayer' hspec' q hq
  · intro v _ hv
    exact native_tree_eq h layer hLayer hspec layer' hLayer' hspec' v (hS.lower ▸ hv)
  · intro v _
    exact coreLayer_eq h layer hLayer hspec layer' hLayer' hspec' v
  · intro q _ hq
    exact Flower.V5W.coupleIncoh_LF h layer hLayer hspec layer' hLayer' hspec' q hq
  · intro v _ hv
    exact Flower.V5W.treeIncoh_LF h layer hLayer hspec layer' hLayer' hspec' v (hS.lower ▸ hv)
  · intro v _
    exact coreLayer_eq h layer hLayer hspec layer' hLayer' hspec' v

theorem sSumW_falseLF (h : LFConstruction s false) {S : Finset (GBranch s.skeleton.tree)} {a b : GBranch s.skeleton.tree}
    (RS : CLRegionData s.skeleton S a b) (hS : SLow s.placement RS)
    (layer : GNode (s.data.forest s.plain) → ℕ) (hLayer : IsLayering (s.data.garden s.plain) layer)
    (hspec : layeredReconstruction s.data s.plain layer hLayer = LG)
    (layer' : GNode (h.data.forest (s.chosen_plain false)) → ℕ)
    (hLayer' : IsLayering (h.data.garden (s.chosen_plain false)) layer')
    (hspec' : layeredReconstruction h.data (s.chosen_plain false) layer' hLayer' = h.output)
    {d : ℕ} (m : (GNode s.skeleton.tree → Fin d → ℤ) → ℂ) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d)
    (t0 t1 t2 : ℝ) (e f : Mom d) (n0 n1 : GNode s.skeleton.tree) (Φ : ℝ → Mom d → Mom d → ℂ) :
    sSumW m RS h.data (s.chosen_plain false) L γ δ F layer' hLayer' base t0 t1 t2 e f n0 n1 Φ =
      (coupling d L γ δ : ℂ) ^ clLocalOrder1 RS * clLocalZeta RS *
        ∑' x : ExtS RS L base e f, ∫ σ : CLInternalTime RS,
          m x.1 * sameInt s.plain s.data h.data L γ δ F layer hLayer layer' hLayer' base
            (pairOfLeaf s.skeleton s.plain s.placement.retained) RS t0 t1 t2 e f n0 n1 Φ x σ := by
  refine sSumW_same s.plain s.data h.data L γ δ F layer hLayer layer' hLayer' base
    (pairOfLeaf s.skeleton s.plain s.placement.retained) RS t0 t1 t2 e f n0 n1 Φ m hS.b_mem_erase hS.p0_mem ?_ ?_ ?_
    (VineEst.selDataEq_LF_false h layer hLayer hspec layer' hLayer' hspec' _ _ (fun q hq => (Finset.mem_erase.mp hq).1)
      (fun v hv => hS.lower ▸ (Finset.mem_erase.mp hv).1)).symm
  · intro q hq
    obtain ⟨hq0, _⟩ := Finset.mem_erase.mp hq
    have := native_couple_eq h layer hLayer hspec layer' hLayer' hspec' q hq0
    have hp : s.pairs false q = q := pairOfLeaf_firstLeaf s.skeleton s.plain q
    rw [hp] at this
    exact this.symm
  · intro v hv
    exact (native_tree_eq h layer hLayer hspec layer' hLayer' hspec' v (hS.lower ▸ (Finset.mem_erase.mp hv).1)).symm
  · intro v _
    exact (coreLayer_eq h layer hLayer hspec layer' hLayer' hspec' v).symm

end LFTw

section Lin
variable {w d : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- Finite linearity of the weighted S sum, from the original absolute majorants and a weight bound. -/
theorem sSumW_finsetSum (m : (GNode G.tree → Fin d → ℤ) → ℂ) (RS : CLRegionData G S a b)
    (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer)
    (base : Mom d) (t0 t1 t2 : ℝ) (e f : Mom d) (n0 n1 : GNode G.tree)
    {β : Type*} (s : Finset β) (Φ : β → ℝ → Mom d → Mom d → ℂ)
    (h : ∀ i ∈ s, SOK RS D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 (Φ i))
    (M : ℝ) (hM : 0 ≤ M) (hm : ∀ x, ‖m x‖ ≤ M) :
    sSumW m RS D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1
      (fun t E F' => ∑ i ∈ s, Φ i t E F') =
    ∑ i ∈ s, sSumW m RS D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 (Φ i) := by
  classical
  unfold sSumW
  rw [← Finset.mul_sum]
  congr 1
  have hsum := fun i hi => summable_weighted_integrals volume _ (h i hi).2
    (fun x => m x.val) M hM (fun x => hm _)
  refine Eq.trans ?_ (Summable.tsum_finsetSum hsum)
  apply tsum_congr
  intro x
  refine Eq.trans ?_ (integral_finsetSum _ (fun i hi =>
    ((h i hi).1 x).const_mul (m x.val)))
  apply integral_congr_ae
  filter_upwards [] with σ
  simp only [Finset.mul_sum]

end Lin

end WaveTurbulence.Flower.V5WB
