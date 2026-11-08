/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceB.Split
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceB.Weight
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.Canon
public import WaveTurbulence.Foundations.Molecule.TwistParents
public import WaveTurbulence.Foundations.VineEst.RowSel.RowDataLF

/-! # V5-SPACE-EXT: the weighted lower kernel of a split state

`kTB κ lam ψ X sx`: the modulated member kernel of the lower block of the split `sx`, weighted by the bond weight of
the lower block. Under a TRUE operation at `p*` it is the source kernel with the first two boundary momenta exchanged
(the bond weight of the lower block reads neither exchanged label: neither exceptional bond is a bond of the lower
block), under a FALSE operation it is unchanged (same chart, same core layers). Hence the fibre relation `kTB_rel`
and the common lower factor `ktildeB`, exactly as `FlatMod.kTM`/`kTM_rel`/`ktildeM` for the unweighted kernel. -/

@[expose] public section
namespace WaveTurbulence.VineSpaceB
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.Reg
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS5C.FlatMod VineSpaceK TTree MeasureTheory

section Kernel
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem memberMX_idx {U U' : Finset (GBranch G.tree)} {a a' b b' : GBranch G.tree}
    (hU : U = U') (ha : a = a') (hb : b = b') (R : CLRegionData G U a b) (R' : CLRegionData G U' a' b')
    (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (lam : ℝ) (m : (GNode G.tree → Fin d → ℤ) → ℂ)
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    memberMX D hG R L γ δ F layer hLayer base lam m t0 t1 t2 e f g h =
      memberMX D hG R' L γ δ F layer hLayer base lam m t0 t1 t2 e f g h := by
  subst hU ha hb
  rw [regionData_subsingleton R R']

theorem memberMX_congr_data (R : CLRegionData G U a b) (hG : G.IsPlain) (D1 D2 : ReconstructionData G) (L γ δ : ℝ)
    (F : ℕ → Mom d → ℝ) (layer1 : GNode (D1.forest hG) → ℕ) (hLayer1 : IsLayering (D1.garden hG) layer1)
    (layer2 : GNode (D2.forest hG) → ℕ) (hLayer2 : IsLayering (D2.garden hG) layer2) (base : Mom d) (lam : ℝ)
    (m : (GNode G.tree → Fin d → ℤ) → ℂ)
    (hC : ∀ p ∈ clRegionalPairs hG U, nativeCoupleLayered D1 hG layer1 hLayer1 p = nativeCoupleLayered D2 hG layer2 hLayer2 p)
    (hT : ∀ v ∈ clInteriorBranches R, nativeChainLayered D1 hG layer1 hLayer1 v = nativeChainLayered D2 hG layer2 hLayer2 v)
    (hl : ∀ v ∈ clInteriorBranches R, layer1 (D1.coreBranch hG v).toNode = layer2 (D2.coreBranch hG v).toNode)
    (t0 t1 t2 : ℝ) (e f g k : Mom d) :
    memberMX D1 hG R L γ δ F layer1 hLayer1 base lam m t0 t1 t2 e f g k =
      memberMX D2 hG R L γ δ F layer2 hLayer2 base lam m t0 t1 t2 e f g k := by
  unfold memberMX
  congr 1
  refine tsum_congr fun κ => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  beta_reduce
  congr 2
  unfold clLocalSummand
  have hstar : ∀ (κ' : GNode G.tree → (Fin d → ℤ)) (t' : Fin 3 → ℝ) (τ' : CLInternalTime R),
      clLocalStarProduct D1 hG R L γ δ F layer1 hLayer1 base κ' t' τ' =
        clLocalStarProduct D2 hG R L γ δ F layer2 hLayer2 base κ' t' τ' :=
    fun κ' t' τ' => clLocalStarProduct_congr_data R hG D1 D2 L γ δ F layer1 hLayer1 layer2 hLayer2 base hC hT κ' t' τ'
  simp only [hstar]
  rw [clLocalTimeDomain_congr_data R hG D1 D2 layer1 layer2 hl]

section Twist
variable (P : CorePlacement G) {T : Finset (GBranch G.tree)} {z : GBranch G.tree}
  (hB : G.molecule.IsBlock T P.lower z) (hCL : Mole.CLParentPattern G T P.lower z)
  (R : CLRegionData G T P.lower z) (R' : TwRegion P T z)
  (hG : G.IsPlain) (D : ReconstructionData G) (D' : ReconstructionData (unitTwistGarden G P))
  (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer)
  (layer' : GNode (D'.forest (unitTwistGarden_plain G P hG)) → ℕ)
  (hLayer' : IsLayering (D'.garden (unitTwistGarden_plain G P hG)) layer') (base : Mom d) (lam : ℝ) (t0 t1 t2 : ℝ)
  (e f g h : Mom d)
  (hC : ∀ p ∈ clRegionalPairs hG T, nativeCoupleLayered D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) =
      nativeCoupleLayered D hG layer hLayer p)
  (hT : ∀ v ∈ clInteriorBranches R, nativeChainLayered D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
      nativeChainLayered D hG layer hLayer v)
  (hl : ∀ v ∈ T, layer' (D'.coreBranch (unitTwistGarden_plain G P hG) (eB P v)).toNode =
      layer (D.coreBranch hG v).toNode)
  (hCi : ∀ p ∈ clRegionalPairs hG T, Flower.V5W.coupleIncoh D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) =
      Flower.V5W.coupleIncoh D hG layer hLayer p)
  (hTi : ∀ v ∈ clInteriorBranches R, Flower.V5W.treeIncoh D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
      Flower.V5W.treeIncoh D hG layer hLayer v)

include hB hCL hC hT hl hCi hTi in
/-- **`K^{T,λ}` with a multiplier, twist invariance** under exact decoration covariance of the multiplier
(the proof of `VineSpaceK.memberMX_twist`). -/
theorem memberMX_twistB
    (m : (GNode G.tree → Fin d → ℤ) → ℂ)
    (m' : (GNode (unitTwistGarden G P).tree → Fin d → ℤ) → ℂ)
    (hcov : ∀ κ' : CLLocalDecoration R' L base ![e, f, g, h],
      m' (clExtendIndices R' κ'.1) =
        m (clExtendIndices R (decEquiv P hB hCL R R' L base e f g h κ').1)) :
    memberMX D' (unitTwistGarden_plain G P hG) R' L γ δ F layer' hLayer' base lam m' t0 t1 t2 e f g h =
      memberMX D hG R L γ δ F layer hLayer base lam m t0 t1 t2 f e g h := by
  unfold memberMX
  rw [order1_twist P R R', zeta_twist P R R']
  congr 1
  have hint : ∀ κ' : CLLocalDecoration R' L base ![e, f, g, h],
      ∫ τ' : CLInternalTime R', m' (clExtendIndices R' κ'.1) * (lowModC R' lam ![t0, t1, t2] τ' *
          clLocalSummand D' (unitTwistGarden_plain G P hG) R' L γ δ F layer' hLayer' base
          ![e, f, g, h] ![t0, t1, t2] κ' τ') =
        ∫ τ : CLInternalTime R, m (clExtendIndices R (decEquiv P hB hCL R R' L base e f g h κ').1) *
          (lowModC R lam ![t0, t1, t2] τ *
          clLocalSummand D hG R L γ δ F layer hLayer base ![f, e, g, h] ![t0, t1, t2]
          (decEquiv P hB hCL R R' L base e f g h κ') τ) := by
    intro κ'
    rw [← (tEquiv_measurePreserving P R R').integral_comp' (g := fun τ' =>
      m' (clExtendIndices R' κ'.1) * (lowModC R' lam ![t0, t1, t2] τ' *
        clLocalSummand D' _ R' L γ δ F layer' hLayer' base ![e, f, g, h] ![t0, t1, t2] κ' τ'))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    beta_reduce
    rw [hcov, lowModC_twist P hB R R' lam _ τ]
    rw [summand_twist P hB hCL R R' hG D D' L γ δ F layer hLayer layer' hLayer' base e f g h hC hT hl hCi hTi _ κ' τ]
  rw [tsum_congr hint]
  exact (decEquiv P hB hCL R R' L base e f g h).tsum_eq
    (fun κ => ∫ τ : CLInternalTime R, m (clExtendIndices R κ.1) * (lowModC R lam ![t0, t1, t2] τ *
      clLocalSummand D hG R L γ δ F layer hLayer base ![f, e, g, h] ![t0, t1, t2] κ τ))

end Twist

/-- The parent of the top joint of a CL block is not an atom of the block. -/
theorem parent_lower_notMem (P : CorePlacement G) {T : Finset (GBranch G.tree)} {z : GBranch G.tree}
    (hB : G.molecule.IsBlock T P.lower z) (R : CLRegionData G T P.lower z) :
    GNode.parent P.lower.toNode P.nonroot ∉ T := by
  intro hp
  have hreal := (mem_real_iff hB R _).mp ((branch_mem_clRealizationNodes _).mpr hp)
  exact lower_parent_outside G P hreal.1

/-- The retained LP bond of the twisted member is not a bond of its lower block. -/
theorem retainedLP_notMem (P : CorePlacement G) {T : Finset (GBranch G.tree)} {z : GBranch G.tree}
    (hB : G.molecule.IsBlock T P.lower z) (hCL : Mole.CLParentPattern G T P.lower z) :
    ¬ G.molecule.InGroup T (retainedLP G P) := fun hg =>
  not_internal_retained P hB hCL ⟨P.unmarked, retained_nonroot G P, P.paired_nonroot, hg⟩

end Kernel

section LF
variable {w : ℕ} {p : ℕ} {kind : Bool} {LG : LayeredGarden w} (s : LFSource p kind LG)

/-- **Weighted `K^{T,λ}` twist invariance, TRUE-choice LF construction.** -/
theorem memberMX_twist_LF {d : ℕ} (h : LFConstruction s true) {T : Finset (GBranch s.skeleton.tree)}
    {z : GBranch s.skeleton.tree}
    (hB : s.skeleton.molecule.IsBlock T s.placement.lower z) (hCL : Mole.CLParentPattern s.skeleton T s.placement.lower z)
    (R : CLRegionData s.skeleton T s.placement.lower z) (R' : TwRegion s.placement T z)
    (layer : GNode (s.data.forest s.plain) → ℕ) (hLayer : IsLayering (s.data.garden s.plain) layer)
    (hspec : layeredReconstruction s.data s.plain layer hLayer = LG)
    (layer' : GNode (h.data.forest (s.chosen_plain true)) → ℕ)
    (hLayer' : IsLayering (h.data.garden (s.chosen_plain true)) layer')
    (hspec' : layeredReconstruction h.data (s.chosen_plain true) layer' hLayer' = h.output)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (lam : ℝ)
    (m : (GNode s.skeleton.tree → Fin d → ℤ) → ℂ)
    (m' : (GNode (unitTwistGarden s.skeleton s.placement).tree → Fin d → ℤ) → ℂ) (t0 t1 t2 : ℝ) (e f g k : Mom d)
    (hcov : ∀ κ' : CLLocalDecoration R' L base ![e, f, g, k],
      m' (clExtendIndices R' κ'.1) =
        m (clExtendIndices R (decEquiv s.placement hB hCL R R' L base e f g k κ').1)) :
    memberMX h.data (s.chosen_plain true) R' L γ δ F layer' hLayer' base lam m' t0 t1 t2 e f g k =
      memberMX s.data s.plain R L γ δ F layer hLayer base lam m t0 t1 t2 f e g k := by
  refine memberMX_twistB s.placement hB hCL R R' s.plain s.data h.data L γ δ F layer hLayer layer' hLayer' base lam
    t0 t1 t2 e f g k ?_ ?_ ?_ ?_ ?_ m m' hcov
  · intro q hq
    have hint := (mem_clRegionalPairs s.skeleton).mp hq
    have hne : q ≠ s.exceptional := by
      intro hqe
      have hqe' : q = pairOfLeaf s.skeleton s.plain s.placement.retained := hqe
      subst hqe'
      have hq' := pairOfLeaf_first_or_partner s.skeleton s.plain s.placement.retained
      rcases hq' with hq' | hq'
      · exact not_internal_retained s.placement hB hCL (hq' ▸ hint)
      · exact not_internal_pair s.placement hB hCL (hq' ▸ hint)
    exact native_couple_eq h layer hLayer hspec layer' hLayer' hspec' q hne
  · intro v hv
    have hvl : v ≠ s.placement.lower := (Finset.mem_erase.mp hv).1
    exact native_tree_eq h layer hLayer hspec layer' hLayer' hspec' v hvl
  · intro v _
    exact coreLayer_eq h layer hLayer hspec layer' hLayer' hspec' v
  · intro q hq
    have hint := (mem_clRegionalPairs s.skeleton).mp hq
    have hne : q ≠ s.exceptional := by
      intro hqe
      have hqe' : q = pairOfLeaf s.skeleton s.plain s.placement.retained := hqe
      subst hqe'
      have hq' := pairOfLeaf_first_or_partner s.skeleton s.plain s.placement.retained
      rcases hq' with hq' | hq'
      · exact not_internal_retained s.placement hB hCL (hq' ▸ hint)
      · exact not_internal_pair s.placement hB hCL (hq' ▸ hint)
    exact Flower.V5W.coupleIncoh_LF h layer hLayer hspec layer' hLayer' hspec' q hne
  · intro v hv
    have hvl : v ≠ s.placement.lower := (Finset.mem_erase.mp hv).1
    exact Flower.V5W.treeIncoh_LF h layer hLayer hspec layer' hLayer' hspec' v hvl

/-- **Weighted `K^{T,λ}` invariance, FALSE-choice LF construction** (same multiplier). -/
theorem memberMX_false_LF {d : ℕ} (h : LFConstruction s false) {T : Finset (GBranch s.skeleton.tree)}
    {z : GBranch s.skeleton.tree}
    (hB : s.skeleton.molecule.IsBlock T s.placement.lower z) (hCL : Mole.CLParentPattern s.skeleton T s.placement.lower z)
    (R : CLRegionData s.skeleton T s.placement.lower z)
    (layer : GNode (s.data.forest s.plain) → ℕ) (hLayer : IsLayering (s.data.garden s.plain) layer)
    (hspec : layeredReconstruction s.data s.plain layer hLayer = LG)
    (layer' : GNode (h.data.forest (s.chosen_plain false)) → ℕ)
    (hLayer' : IsLayering (h.data.garden (s.chosen_plain false)) layer')
    (hspec' : layeredReconstruction h.data (s.chosen_plain false) layer' hLayer' = h.output)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (lam : ℝ) (m : (GNode s.skeleton.tree → Fin d → ℤ) → ℂ)
    (t0 t1 t2 : ℝ) (e f g k : Mom d) :
    memberMX h.data (s.chosen_plain false) R L γ δ F layer' hLayer' base lam m t0 t1 t2 e f g k =
      memberMX s.data s.plain R L γ δ F layer hLayer base lam m t0 t1 t2 e f g k := by
  refine memberMX_congr_data R s.plain h.data s.data L γ δ F layer' hLayer' layer hLayer base lam m ?_ ?_ ?_
    t0 t1 t2 e f g k
  · intro q hq
    have hint := (mem_clRegionalPairs s.skeleton).mp hq
    have hne : q ≠ s.exceptional := by
      intro hqe
      have hqe' : q = pairOfLeaf s.skeleton s.plain s.placement.retained := hqe
      subst hqe'
      have hq' := pairOfLeaf_first_or_partner s.skeleton s.plain s.placement.retained
      rcases hq' with hq' | hq'
      · exact not_internal_retained s.placement hB hCL (hq' ▸ hint)
      · exact not_internal_pair s.placement hB hCL (hq' ▸ hint)
    have := native_couple_eq h layer hLayer hspec layer' hLayer' hspec' q hne
    have hp : s.pairs false q = q := pairOfLeaf_firstLeaf s.skeleton s.plain q
    rwa [hp] at this
  · intro v hv
    have hvl : v ≠ s.placement.lower := (Finset.mem_erase.mp hv).1
    exact native_tree_eq h layer hLayer hspec layer' hLayer' hspec' v hvl
  · intro v _
    exact (coreLayer_eq h layer hLayer hspec layer' hLayer' hspec' v)

end LF

section KT
variable {w d : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι} (κ : KPar d) (lam : ℝ)
  (ψ : ℕ → ℕ → Mom d → ℂ) (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J)

/-- **The weighted lower kernel** of a split state. -/
noncomputable def kTB (X : FamilyReconstruction w ι) (sx : SplitAt X.skeleton X.family pstar J) :
    ℝ → Mom d → Mom d → ℂ :=
  fun t E F' =>
    memberMX X.data X.plain sx.RT κ.L κ.γ κ.δ κ.F (stateLayer X) (stateLayer_isLayering X) κ.base lam
      (bW ψ κ X sx.tb.U) t κ.t1 κ.t2 E F' κ.g κ.h

variable (hcan : CanonicalObject p kind A.layered)
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

/-- A TRUE operation at `pstar` exchanges the first two boundary momenta of the weighted lower kernel. -/
theorem kTB_op_true (con : LFConstruction (A.source pstar hcan hel htc hcc) true) (t : ℝ) (E F' : Mom d) :
    kTB κ lam ψ (opOut A pstar hcan hel htc hcc con) (SplitAt.nextA A sp pstar true) t E F' =
      kTB κ lam ψ A sp t F' E := by
  have hb := SplitAt.joint_lower A sp
  unfold kTB
  have key : ∀ {T : Finset (GBranch A.skeleton.tree)} {b z : GBranch A.skeleton.tree}
      (hb : b = (A.family.placement pstar).lower) (hB : A.skeleton.molecule.IsBlock T b z)
      (hCL : Mole.CLParentPattern A.skeleton T b z) (R : CLRegionData A.skeleton T b z)
      (R' : CLRegionData (unitTwistGarden A.skeleton (A.family.placement pstar)) (twistedAtoms A.skeleton (A.family.placement pstar) T)
        (coreBranchEquiv A.skeleton (A.family.placement pstar) b) (coreBranchEquiv A.skeleton (A.family.placement pstar) z)),
      memberMX (opOut A pstar hcan hel htc hcc con).data (opOut A pstar hcan hel htc hcc con).plain
        R' κ.L κ.γ κ.δ κ.F (stateLayer (opOut A pstar hcan hel htc hcc con))
        (stateLayer_isLayering _) κ.base lam
        (bW ψ κ (opOut A pstar hcan hel htc hcc con) (twistedAtoms A.skeleton (A.family.placement pstar) T))
        t κ.t1 κ.t2 E F' κ.g κ.h =
      memberMX A.data A.plain R κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A) κ.base lam (bW ψ κ A T)
        t κ.t1 κ.t2 F' E κ.g κ.h := by
    intro T b z hb hB hCL R R'
    subst hb
    refine memberMX_twist_LF (A.source pstar hcan hel htc hcc) con hB hCL R R' _ _ (stateLayer_spec A) _ _
      (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) κ.L κ.γ κ.δ κ.F κ.base lam _ _ t κ.t1 κ.t2 E F' κ.g κ.h ?_
    intro κ'
    refine (bW_twNode A pstar hcan hel htc hcc ψ κ con (parent_lower_notMem _ hB R) (retainedLP_notMem _ hB hCL)
      (clExtendIndices R' κ'.1)).trans ?_
    congr 1
    funext y
    exact (decEquiv_ext (A.family.placement pstar) hB hCL R R' κ.L κ.base E F' κ.g κ.h κ' y).symm
  exact key hb sp.hT sp.clST.2 sp.RT (SplitAt.nextA A sp pstar true).RT

/-- A FALSE operation at `pstar` leaves the weighted lower kernel unchanged. -/
theorem kTB_op_false (con : LFConstruction (A.source pstar hcan hel htc hcc) false) (t : ℝ) (E F' : Mom d) :
    kTB κ lam ψ (opOut A pstar hcan hel htc hcc con) (SplitAt.nextA A sp pstar false) t E F' =
      kTB κ lam ψ A sp t E F' := by
  have hb := SplitAt.joint_lower A sp
  unfold kTB
  rw [show bW ψ κ (opOut A pstar hcan hel htc hcc con) (SplitAt.nextA A sp pstar false).tb.U = bW ψ κ A sp.tb.U from
    bW_false A pstar hcan hel htc hcc ψ κ con sp.tb.U]
  have key : ∀ {T : Finset (GBranch A.skeleton.tree)} {b z : GBranch A.skeleton.tree}
      (hb : b = (A.family.placement pstar).lower) (hB : A.skeleton.molecule.IsBlock T b z)
      (hCL : Mole.CLParentPattern A.skeleton T b z) (R : CLRegionData A.skeleton T b z),
      memberMX (opOut A pstar hcan hel htc hcc con).data (opOut A pstar hcan hel htc hcc con).plain
        R κ.L κ.γ κ.δ κ.F (stateLayer (opOut A pstar hcan hel htc hcc con))
        (stateLayer_isLayering _) κ.base lam (bW ψ κ A sp.tb.U) t κ.t1 κ.t2 E F' κ.g κ.h =
      memberMX A.data A.plain R κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A) κ.base lam (bW ψ κ A sp.tb.U)
        t κ.t1 κ.t2 E F' κ.g κ.h := by
    intro T b z hb hB hCL R
    subst hb
    exact memberMX_false_LF (A.source pstar hcan hel htc hcc) con hB hCL R _ _ (stateLayer_spec A) _ _
      (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) κ.L κ.γ κ.δ κ.F κ.base lam _ t κ.t1 κ.t2 E F' κ.g κ.h
  have h := key hb sp.hT sp.clST.2 (SplitAt.nextA A sp pstar false).RT
  refine h.trans ?_
  rw [regionData_subsingleton (SplitAt.nextA A sp pstar false).RT sp.RT]

end KT

end WaveTurbulence.VineSpaceB
