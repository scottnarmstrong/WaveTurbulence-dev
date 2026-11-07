/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RowSel.RowDataLF
public import WaveTurbulence.Foundations.VineEst.RowSel.RowTransport
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Rg4Time
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Tw10Final

/-! # The S-side of (tildeJ2) is rigidly twist invariant (V5 Step 4b, step 4, WP-B part 5)

`sSum` is the S-side of the factorized kernel: `coupling^{n₁(S)} ζ_S ∑'_{xS} ∫_σ spart(xS, σ) Φ(σ_b, E(xS), F(xS))`, for an arbitrary
lower-block factor `Φ` (TARGET (tildeJ2): `Φ = K̃^{U<p}`), the boundary labels being read at two nodes `n0, n1`.
`sSum_rigid`: for the rigid image of `S` under a unit twist, with `n0, n1` moved by the naive bijection, `sSum` is unchanged.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree
  MeasureTheory

/-- The S-side of the factorized kernel with an arbitrary lower factor `Φ`. -/
@[expose] noncomputable def sSum {w d : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (RS : CLRegionData G S a b) (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (t0 t1 t2 : ℝ)
    (e f : Mom d) (n0 n1 : GNode G.tree) (Φ : ℝ → Mom d → Mom d → ℂ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ clLocalOrder1 RS * clLocalZeta RS *
    ∑' xS : ExtS RS L base e f, ∫ σ : CLInternalTime RS,
      spart D hG L γ δ F layer hLayer base S a b xS.1 (clLocalClock RS ![t0, t1, t2] σ) *
        Φ (clLocalClock RS ![t0, t1, t2] σ b) (base + latticePoint L (xS.1 n0)) (base + latticePoint L (xS.1 n1))

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
/-- **The S-side of (tildeJ2) is invariant under a rigid twist** (no exchange of the two boundary labels). -/
theorem sSum_rigid (t0 t1 t2 : ℝ) (e f : Mom d) (n0 n1 : GNode G.tree) (Φ : ℝ → Mom d → Mom d → ℂ) :
    sSum RS' D' (unitTwistGarden_plain G P hG) L γ δ F layer' hLayer' base t0 t1 t2 e f
        (naiveNodeEquiv G P n0) (naiveNodeEquiv G P n1) Φ =
      sSum RS D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 Φ := by
  unfold sSum
  rw [order1_rigid P RS RS', zeta_rigid P RS RS' hR]
  congr 1
  rw [← (extSEquiv P RS RS' L base e f hS hR).tsum_eq]
  refine tsum_congr fun xS' => ?_
  rw [← (tEquivS_measurePreserving P RS RS').integral_comp'
    (g := fun σ' => spart D' (unitTwistGarden_plain G P hG) L γ δ F layer' hLayer' base (twistedAtoms G P S) (eB P a)
      (eB P b) xS'.1 (clLocalClock RS' ![t0, t1, t2] σ') *
        Φ (clLocalClock RS' ![t0, t1, t2] σ' (eB P b)) (base + latticePoint L (xS'.1 (naiveNodeEquiv G P n0)))
          (base + latticePoint L (xS'.1 (naiveNodeEquiv G P n1))))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  have hu : ∀ v ∈ S, clLocalClock RS' ![t0, t1, t2] (tEquivS P RS RS' τ) (eB P v) = clLocalClock RS ![t0, t1, t2] τ v :=
    fun v hv => clockS_corr P RS RS' _ τ hv
  have hsp := spart_rigid P hS hR hG D D' L γ δ F layer hLayer layer' hLayer' base hC hT hCi hTi hlS RS xS'.1
    (clLocalClock RS' ![t0, t1, t2] (tEquivS P RS RS' τ)) (clLocalClock RS ![t0, t1, t2] τ) hu hl
  show spart D' (unitTwistGarden_plain G P hG) L γ δ F layer' hLayer' base (twistedAtoms G P S) (eB P a) (eB P b) xS'.1
        (clLocalClock RS' ![t0, t1, t2] (tEquivS P RS RS' τ)) *
      Φ (clLocalClock RS' ![t0, t1, t2] (tEquivS P RS RS' τ) (eB P b)) (base + latticePoint L (xS'.1 (naiveNodeEquiv G P n0)))
        (base + latticePoint L (xS'.1 (naiveNodeEquiv G P n1))) =
      spart D hG L γ δ F layer hLayer base S a b (fun y => xS'.1 (naiveNodeEquiv G P y)) (clLocalClock RS ![t0, t1, t2] τ) *
        Φ (clLocalClock RS ![t0, t1, t2] τ b) (base + latticePoint L (xS'.1 (naiveNodeEquiv G P n0)))
          (base + latticePoint L (xS'.1 (naiveNodeEquiv G P n1)))
  rw [hsp, hu b hS.2.2.1]

/-! ## LF-level statements -/

section LF
variable {p : ℕ} {kind : Bool} {LG : LayeredGarden w} (s : LFSource p kind LG)

/-- **S-side invariance for a TRUE-choice LF construction at a member below the split.** -/
theorem sSum_rigid_LF (h : LFConstruction s true) {S : Finset (GBranch s.skeleton.tree)} {a b : GBranch s.skeleton.tree}
    (hS : s.skeleton.molecule.IsBlock S a b) (hR : RigidAt s.placement S b) (RS : CLRegionData s.skeleton S a b)
    (RS' : CLRegionData (unitTwistGarden s.skeleton s.placement) (twistedAtoms s.skeleton s.placement S)
      (eB s.placement a) (eB s.placement b))
    (layer : GNode (s.data.forest s.plain) → ℕ) (hLayer : IsLayering (s.data.garden s.plain) layer)
    (hspec : layeredReconstruction s.data s.plain layer hLayer = LG)
    (layer' : GNode (h.data.forest (s.chosen_plain true)) → ℕ)
    (hLayer' : IsLayering (h.data.garden (s.chosen_plain true)) layer')
    (hspec' : layeredReconstruction h.data (s.chosen_plain true) layer' hLayer' = h.output)
    {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (t0 t1 t2 : ℝ) (e f : Mom d) (n0 n1 : GNode s.skeleton.tree)
    (Φ : ℝ → Mom d → Mom d → ℂ) :
    sSum RS' h.data (s.chosen_plain true) L γ δ F layer' hLayer' base t0 t1 t2 e f
        (naiveNodeEquiv s.skeleton s.placement n0) (naiveNodeEquiv s.skeleton s.placement n1) Φ =
      sSum RS s.data s.plain L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 Φ := by
  refine sSum_rigid s.placement hS hR RS RS' s.plain s.data h.data L γ δ F layer hLayer layer' hLayer' base ?_ ?_ ?_ ?_ ?_ ?_
    t0 t1 t2 e f n0 n1 Φ
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

/-- **S-side invariance for a FALSE-choice LF construction** (same skeleton and region, native rows equal). -/
theorem sSum_false_LF (h : LFConstruction s false) {S : Finset (GBranch s.skeleton.tree)} {a b : GBranch s.skeleton.tree}
    (hlow : s.placement.lower ∉ S) (RS : CLRegionData s.skeleton S a b)
    (layer : GNode (s.data.forest s.plain) → ℕ) (hLayer : IsLayering (s.data.garden s.plain) layer)
    (hspec : layeredReconstruction s.data s.plain layer hLayer = LG)
    (layer' : GNode (h.data.forest (s.chosen_plain false)) → ℕ)
    (hLayer' : IsLayering (h.data.garden (s.chosen_plain false)) layer')
    (hspec' : layeredReconstruction h.data (s.chosen_plain false) layer' hLayer' = h.output)
    {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (t0 t1 t2 : ℝ) (e f : Mom d) (n0 n1 : GNode s.skeleton.tree)
    (Φ : ℝ → Mom d → Mom d → ℂ) :
    sSum RS h.data (s.chosen_plain false) L γ δ F layer' hLayer' base t0 t1 t2 e f n0 n1 Φ =
      sSum RS s.data s.plain L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 Φ := by
  unfold sSum
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

end WaveTurbulence.VineEstS4
