/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5W.RowData
public import WaveTurbulence.Foundations.VineEst.RowSel.RowDataLemmas

/-! # V5W-0: the weighted kernel with selected rows under a rigid twist and under a FALSE operation

Weighted copies of main's `VineC.summand_rigid`, `clLocalKernelW_rigid`, `clLocalKernelW_congr_data`,
`clLocalKernelW_rigid_LF`, `clLocalKernelW_false_LF` (VCRigid2), for `clLocalKernelFW`:

* the selected factor `clLocalStarProductFW` is transported pair by pair and branch by branch; besides the native rows
  (`hC`, `hT`) and the atom layers (`hl`, now on the whole region, for the root parent layers) it needs the incoherency
  indices of the rows (`hCi`, `hTi`), from which the selection is read;
* the spatial multiplier `m` is transported along the naive node bijection (`hm`);
* the LF statements derive `hCi`, `hTi` from `coupleIncoh_LF`, `treeIncoh_LF`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
noncomputable section
namespace WaveTurbulence.Flower.V5W
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.Reg
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton WaveTurbulence.VineEstS4 TTree MeasureTheory
open WaveTurbulence.VineC WaveTurbulence.LGSpine WaveTurbulence.Flower.Stage1W

/- `real_child` is now on main (416902c8, V5W-B: `VineEst/RowSel/RowDataLemmas.lean`), imported above. -/

section Summand
variable {w : ℕ} {G : Garden w} {P : CorePlacement G} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  (hB : G.molecule.IsBlock U a b) (hF : FullRigid P U)
  (R : CLRegionData G U a b) (R' : CLRegionData (unitTwistGarden G P) (twistedAtoms G P U) (eB P a) (eB P b))
variable {d : ℕ} (pw : ℕ) (g : Mom d → ℂ) (hG : G.IsPlain) (D : ReconstructionData G)
  (D' : ReconstructionData (unitTwistGarden G P))
  (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer)
  (layer' : GNode (D'.forest (unitTwistGarden_plain G P hG)) → ℕ)
  (hLayer' : IsLayering (D'.garden (unitTwistGarden_plain G P hG)) layer') (base : Mom d) (β : Fin 4 → Mom d)
  (hC : ∀ p ∈ clRegionalPairs hG U, nativeCoupleLayered D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) =
      nativeCoupleLayered D hG layer hLayer p)
  (hT : ∀ v ∈ U.erase a, nativeChainLayered D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
      nativeChainLayered D hG layer hLayer v)
  (hl : ∀ v ∈ U, layer' (D'.coreBranch (unitTwistGarden_plain G P hG) (eB P v)).toNode =
      layer (D.coreBranch hG v).toNode)
  (hCi : ∀ p ∈ clRegionalPairs hG U, coupleIncoh D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) =
      coupleIncoh D hG layer hLayer p)
  (hTi : ∀ v ∈ U.erase a, treeIncoh D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
      treeIncoh D hG layer hLayer v)

include hB hF hC hT hl hCi hTi in
/-- **The selected regional factor is invariant under a rigid twist.** -/
theorem starProductFW_rigid (t : Fin 3 → ℝ) (x' : GNode (unitTwistGarden G P).tree → (Fin d → ℤ))
    (τ : CLInternalTime R) :
    clLocalStarProductFW pw g D' (unitTwistGarden_plain G P hG) R' L γ δ F layer' hLayer' base x' t
        (tEquivS P R R' τ) =
      clLocalStarProductFW pw g D hG R L γ δ F layer hLayer base (fun y => x' (naiveNodeEquiv G P y)) t τ := by
  have hR := hF.rigidAt b
  have hu : ∀ v ∈ U, clLocalClock R' t (tEquivS P R R' τ) (eB P v) = clLocalClock R t τ v :=
    fun v hv => clockS_corr P R R' t τ hv
  dsimp only [clLocalStarProductFW]
  refine congrArg₂ (· * ·) ?_ ?_
  · refine (Finset.prod_equiv (tp P hG) (fun q => (regional_tp_rigid P hR hG q).symm) (fun q hq => ?_)).symm
    obtain ⟨hf, hs⟩ := tp_first_rigid P hR hG q hq
    have hint := (mem_clRegionalPairs G).mp hq
    have hr1 : (q.firstLeaf hG).toNode ∈ clRealizationNodes G U := (leaf_mem_clRealizationNodes _).mpr hint
    have hr2 : (q.secondLeaf hG).toNode ∈ clRealizationNodes G U := by
      have := (Mole.internal_leaf_pair_iff G U (q.firstLeaf hG)).mpr hint
      rw [pair_first_eq_second hG q] at this
      exact (leaf_mem_clRealizationNodes _).mpr this
    have hl1 : (q.firstLeaf hG).toNode ≠ a.toNode := (Mole.branch_toNode_ne_leaf a _).symm
    have hl2 : (q.secondLeaf hG).toNode ≠ a.toNode := (Mole.branch_toNode_ne_leaf a _).symm
    have c1 := parentClock_rigid P hB hR R (t 0) _ _ hu hr1 hl1
    have c2 := parentClock_rigid P hB hR R (t 0) _ _ hu hr2 hl2
    have n1 : naiveNodeEquiv G P (q.firstLeaf hG).toNode = (eL P (q.firstLeaf hG)).toNode := naiveNodeEquiv_leaf G P _
    have n2 : naiveNodeEquiv G P (q.secondLeaf hG).toNode = (eL P (q.secondLeaf hG)).toNode :=
      naiveNodeEquiv_leaf G P _
    have c1' := (congrArg (parentClock (t 0) (clLocalClock R' t (tEquivS P R R' τ))) n1.symm).trans c1
    have c2' := (congrArg (parentClock (t 0) (clLocalClock R' t (tEquivS P R R' τ))) n2.symm).trans c2
    have d1 : cosetDecoration (unitTwistGarden G P) L base x' (eL P (q.firstLeaf hG)).toNode =
        cosetDecoration G L base (fun y => x' (naiveNodeEquiv G P y)) (q.firstLeaf hG).toNode := by
      unfold cosetDecoration
      exact congrArg (fun y => base + latticePoint L y) (congrArg x' n1.symm)
    obtain ⟨v1, i1, hv1, hx1, hn1⟩ := naive_real P hB hR R hr1 hl1
    obtain ⟨v2, i2, hv2, hx2, hn2⟩ := naive_real P hB hR R hr2 hl2
    have r0 : coupleRootParents pw D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG q) 0 =
        coupleRootParents pw D hG layer hLayer q 0 := by
      rw [coupleRootParents_zero D' (unitTwistGarden_plain G P hG) layer' hLayer' pw (tp P hG q) (eB P v1) i1
          (by rw [hf, ← n1, hn1]),
        coupleRootParents_zero D hG layer hLayer pw q v1 i1 hx1, hl v1 hv1]
    have r1 : coupleRootParents pw D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG q) 1 =
        coupleRootParents pw D hG layer hLayer q 1 := by
      rw [coupleRootParents_one D' (unitTwistGarden_plain G P hG) layer' hLayer' pw (tp P hG q) (eB P v2) i2
          (by rw [hs, ← n2, hn2]),
        coupleRootParents_one D hG layer hLayer pw q v2 i2 hx2, hl v2 hv2]
    rw [hf, hs, hC q hq, hCi q hq, r0, r1, c1', c2', d1]
  · have hset : ∀ v, v ∈ U.erase a ↔ eB P v ∈ (twistedAtoms G P U).erase (eB P a) := fun v =>
      (mem_erase_twisted P (b := a) v).symm
    refine (Finset.prod_equiv (eB P) (fun v => hset v) (fun v hv => ?_)).symm
    have hvS : v ∈ U := Finset.mem_of_mem_erase hv
    have hva : v ≠ a := (Finset.mem_erase.mp hv).1
    have hvn : v.toNode ≠ a.toNode := fun h => hva (Mole.branch_toNode_injective h)
    have hrv := (branch_mem_clRealizationNodes (U := U) v).mpr hvS
    have c1 := parentClock_rigid P hB hR R (t 0) _ _ hu hrv hvn
    have c1' : parentClock (t 0) (clLocalClock R' t (tEquivS P R R' τ)) (eB P v).toNode =
        parentClock (t 0) (clLocalClock R t τ) v.toNode :=
      (congrArg (parentClock (t 0) (clLocalClock R' t (tEquivS P R R' τ))) (naiveNodeEquiv_branch G P v).symm).trans c1
    have d1 : cosetDecoration (unitTwistGarden G P) L base x' (eB P v).toNode =
        cosetDecoration G L base (fun y => x' (naiveNodeEquiv G P y)) v.toNode := by
      unfold cosetDecoration
      exact congrArg (fun y => base + latticePoint L y) (congrArg x' (naiveNodeEquiv_branch G P v).symm)
    obtain ⟨c, i, hc, hxc, hnc⟩ := naive_real P hB hR R hrv hvn
    have rT : treeRootParent pw D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
        treeRootParent pw D hG layer hLayer v := by
      rw [treeRootParent_eq D' (unitTwistGarden_plain G P hG) layer' hLayer' pw (eB P v) (eB P c) i
          ((naiveNodeEquiv_branch G P v).symm.trans hnc),
        treeRootParent_eq D hG layer hLayer pw v c i hxc, hl c hc]
    rw [hT v hv, hTi v hv, rT, c1', hu v hvS, d1]

include hB hF hC hT hl hCi hTi in
/-- **The local summand with selected rows is invariant under a rigid twist** (no exchange of the boundary momenta). -/
theorem summandFW_rigid (t : Fin 3 → ℝ) (κ' : CLLocalDecoration R' L base β) (τ : CLInternalTime R) :
    clLocalSummandFW pw g D' (unitTwistGarden_plain G P hG) R' L γ δ F layer' hLayer' base β t κ' (tEquivS P R R' τ) =
      clLocalSummandFW pw g D hG R L γ δ F layer hLayer base β t (decEquivR hB hF R R' L base β κ') τ := by
  set κ := decEquivR hB hF R R' L base β κ' with hκ
  have hRl := hF.rigidAt P.lower
  have hext : clExtendIndices R κ.1 = fun y => clExtendIndices R' κ'.1 (naiveNodeEquiv G P y) :=
    funext fun x => decEquivR_ext hB hF R R' L base β κ' x
  have hclock := fun v (hv : v ∈ U) => clockS_corr P R R' t τ hv
  have heps : clRegionalEpsilon (unitTwistGarden G P) (twistedAtoms G P U) (clExtendIndices R' κ'.1) =
      clRegionalEpsilon G U (clExtendIndices R κ.1) := by
    have := eps_rigid P hRl (clExtendIndices R' κ'.1)
    rw [hF.erase_lower', hF.erase_lower] at this
    rw [hext]
    exact this
  have hk : cosetDecoration G L base (clExtendIndices R κ.1) =
      fun y => cosetDecoration (unitTwistGarden G P) L base (clExtendIndices R' κ'.1) (naiveNodeEquiv G P y) := by
    funext y
    unfold cosetDecoration
    rw [hext]
  have hph : clRegionalPhase (unitTwistGarden G P) (twistedAtoms G P U) L γ δ
        (cosetDecoration (unitTwistGarden G P) L base (clExtendIndices R' κ'.1)) (clLocalClock R' t (tEquivS P R R' τ)) =
      clRegionalPhase G U L γ δ (cosetDecoration G L base (clExtendIndices R κ.1)) (clLocalClock R t τ) := by
    have := phase_rigid P hRl L γ δ (cosetDecoration (unitTwistGarden G P) L base (clExtendIndices R' κ'.1))
      (clLocalClock R' t (tEquivS P R R' τ)) (clLocalClock R t τ)
      (fun v hv => hclock v (Finset.mem_of_mem_erase hv))
    rw [hF.erase_lower', hF.erase_lower] at this
    rw [hk]
    exact this
  have hst : clLocalStarProductFW pw g D' (unitTwistGarden_plain G P hG) R' L γ δ F layer' hLayer' base
        (clExtendIndices R' κ'.1) t (tEquivS P R R' τ) =
      clLocalStarProductFW pw g D hG R L γ δ F layer hLayer base (clExtendIndices R κ.1) t τ := by
    rw [hext]
    exact starProductFW_rigid hB hF R R' pw g hG D D' L γ δ F layer hLayer layer' hLayer' base hC hT hl hCi hTi t
      (clExtendIndices R' κ'.1) τ
  have hdom := domain_iff_rigid hB hF R R' (fun v => layer (D.coreBranch hG v).toNode)
    (fun v => layer' (D'.coreBranch (unitTwistGarden_plain G P hG) v).toNode) hl t τ
  unfold clLocalSummandFW
  rw [heps]
  congr 1
  by_cases hm : τ ∈ clLocalTimeDomain R (fun v => layer (D.coreBranch hG v).toNode) t
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hdom.mpr hm)]
    rw [hph, hst]
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (fun h => hm (hdom.mp h))]

include hB hF hC hT hl hCi hTi in
/-- **The weighted kernel with selected rows is invariant under a rigid twist**, for multipliers related by the naive
node bijection. -/
theorem clLocalKernelFW_rigid (m : (GNode G.tree → Fin d → ℤ) → ℂ)
    (m' : (GNode (unitTwistGarden G P).tree → Fin d → ℤ) → ℂ)
    (hm : ∀ z', m' z' = m (fun y => z' (naiveNodeEquiv G P y)))
    (W : ℝ → ℂ) (t0 t1 t2 : ℝ) (e f g' h : Mom d) :
    clLocalKernelFW pw g D' (unitTwistGarden_plain G P hG) R' L γ δ F layer' hLayer' base m' W t0 t1 t2 e f g' h =
      clLocalKernelFW pw g D hG R L γ δ F layer hLayer base m W t0 t1 t2 e f g' h := by
  unfold clLocalKernelFW
  rw [order1_rigid P R R', zeta_rigid P R R' (hF.rigidAt b)]
  congr 1
  have hint : ∀ κ' : CLLocalDecoration R' L base ![e, f, g', h],
      ∫ τ' : CLInternalTime R', m' (clExtendIndices R' κ'.1) *
        (clLocalSummandFW pw g D' (unitTwistGarden_plain G P hG) R' L γ δ F layer' hLayer' base
          ![e, f, g', h] ![t0, t1, t2] κ' τ' * W (clLocalClock R' ![t0, t1, t2] τ' (eB P b))) =
        ∫ τ : CLInternalTime R, m (clExtendIndices R (decEquivR hB hF R R' L base ![e, f, g', h] κ').1) *
          (clLocalSummandFW pw g D hG R L γ δ F layer hLayer base ![e, f, g', h] ![t0, t1, t2]
            (decEquivR hB hF R R' L base ![e, f, g', h] κ') τ * W (clLocalClock R ![t0, t1, t2] τ b)) := by
    intro κ'
    have hmk : m' (clExtendIndices R' κ'.1) =
        m (clExtendIndices R (decEquivR hB hF R R' L base ![e, f, g', h] κ').1) := by
      rw [hm]
      congr 1
      funext y
      exact (decEquivR_ext hB hF R R' L base _ κ' y).symm
    rw [← (tEquivS_measurePreserving P R R').integral_comp' (g := fun τ' => m' (clExtendIndices R' κ'.1) *
      (clLocalSummandFW pw g D' _ R' L γ δ F layer' hLayer' base ![e, f, g', h] ![t0, t1, t2] κ' τ' *
        W (clLocalClock R' ![t0, t1, t2] τ' (eB P b))))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    show m' (clExtendIndices R' κ'.1) *
        (clLocalSummandFW pw g D' _ R' L γ δ F layer' hLayer' base ![e, f, g', h] ![t0, t1, t2] κ' (tEquivS P R R' τ) *
          W (clLocalClock R' ![t0, t1, t2] (tEquivS P R R' τ) (eB P b))) = _
    rw [summandFW_rigid hB hF R R' pw g hG D D' L γ δ F layer hLayer layer' hLayer' base ![e, f, g', h] hC hT hl hCi
      hTi, clockS_corr P R R' _ τ hB.2.2.1, hmk]
  rw [tsum_congr hint]
  exact (decEquivR hB hF R R' L base ![e, f, g', h]).tsum_eq
    (fun κ => ∫ τ : CLInternalTime R, m (clExtendIndices R κ.1) *
      (clLocalSummandFW pw g D hG R L γ δ F layer hLayer base ![e, f, g', h] ![t0, t1, t2] κ τ *
        W (clLocalClock R ![t0, t1, t2] τ b)))

end Summand

section Congr
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {d : ℕ} (pw : ℕ) (g : Mom d → ℂ) (hB : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (hG : G.IsPlain)
  (D1 D2 : ReconstructionData G) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer1 : GNode (D1.forest hG) → ℕ) (hLayer1 : IsLayering (D1.garden hG) layer1)
  (layer2 : GNode (D2.forest hG) → ℕ) (hLayer2 : IsLayering (D2.garden hG) layer2) (base : Mom d)
  (hC : ∀ p ∈ clRegionalPairs hG U, nativeCoupleLayered D1 hG layer1 hLayer1 p = nativeCoupleLayered D2 hG layer2 hLayer2 p)
  (hT : ∀ v ∈ clInteriorBranches R, nativeChainLayered D1 hG layer1 hLayer1 v = nativeChainLayered D2 hG layer2 hLayer2 v)
  (hl : ∀ v ∈ U, layer1 (D1.coreBranch hG v).toNode = layer2 (D2.coreBranch hG v).toNode)
  (hCi : ∀ p ∈ clRegionalPairs hG U, coupleIncoh D1 hG layer1 hLayer1 p = coupleIncoh D2 hG layer2 hLayer2 p)
  (hTi : ∀ v ∈ clInteriorBranches R, treeIncoh D1 hG layer1 hLayer1 v = treeIncoh D2 hG layer2 hLayer2 v)

include hB hC hT hl hCi hTi in
theorem starProductFW_congr_data (κ : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (τ : CLInternalTime R) :
    clLocalStarProductFW pw g D1 hG R L γ δ F layer1 hLayer1 base κ t τ =
      clLocalStarProductFW pw g D2 hG R L γ δ F layer2 hLayer2 base κ t τ := by
  dsimp only [clLocalStarProductFW]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun q hq => ?_) (Finset.prod_congr rfl fun v hv => ?_)
  · have hint := (mem_clRegionalPairs G).mp hq
    have hr1 : (q.firstLeaf hG).toNode ∈ clRealizationNodes G U := (leaf_mem_clRealizationNodes _).mpr hint
    have hr2 : (q.secondLeaf hG).toNode ∈ clRealizationNodes G U := by
      have := (Mole.internal_leaf_pair_iff G U (q.firstLeaf hG)).mpr hint
      rw [pair_first_eq_second hG q] at this
      exact (leaf_mem_clRealizationNodes _).mpr this
    obtain ⟨v1, i1, hv1, hx1⟩ := real_child hB R hr1 (Mole.branch_toNode_ne_leaf a _).symm
    obtain ⟨v2, i2, hv2, hx2⟩ := real_child hB R hr2 (Mole.branch_toNode_ne_leaf a _).symm
    rw [hC q hq, hCi q hq, coupleRootParents_zero D1 hG layer1 hLayer1 pw q v1 i1 hx1,
      coupleRootParents_zero D2 hG layer2 hLayer2 pw q v1 i1 hx1, coupleRootParents_one D1 hG layer1 hLayer1 pw q v2 i2 hx2,
      coupleRootParents_one D2 hG layer2 hLayer2 pw q v2 i2 hx2, hl v1 hv1, hl v2 hv2]
  · have hvS : v ∈ U := Finset.mem_of_mem_erase hv
    have hvn : v.toNode ≠ a.toNode := fun h => (Finset.mem_erase.mp hv).1 (Mole.branch_toNode_injective h)
    obtain ⟨c, i, hc, hxc⟩ := real_child hB R ((branch_mem_clRealizationNodes (U := U) v).mpr hvS) hvn
    rw [hT v hv, hTi v hv, treeRootParent_eq D1 hG layer1 hLayer1 pw v c i hxc,
      treeRootParent_eq D2 hG layer2 hLayer2 pw v c i hxc, hl c hc]

include hB hC hT hl hCi hTi in
/-- The weighted kernel with selected rows reads the reconstruction data only through the native rows, their
incoherency indices and the atom layers. -/
theorem clLocalKernelFW_congr_data (m1 m2 : (GNode G.tree → Fin d → ℤ) → ℂ) (hm : ∀ z, m1 z = m2 z)
    (W : ℝ → ℂ) (t0 t1 t2 : ℝ) (e f g' k : Mom d) :
    clLocalKernelFW pw g D1 hG R L γ δ F layer1 hLayer1 base m1 W t0 t1 t2 e f g' k =
      clLocalKernelFW pw g D2 hG R L γ δ F layer2 hLayer2 base m2 W t0 t1 t2 e f g' k := by
  unfold clLocalKernelFW
  congr 1
  refine tsum_congr fun κ => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  rw [hm]
  unfold clLocalSummandFW
  have hstar : ∀ (κ' : GNode G.tree → (Fin d → ℤ)) (t' : Fin 3 → ℝ) (τ' : CLInternalTime R),
      clLocalStarProductFW pw g D1 hG R L γ δ F layer1 hLayer1 base κ' t' τ' =
        clLocalStarProductFW pw g D2 hG R L γ δ F layer2 hLayer2 base κ' t' τ' :=
    fun κ' t' τ' => starProductFW_congr_data pw g hB R hG D1 D2 L γ δ F layer1 hLayer1 layer2 hLayer2 base hC hT hl hCi
      hTi κ' t' τ'
  simp only [hstar]
  rw [clLocalTimeDomain_congr_data R hG D1 D2 layer1 layer2 (fun v hv => hl v (Finset.mem_of_mem_erase hv))]

end Congr

section LF
variable {w : ℕ} {p : ℕ} {kind : Bool} {LG : LayeredGarden w} (s : LFSource p kind LG)

/-- **Rigid invariance for a TRUE-choice LF construction at a placement that moves `U` rigidly.** -/
theorem clLocalKernelFW_rigid_LF (h : LFConstruction s true) {U : Finset (GBranch s.skeleton.tree)}
    {a b : GBranch s.skeleton.tree} (hB : s.skeleton.molecule.IsBlock U a b) (hF : FullRigid s.placement U)
    (R : CLRegionData s.skeleton U a b)
    (R' : CLRegionData (unitTwistGarden s.skeleton s.placement) (twistedAtoms s.skeleton s.placement U)
      (eB s.placement a) (eB s.placement b))
    (layer : GNode (s.data.forest s.plain) → ℕ) (hLayer : IsLayering (s.data.garden s.plain) layer)
    (hspec : layeredReconstruction s.data s.plain layer hLayer = LG)
    (layer' : GNode (h.data.forest (s.chosen_plain true)) → ℕ)
    (hLayer' : IsLayering (h.data.garden (s.chosen_plain true)) layer')
    (hspec' : layeredReconstruction h.data (s.chosen_plain true) layer' hLayer' = h.output)
    {d : ℕ} (pw : ℕ) (g : Mom d → ℂ) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d)
    (m : (GNode s.skeleton.tree → Fin d → ℤ) → ℂ)
    (m' : (GNode (unitTwistGarden s.skeleton s.placement).tree → Fin d → ℤ) → ℂ)
    (hm : ∀ z', m' z' = m (fun y => z' (naiveNodeEquiv s.skeleton s.placement y)))
    (W : ℝ → ℂ) (t0 t1 t2 : ℝ) (e f g' k : Mom d) :
    clLocalKernelFW pw g h.data (s.chosen_plain true) R' L γ δ F layer' hLayer' base m' W t0 t1 t2 e f g' k =
      clLocalKernelFW pw g s.data s.plain R L γ δ F layer hLayer base m W t0 t1 t2 e f g' k := by
  have hne : ∀ q ∈ clRegionalPairs s.plain U, q ≠ s.exceptional := by
    intro q hq hqe
    have hint := (mem_clRegionalPairs s.skeleton).mp hq
    have hqe' : q = pairOfLeaf s.skeleton s.plain s.placement.retained := hqe
    subst hqe'
    rcases pairOfLeaf_first_or_partner s.skeleton s.plain s.placement.retained with hq' | hq'
    · exact not_internal_retained_of s.placement hF.lower_notMem (hq' ▸ hint)
    · exact not_internal_pair_of s.placement hF.lower_notMem (hq' ▸ hint)
  refine clLocalKernelFW_rigid hB hF R R' pw g s.plain s.data h.data L γ δ F layer hLayer layer' hLayer' base ?_ ?_ ?_
    ?_ ?_ m m' hm W t0 t1 t2 e f g' k
  · intro q hq
    exact native_couple_eq h layer hLayer hspec layer' hLayer' hspec' q (hne q hq)
  · intro v hv
    exact native_tree_eq h layer hLayer hspec layer' hLayer' hspec' v (hF.ne_lower (Finset.mem_of_mem_erase hv))
  · intro v _
    exact coreLayer_eq h layer hLayer hspec layer' hLayer' hspec' v
  · intro q hq
    exact coupleIncoh_LF h layer hLayer hspec layer' hLayer' hspec' q (hne q hq)
  · intro v hv
    exact treeIncoh_LF h layer hLayer hspec layer' hLayer' hspec' v (hF.ne_lower (Finset.mem_of_mem_erase hv))

/-- **Invariance for a FALSE-choice LF construction at a placement whose lower joint is outside `U`.** -/
theorem clLocalKernelFW_false_LF (h : LFConstruction s false) {U : Finset (GBranch s.skeleton.tree)}
    {a b : GBranch s.skeleton.tree} (hB : s.skeleton.molecule.IsBlock U a b) (hlow : s.placement.lower ∉ U)
    (R : CLRegionData s.skeleton U a b)
    (layer : GNode (s.data.forest s.plain) → ℕ) (hLayer : IsLayering (s.data.garden s.plain) layer)
    (hspec : layeredReconstruction s.data s.plain layer hLayer = LG)
    (layer' : GNode (h.data.forest (s.chosen_plain false)) → ℕ)
    (hLayer' : IsLayering (h.data.garden (s.chosen_plain false)) layer')
    (hspec' : layeredReconstruction h.data (s.chosen_plain false) layer' hLayer' = h.output)
    {d : ℕ} (pw : ℕ) (g : Mom d → ℂ) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d)
    (m m' : (GNode s.skeleton.tree → Fin d → ℤ) → ℂ) (hm : ∀ z, m' z = m z)
    (W : ℝ → ℂ) (t0 t1 t2 : ℝ) (e f g' k : Mom d) :
    clLocalKernelFW pw g h.data (s.chosen_plain false) R L γ δ F layer' hLayer' base m' W t0 t1 t2 e f g' k =
      clLocalKernelFW pw g s.data s.plain R L γ δ F layer hLayer base m W t0 t1 t2 e f g' k := by
  have hne : ∀ q ∈ clRegionalPairs s.plain U, q ≠ s.exceptional := by
    intro q hq hqe
    have hint := (mem_clRegionalPairs s.skeleton).mp hq
    have hqe' : q = pairOfLeaf s.skeleton s.plain s.placement.retained := hqe
    subst hqe'
    rcases pairOfLeaf_first_or_partner s.skeleton s.plain s.placement.retained with hq' | hq'
    · exact not_internal_retained_of s.placement hlow (hq' ▸ hint)
    · exact not_internal_pair_of s.placement hlow (hq' ▸ hint)
  have hp : ∀ q : SourcePair s.skeleton, s.pairs false q = q := fun q => pairOfLeaf_firstLeaf s.skeleton s.plain q
  refine clLocalKernelFW_congr_data pw g hB R s.plain h.data s.data L γ δ F layer' hLayer' layer hLayer base ?_ ?_ ?_
    ?_ ?_ m' m hm W t0 t1 t2 e f g' k
  · intro q hq
    have := native_couple_eq h layer hLayer hspec layer' hLayer' hspec' q (hne q hq)
    rwa [hp] at this
  · intro v hv
    have hvl : v ≠ s.placement.lower := fun he => hlow (he ▸ Finset.mem_of_mem_erase hv)
    exact native_tree_eq h layer hLayer hspec layer' hLayer' hspec' v hvl
  · intro v _
    exact coreLayer_eq h layer hLayer hspec layer' hLayer' hspec' v
  · intro q hq
    have := coupleIncoh_LF h layer hLayer hspec layer' hLayer' hspec' q (hne q hq)
    rwa [hp] at this
  · intro v hv
    have hvl : v ≠ s.placement.lower := fun he => hlow (he ▸ Finset.mem_of_mem_erase hv)
    exact treeIncoh_LF h layer hLayer hspec layer' hLayer' hspec' v hvl

end LF

end WaveTurbulence.Flower.V5W
