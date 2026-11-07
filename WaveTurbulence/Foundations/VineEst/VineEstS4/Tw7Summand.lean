/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Tw6Pairs
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLLocalKernel
public import WaveTurbulence.Foundations.VineEst.RowSel.RowDataLemmas
public import WaveTurbulence.Foundations.Molecule.TwistChildLabels

/-! # K^T twist invariance, the local summand (V5 Step 4b, step 3, part 7) -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree
  MeasureTheory

variable {w : ℕ} {G : Garden w} (P : CorePlacement G) {T : Finset (GBranch G.tree)} {z : GBranch G.tree}
  (hB : G.molecule.IsBlock T P.lower z) (hCL : Mole.CLParentPattern G T P.lower z)
  (R : CLRegionData G T P.lower z) (R' : TwRegion P T z)

section Reg
variable {d : ℕ}

include hB hCL in
theorem eps_reg (ext : GNode G.tree → (Fin d → ℤ)) (ext' : GNode (unitTwistGarden G P).tree → (Fin d → ℤ))
    (hext : ∀ x, ext x = ext' (twNode P x))
    (hcons : ext P.lower.toNode = ext (P.lower.child 0) - ext (P.lower.child 1) + ext (P.lower.child 2)) :
    clRegionalEpsilon (unitTwistGarden G P) (twistedAtoms G P T) ext' = clRegionalEpsilon G T ext := by
  unfold clRegionalEpsilon
  exact (Finset.prod_equiv (eB P) (fun v => (mem_twistedAtoms G P T v).symm)
    (fun v hv => (eps_at P hB hCL ext ext' hext hv hcons).symm)).symm

include hB hCL in
theorem phase_reg (L γ δ : ℝ) (k : GNode G.tree → Mom d) (k' : GNode (unitTwistGarden G P).tree → Mom d)
    (hk : ∀ x, k x = k' (twNode P x)) (u : GBranch G.tree → ℝ) (u' : GBranch (unitTwistGarden G P).tree → ℝ)
    (hu : ∀ v ∈ T, u' (eB P v) = u v) :
    clRegionalPhase (unitTwistGarden G P) (twistedAtoms G P T) L γ δ k' u' = clRegionalPhase G T L γ δ k u := by
  unfold clRegionalPhase
  refine (Finset.prod_equiv (eB P) (fun v => (mem_twistedAtoms G P T v).symm) (fun v hv => ?_)).symm
  rw [hu v hv]
  exact (phaseAtom_congr L γ δ _ _ _ _ _ (sign_omega_at P hB hCL k k' hk hv)).symm

end Reg

section Star
variable {d : ℕ} (hG : G.IsPlain) (D : ReconstructionData G) (D' : ReconstructionData (unitTwistGarden G P))
  (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer)
  (layer' : GNode (D'.forest (unitTwistGarden_plain G P hG)) → ℕ)
  (hLayer' : IsLayering (D'.garden (unitTwistGarden_plain G P hG)) layer') (base : Mom d)

include hB hCL R' in
theorem regional_tp_iff (p : SourcePair G) :
    tp P hG p ∈ clRegionalPairs (unitTwistGarden_plain G P hG) (twistedAtoms G P T) ↔ p ∈ clRegionalPairs hG T := by
  have hpe : tp P hG p = pairOfLeaf (unitTwistGarden G P) (unitTwistGarden_plain G P hG) (eL P (p.firstLeaf hG)) := rfl
  rw [hpe]
  exact (mem_clRegionalPairs_of_leaf (unitTwistGarden G P) (hG := unitTwistGarden_plain G P hG) (U := twistedAtoms G P T)
    (eL P (p.firstLeaf hG))).trans ((internal_iff P hB hCL R' (p.firstLeaf hG)).symm.trans (mem_clRegionalPairs G).symm)

include hB hCL R in
theorem star_reg (ext : GNode G.tree → (Fin d → ℤ)) (ext' : GNode (unitTwistGarden G P).tree → (Fin d → ℤ))
    (hext : ∀ x, ext x = ext' (twNode P x)) (t : Fin 3 → ℝ) (τ : CLInternalTime R)
    (hC : ∀ p ∈ clRegionalPairs hG T, nativeCoupleLayered D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) =
      nativeCoupleLayered D hG layer hLayer p)
    (hT : ∀ v ∈ clInteriorBranches R, nativeChainLayered D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
      nativeChainLayered D hG layer hLayer v)
    (hCi : ∀ p ∈ clRegionalPairs hG T, Flower.V5W.coupleIncoh D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) =
      Flower.V5W.coupleIncoh D hG layer hLayer p)
    (hTi : ∀ v ∈ clInteriorBranches R, Flower.V5W.treeIncoh D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
      Flower.V5W.treeIncoh D hG layer hLayer v)
    (hl : ∀ v ∈ T, layer' (D'.coreBranch (unitTwistGarden_plain G P hG) (eB P v)).toNode =
      layer (D.coreBranch hG v).toNode) :
    clLocalStarProduct D' (unitTwistGarden_plain G P hG) R' L γ δ F layer' hLayer' base ext' t (tEquiv P R R' τ) =
      clLocalStarProduct D hG R L γ δ F layer hLayer base ext t τ := by
  have hclock := fun v (hv : v ∈ T) => clock_corr P R R' t τ hv
  unfold clLocalStarProduct
  simp only []
  refine congrArg₂ (· * ·) ?_ ?_
  · refine (Finset.prod_equiv (tp P hG) (fun p => (regional_tp_iff P hB hCL R' hG p).symm) (fun p hp => ?_)).symm
    obtain ⟨hf, hs⟩ := tp_first P hG hB hCL p hp
    have hint := (mem_clRegionalPairs G).mp hp
    have h1 : p.firstLeaf hG ≠ P.retained := fun h => not_internal_retained P hB hCL (h ▸ hint)
    have hr1 : (p.firstLeaf hG).toNode ∈ clRealizationNodes G T := (leaf_mem_clRealizationNodes _).mpr hint
    have hr2 : (p.secondLeaf hG).toNode ∈ clRealizationNodes G T := by
      have := (Mole.internal_leaf_pair_iff G T (p.firstLeaf hG)).mpr hint
      rw [pair_first_eq_second hG p] at this
      exact (leaf_mem_clRealizationNodes _).mpr this
    have hl1 : (p.firstLeaf hG).toNode ≠ P.lower.toNode := (Mole.branch_toNode_ne_leaf P.lower _).symm
    have hl2 : (p.secondLeaf hG).toNode ≠ P.lower.toNode := (Mole.branch_toNode_ne_leaf P.lower _).symm
    have c1 := parentClock_corr P hB hCL R (t 0) (clLocalClock R t τ) (clLocalClock R' t (tEquiv P R R' τ))
      hclock hr1 hl1
    have c2 := parentClock_corr P hB hCL R (t 0) (clLocalClock R t τ) (clLocalClock R' t (tEquiv P R R' τ))
      hclock hr2 hl2
    have n1 : naiveNodeEquiv G P (p.firstLeaf hG).toNode = (eL P (p.firstLeaf hG)).toNode :=
      naiveNodeEquiv_leaf G P _
    have n2 : naiveNodeEquiv G P (p.secondLeaf hG).toNode = (eL P (p.secondLeaf hG)).toNode :=
      naiveNodeEquiv_leaf G P _
    have hp1 : p.firstLeaf hG ≠ G.pair P.retained := fun h => not_internal_pair P hB hCL (h ▸ hint)
    have hint2 : Mole.IsInternalLeaf G T (p.secondLeaf hG) := by
      have := (Mole.internal_leaf_pair_iff G T (p.firstLeaf hG)).mpr hint
      rwa [pair_first_eq_second hG p] at this
    have hp2 : p.secondLeaf hG ≠ G.pair P.retained := fun h => not_internal_pair P hB hCL (h ▸ hint2)
    obtain ⟨v1, i1, hv1, hx1⟩ := Flower.V5W.real_child hB R hr1 hl1
    obtain ⟨v2, i2, hv2, hx2⟩ := Flower.V5W.real_child hB R hr2 hl2
    have hq : ∀ i, Flower.V5W.coupleRootParents rowSel.p D' (unitTwistGarden_plain G P hG) layer' hLayer'
        (tp P hG p) i = Flower.V5W.coupleRootParents rowSel.p D hG layer hLayer p i := by
      intro i
      fin_cases i
      · have hx1' : ((tp P hG p).firstLeaf (unitTwistGarden_plain G P hG)).toNode =
            (eB P v1).child (exchangeChildSlot P.lower.1 P.keep v1.1 i1) := by
          rw [hf]
          exact (naiveNodeEquiv_leaf G P _).symm.trans
            (naiveNodeEquiv_child G P hx1 hl1 (fun h => hp1 (Mole.leaf_toNode_injective h)))
        show Flower.V5W.coupleRootParents rowSel.p D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) 0 =
          Flower.V5W.coupleRootParents rowSel.p D hG layer hLayer p 0
        rw [Flower.V5W.coupleRootParents_zero D' (unitTwistGarden_plain G P hG) layer' hLayer' rowSel.p (tp P hG p)
            (eB P v1) _ hx1', Flower.V5W.coupleRootParents_zero D hG layer hLayer rowSel.p p v1 i1 hx1, hl v1 hv1]
      · have hx2' : ((tp P hG p).secondLeaf (unitTwistGarden_plain G P hG)).toNode =
            (eB P v2).child (exchangeChildSlot P.lower.1 P.keep v2.1 i2) := by
          rw [hs]
          exact (naiveNodeEquiv_leaf G P _).symm.trans
            (naiveNodeEquiv_child G P hx2 hl2 (fun h => hp2 (Mole.leaf_toNode_injective h)))
        show Flower.V5W.coupleRootParents rowSel.p D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) 1 =
          Flower.V5W.coupleRootParents rowSel.p D hG layer hLayer p 1
        rw [Flower.V5W.coupleRootParents_one D' (unitTwistGarden_plain G P hG) layer' hLayer' rowSel.p (tp P hG p)
            (eB P v2) _ hx2', Flower.V5W.coupleRootParents_one D hG layer hLayer rowSel.p p v2 i2 hx2, hl v2 hv2]
    rw [VineEst.selCoupleRow_congr L γ δ F D hG layer hLayer p D' (unitTwistGarden_plain G P hG) layer' hLayer'
      (tp P hG p) (hC p hp) (hCi p hp) hq, hf, hs]
    have d1 : cosetDecoration (unitTwistGarden G P) L base ext' (eL P (p.firstLeaf hG)).toNode =
        cosetDecoration G L base ext (p.firstLeaf hG).toNode := by
      unfold cosetDecoration
      exact congrArg (fun y => base + latticePoint L y) ((hext _).trans (congrArg ext' (twNode_leaf P _ h1))).symm
    have c1' := (congrArg (parentClock (t 0) (clLocalClock R' t (tEquiv P R R' τ))) n1.symm).trans c1
    have c2' := (congrArg (parentClock (t 0) (clLocalClock R' t (tEquiv P R R' τ))) n2.symm).trans c2
    rw [d1, c1', c2']
  · refine (Finset.prod_equiv (eB P) (fun v => (mem_interior_iff P R R' v).symm) (fun v hv => ?_)).symm
    have hvT : v ∈ T := Finset.mem_of_mem_erase hv
    have hvl : v ≠ P.lower := (Finset.mem_erase.mp hv).1
    have hvn : v.toNode ≠ P.lower.toNode := fun h => hvl (Mole.branch_toNode_injective h)
    have c1 := parentClock_corr P hB hCL R (t 0) (clLocalClock R t τ) (clLocalClock R' t (tEquiv P R R' τ))
      hclock ((branch_mem_clRealizationNodes v).mpr hvT) hvn
    have c1' : parentClock (t 0) (clLocalClock R' t (tEquiv P R R' τ)) (eB P v).toNode =
        parentClock (t 0) (clLocalClock R t τ) v.toNode :=
      (congrArg (parentClock (t 0) (clLocalClock R' t (tEquiv P R R' τ)))
        (naiveNodeEquiv_branch G P v).symm).trans c1
    have d1 : cosetDecoration (unitTwistGarden G P) L base ext' (eB P v).toNode =
        cosetDecoration G L base ext v.toNode := by
      unfold cosetDecoration
      exact congrArg (fun y => base + latticePoint L y) ((hext _).trans (congrArg ext' (twNode_branch P v hvl))).symm
    obtain ⟨c, i, hc, hxc⟩ := Flower.V5W.real_child hB R ((branch_mem_clRealizationNodes v).mpr hvT) hvn
    have hxc' : (eB P v).toNode = (eB P c).child (exchangeChildSlot P.lower.1 P.keep c.1 i) := by
      exact (naiveNodeEquiv_branch G P v).symm.trans
        (naiveNodeEquiv_child G P hxc hvn (Mole.branch_toNode_ne_leaf v _))
    have hqT : Flower.V5W.treeRootParent rowSel.p D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
        Flower.V5W.treeRootParent rowSel.p D hG layer hLayer v := by
      rw [Flower.V5W.treeRootParent_eq D' (unitTwistGarden_plain G P hG) layer' hLayer' rowSel.p (eB P v) (eB P c) _ hxc',
        Flower.V5W.treeRootParent_eq D hG layer hLayer rowSel.p v c i hxc, hl c hc]
    rw [VineEst.selTreeRow_congr L γ δ F D hG layer hLayer v D' (unitTwistGarden_plain G P hG) layer' hLayer'
      (eB P v) (hT v hv) (hTi v hv) hqT, c1', hclock v hvT, d1]

end Star

section Summand
variable {d : ℕ} (hG : G.IsPlain) (D : ReconstructionData G) (D' : ReconstructionData (unitTwistGarden G P))
  (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer)
  (layer' : GNode (D'.forest (unitTwistGarden_plain G P hG)) → ℕ)
  (hLayer' : IsLayering (D'.garden (unitTwistGarden_plain G P hG)) layer') (base : Mom d) (e f g h : Mom d)
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
/-- **The local summand is twist invariant**: the summand of the twisted garden at `κ'` and the clock `tEquiv τ` is the
summand of the original garden at `decEquiv κ'` (boundary momenta `e, f` exchanged) and the clock `τ`. -/
theorem summand_twist (t : Fin 3 → ℝ) (κ' : CLLocalDecoration R' L base ![e, f, g, h]) (τ : CLInternalTime R) :
    clLocalSummand D' (unitTwistGarden_plain G P hG) R' L γ δ F layer' hLayer' base ![e, f, g, h] t κ'
        (tEquiv P R R' τ) =
      clLocalSummand D hG R L γ δ F layer hLayer base ![f, e, g, h] t
        (decEquiv P hB hCL R R' L base e f g h κ') τ := by
  set κ := decEquiv P hB hCL R R' L base e f g h κ' with hκ
  have hext : ∀ x, clExtendIndices R κ.1 x = clExtendIndices R' κ'.1 (twNode P x) :=
    fun x => decEquiv_ext P hB hCL R R' L base e f g h κ' x
  have hcons := κ.2.1 P.lower hB.2.1
  have heps := eps_reg P hB hCL (clExtendIndices R κ.1) (clExtendIndices R' κ'.1) hext hcons
  have hclock := fun v (hv : v ∈ T) => clock_corr P R R' t τ hv
  have hk : ∀ x, cosetDecoration G L base (clExtendIndices R κ.1) x =
      cosetDecoration (unitTwistGarden G P) L base (clExtendIndices R' κ'.1) (twNode P x) := by
    intro x; unfold cosetDecoration; rw [hext x]
  have hph := phase_reg P hB hCL L γ δ _ _ hk (clLocalClock R t τ) (clLocalClock R' t (tEquiv P R R' τ)) hclock
  have hst := star_reg P hB hCL R R' hG D D' L γ δ F layer hLayer layer' hLayer' base (clExtendIndices R κ.1)
    (clExtendIndices R' κ'.1) hext t τ hC hT hCi hTi hl
  have hdom := twDomain_iff P hB hCL R R' (fun v => layer (D.coreBranch hG v).toNode)
    (fun v => layer' (D'.coreBranch (unitTwistGarden_plain G P hG) v).toNode) hl t τ
  unfold clLocalSummand
  rw [heps]
  congr 1
  by_cases hm : τ ∈ clLocalTimeDomain R (fun v => layer (D.coreBranch hG v).toNode) t
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hdom.mpr hm)]
    rw [hph, hst]
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (fun h => hm (hdom.mp h))]

end Summand

end WaveTurbulence.VineEstS4
