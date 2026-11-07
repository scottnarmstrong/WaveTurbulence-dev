/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RowSel.RowDataLemmas
public import WaveTurbulence.Foundations.Molecule.TwistChildLabels
public import WaveTurbulence.Foundations.VineEst.VineEstS5B.Fac1

/-! # V5 Step 4d-B: the factors of the S-side under a twist at the lower joint (part 2)

The ordinary rows (regional pairs other than the pair of the retained leaf, interior branches other than the lower
joint) and `spartFrame_tw`: the frame of the twisted S-part, evaluated at the label-switched decoration and the
transported clocks, is the frame of the original.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.RegRed
  WaveTurbulence.Reg.Skeleton TTree

variable {w : ℕ} {G : Garden w} {P : CorePlacement G} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  {RS : CLRegionData G S a b}
  {RS' : CLRegionData (unitTwistGarden G P) (twistedAtoms G P S) (eB P a) (eB P b)} (h : STw P RS RS')

section Pairs
variable (hG : G.IsPlain)

theorem tp_first_of_ne (p : SourcePair G) (hp : p ≠ pairOfLeaf G hG P.retained) :
    (tp P hG p).firstLeaf (unitTwistGarden_plain G P hG) = eL P (p.firstLeaf hG) ∧
    (tp P hG p).secondLeaf (unitTwistGarden_plain G P hG) = eL P (p.secondLeaf hG) := by
  have h1 : p.firstLeaf hG ≠ P.retained := fun e => hp (by rw [← pairOfLeaf_firstLeaf G hG p, e])
  have h2 : p.firstLeaf hG ≠ G.pair P.retained := fun e => hp (by
    rw [← pairOfLeaf_firstLeaf G hG p, e, pairOfLeaf_partner])
  have hs : nodeSign (unitTwistGarden G P).sig (eL P (p.firstLeaf hG)).1 = 1 := by
    have := coreLeafEquiv_sign G P (p.firstLeaf hG)
    simp only [coreLeafMultiplier, h1, h2, or_self, ite_false, one_mul] at this
    exact this.trans (sourcePair_first_sign G hG p)
  have hpe : tp P hG p = pairOfLeaf (unitTwistGarden G P) (unitTwistGarden_plain G P hG) (eL P (p.firstLeaf hG)) := rfl
  obtain ⟨hf, hsec⟩ := pairOfLeaf_sides_pos (unitTwistGarden G P) (unitTwistGarden_plain G P hG) _ hs
  rw [hpe]
  refine ⟨hf, ?_⟩
  rw [hsec]
  exact (unitTwistGarden_pair G P (p.firstLeaf hG)).trans (congrArg (eL P) (pair_first_eq_second hG p))

include h in
theorem mem_pairs_tw (p : SourcePair G) :
    tp P hG p ∈ clRegionalPairs (unitTwistGarden_plain G P hG) (twistedAtoms G P S) ↔ p ∈ clRegionalPairs hG S := by
  rw [mem_clRegionalPairs, mem_clRegionalPairs]
  have hpe : tp P hG p = pairOfLeaf (unitTwistGarden G P) (unitTwistGarden_plain G P hG) (eL P (p.firstLeaf hG)) := rfl
  rw [hpe]
  rcases pairOfLeaf_first_or_partner (unitTwistGarden G P) (unitTwistGarden_plain G P hG) (eL P (p.firstLeaf hG)) with e | e
  · rw [e]; exact h.internal_iff _
  · rw [e, Mole.internal_leaf_pair_iff]
    exact h.internal_iff _

end Pairs

section Rows
variable {d : ℕ} (hG : G.IsPlain) (D : ReconstructionData G) (D' : ReconstructionData (unitTwistGarden G P))
  (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer)
  (layer' : GNode (D'.forest (unitTwistGarden_plain G P hG)) → ℕ)
  (hLayer' : IsLayering (D'.garden (unitTwistGarden_plain G P hG)) layer') (base : Mom d)
  (x : GNode G.tree → (Fin d → ℤ)) (hpx : PairedAt P x)
  (u' : GBranch (unitTwistGarden G P).tree → ℝ) (u : GBranch G.tree → ℝ) (hu : ∀ v ∈ S, u' (eB P v) = u v)

include h hu in
theorem qRow_tw (p : SourcePair G) (hp : p ∈ clRegionalPairs hG S) (hp0 : p ≠ pairOfLeaf G hG P.retained)
    (hC : nativeCoupleLayered D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) =
      nativeCoupleLayered D hG layer hLayer p)
    (hCi : Flower.V5W.coupleIncoh D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) =
      Flower.V5W.coupleIncoh D hG layer hLayer p)
    (hlS : ∀ v ∈ S, layer' (D'.coreBranch (unitTwistGarden_plain G P hG) (eB P v)).toNode =
      layer (D.coreBranch hG v).toNode) :
    qRow D' (unitTwistGarden_plain G P hG) L γ δ F layer' hLayer' base (u' (eB P a)) (twistNodeLabels G P x) u'
        (tp P hG p) =
      qRow D hG L γ δ F layer hLayer base (u a) x u p := by
  obtain ⟨hf, hs⟩ := tp_first_of_ne hG p hp0
  have hint1 : Mole.IsInternalLeaf G S (p.firstLeaf hG) := (mem_clRegionalPairs G).mp hp
  have hint2 : Mole.IsInternalLeaf G S (p.secondLeaf hG) := by
    rw [← pair_first_eq_second hG p]; exact (Mole.internal_leaf_pair_iff G S _).mpr hint1
  have h1 : p.firstLeaf hG ≠ P.retained := fun e => hp0 (by rw [← pairOfLeaf_firstLeaf G hG p, e])
  have h2 : p.firstLeaf hG ≠ G.pair P.retained := fun e => hp0 (by
    rw [← pairOfLeaf_firstLeaf G hG p, e, pairOfLeaf_partner])
  have h3 : p.secondLeaf hG ≠ P.retained := by
    rw [← pair_first_eq_second hG p]
    intro e
    apply h2
    have := congrArg G.pair e
    rwa [G.pair_pair] at this
  have h4 : p.secondLeaf hG ≠ G.pair P.retained := by
    rw [← pair_first_eq_second hG p]
    intro e
    apply h1
    have := congrArg G.pair e
    rwa [G.pair_pair, G.pair_pair] at this
  have hlf : ∀ l : GLeaf G.tree, Mole.IsInternalLeaf G S l → l ≠ P.retained → l ≠ G.pair P.retained →
      parentClock (u' (eB P a)) u' (eL P l).toNode = parentClock (u a) u l.toNode := by
    intro l hl hr hq
    have hua : u' (eB P a) = u a := hu a h.block.2.1
    rw [hua, show (eL P l).toNode = naiveNodeEquiv G P l.toNode from (naiveNodeEquiv_leaf G P l).symm]
    exact h.parentClock_naive ((leaf_mem_clRealizationNodes l).mpr hl)
      (Mole.branch_toNode_ne_leaf a l).symm (Mole.branch_toNode_ne_leaf P.lower l).symm
      (fun e => hq (Mole.leaf_toNode_injective e)) (u a) u' u hu
  have hco : ∀ l : GLeaf G.tree, l ≠ P.retained → l ≠ G.pair P.retained →
      cosetDecoration (unitTwistGarden G P) L base (twistNodeLabels G P x) (eL P l).toNode =
        cosetDecoration G L base x l.toNode := by
    intro l hr hq
    unfold cosetDecoration
    have t0 : twistNodeLabels G P x (eL P l).toNode =
        if l = P.retained ∨ l = G.pair P.retained then x P.lower.toNode else x l.toNode :=
      twistNodeLabels_leaf G P x l
    rw [t0, if_neg (by tauto)]
  have hl1 : (p.firstLeaf hG).toNode ≠ a.toNode := (Mole.branch_toNode_ne_leaf a _).symm
  have hl2 : (p.secondLeaf hG).toNode ≠ a.toNode := (Mole.branch_toNode_ne_leaf a _).symm
  have hn1 : (p.firstLeaf hG).toNode ≠ P.lower.toNode := (Mole.branch_toNode_ne_leaf P.lower _).symm
  have hn2 : (p.secondLeaf hG).toNode ≠ P.lower.toNode := (Mole.branch_toNode_ne_leaf P.lower _).symm
  obtain ⟨v1, i1, hv1, hx1⟩ := Flower.V5W.real_child h.block RS ((leaf_mem_clRealizationNodes _).mpr hint1) hl1
  obtain ⟨v2, i2, hv2, hx2⟩ := Flower.V5W.real_child h.block RS ((leaf_mem_clRealizationNodes _).mpr hint2) hl2
  have hq : ∀ i, Flower.V5W.coupleRootParents rowSel.p D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) i =
      Flower.V5W.coupleRootParents rowSel.p D hG layer hLayer p i := by
    intro i
    fin_cases i
    · have hx1' : ((tp P hG p).firstLeaf (unitTwistGarden_plain G P hG)).toNode =
          (eB P v1).child (exchangeChildSlot P.lower.1 P.keep v1.1 i1) := by
        rw [hf]
        exact (naiveNodeEquiv_leaf G P _).symm.trans
          (naiveNodeEquiv_child G P hx1 hn1 (fun e => h2 (Mole.leaf_toNode_injective e)))
      show Flower.V5W.coupleRootParents rowSel.p D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) 0 =
        Flower.V5W.coupleRootParents rowSel.p D hG layer hLayer p 0
      rw [Flower.V5W.coupleRootParents_zero D' (unitTwistGarden_plain G P hG) layer' hLayer' rowSel.p (tp P hG p)
          (eB P v1) _ hx1', Flower.V5W.coupleRootParents_zero D hG layer hLayer rowSel.p p v1 i1 hx1, hlS v1 hv1]
    · have hx2' : ((tp P hG p).secondLeaf (unitTwistGarden_plain G P hG)).toNode =
          (eB P v2).child (exchangeChildSlot P.lower.1 P.keep v2.1 i2) := by
        rw [hs]
        exact (naiveNodeEquiv_leaf G P _).symm.trans
          (naiveNodeEquiv_child G P hx2 hn2 (fun e => h4 (Mole.leaf_toNode_injective e)))
      show Flower.V5W.coupleRootParents rowSel.p D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) 1 =
        Flower.V5W.coupleRootParents rowSel.p D hG layer hLayer p 1
      rw [Flower.V5W.coupleRootParents_one D' (unitTwistGarden_plain G P hG) layer' hLayer' rowSel.p (tp P hG p)
          (eB P v2) _ hx2', Flower.V5W.coupleRootParents_one D hG layer hLayer rowSel.p p v2 i2 hx2, hlS v2 hv2]
  unfold qRow
  rw [VineEst.selCoupleRow_congr L γ δ F D hG layer hLayer p D' (unitTwistGarden_plain G P hG) layer' hLayer'
    (tp P hG p) hC hCi hq, hf, hs, hlf _ hint1 h1 h2, hlf _ hint2 h3 h4, hco _ h1 h2]

include h hu in
theorem tRow_tw (v : GBranch G.tree) (hv : v ∈ S.erase a) (hvb : v ≠ b)
    (hT : nativeChainLayered D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
      nativeChainLayered D hG layer hLayer v)
    (hTi : Flower.V5W.treeIncoh D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
      Flower.V5W.treeIncoh D hG layer hLayer v)
    (hlS : ∀ v ∈ S, layer' (D'.coreBranch (unitTwistGarden_plain G P hG) (eB P v)).toNode =
      layer (D.coreBranch hG v).toNode) :
    tRow D' (unitTwistGarden_plain G P hG) L γ δ F layer' hLayer' base (u' (eB P a)) (twistNodeLabels G P x) u'
        (eB P v) =
      tRow D hG L γ δ F layer hLayer base (u a) x u v := by
  have hvS : v ∈ S := (Finset.mem_erase.mp hv).2
  have hvl : v ≠ P.lower := h.lower ▸ hvb
  have hua : u' (eB P a) = u a := hu a h.block.2.1
  have hpc : parentClock (u' (eB P a)) u' (eB P v).toNode = parentClock (u a) u v.toNode := by
    rw [hua, show (eB P v).toNode = naiveNodeEquiv G P v.toNode from (naiveNodeEquiv_branch G P v).symm]
    exact h.parentClock_naive ((branch_mem_clRealizationNodes v).mpr hvS)
      (fun he => (Finset.mem_erase.mp hv).1 (Mole.branch_toNode_injective he))
      (fun he => hvl (Mole.branch_toNode_injective he)) (Mole.branch_toNode_ne_leaf v _) (u a) u' u hu
  have hva : v.toNode ≠ a.toNode := fun he => (Finset.mem_erase.mp hv).1 (Mole.branch_toNode_injective he)
  obtain ⟨c, i, hc, hxc⟩ := Flower.V5W.real_child h.block RS ((branch_mem_clRealizationNodes v).mpr hvS) hva
  have hxc' : (eB P v).toNode = (eB P c).child (exchangeChildSlot P.lower.1 P.keep c.1 i) :=
    (naiveNodeEquiv_branch G P v).symm.trans
      (naiveNodeEquiv_child G P hxc (fun he => hvl (Mole.branch_toNode_injective he)) (Mole.branch_toNode_ne_leaf v _))
  have hqT : Flower.V5W.treeRootParent rowSel.p D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
      Flower.V5W.treeRootParent rowSel.p D hG layer hLayer v := by
    rw [Flower.V5W.treeRootParent_eq D' (unitTwistGarden_plain G P hG) layer' hLayer' rowSel.p (eB P v) (eB P c) _ hxc',
      Flower.V5W.treeRootParent_eq D hG layer hLayer rowSel.p v c i hxc, hlS c hc]
  unfold tRow cosetDecoration
  rw [VineEst.selTreeRow_congr L γ δ F D hG layer hLayer v D' (unitTwistGarden_plain G P hG) layer' hLayer'
    (eB P v) hT hTi hqT, hpc, hu v hvS, STw.branch_rel x hvl]

end Rows

end WaveTurbulence.VineEstS5B
