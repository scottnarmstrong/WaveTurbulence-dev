/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsO.UnKer
public import WaveTurbulence.Foundations.Flower.MkSlots.IntGeo
public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.FwNode
public import WaveTurbulence.Foundations.Flower.ProtDefs.Defs

/-! # B3s-HELPER8 / UNPIN (part 2): the per-node factors and node weights of an unpinned non-cap slot

On the reconstruction `LG` of a skeleton whose cap trees are single leaves:

* `unNode_cpl_eq_one`: a non-cap native couple carries no capped-stem node (a capped flower below a couple node is a
  leaf of the couple, which makes it a cap couple, `IntGeo.leaf_inCapNative`), so `genΘs` is `1` there;
* `ChStem`, `chF`/`chM` (σ's dyadic filters `2^i L`), `chFu`/`chMu` (the selection shells `Rs j`): the two filter
  layers of a native chain; **`prod_unNode_chain`**: without a selected native vertex, the node product of `unNode`
  at the native resonances is `filtWeight chF … · filtWeight chFu …`;
* **`slotFn_cpl_eq`**: the unpinned non-cap couple slot kernel is B3's `coupleLeavesTopR` (frontier weights, weight
  layers `cplQ`, type profiles);
* **`slotFn_chain_eq`**: the unpinned chain slot kernel without selected native vertex is the leafwise kernel with
  the multiplier `rowTopWeightR (treeQ) · filtWeight chF · filtWeight chFu`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.Stage1W
open WaveTurbulence.Flower.MkSlotsI

namespace WaveTurbulence.Flower.MkSlotsO

variable {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)

/-! ## Couples -/

/-- **No capped stem in a non-cap couple**: the per-node factor is `1` at every node of a non-cap native couple. -/
theorem unNode_cpl_eq_one (hcap : ∀ j ∈ J, (D.garden hS).tree j = TTree.leaf) (q : SourcePair S)
    (hq : ¬ MkSlots.IsCapPair S hS J q) (a : GNode (nativeCoupleLayered D hS layer hLayer q).garden.tree) (x : ℝ) :
    unNode D hS layer hLayer J L σ kSel Rs ((nativeCoupleForest D hS q).nodeEmbedding a) x = 1 := by
  unfold unNode
  rw [ite_eq_right (fun ⟨β, hβ⟩ => un_cpl_not_core D hS layer hLayer q a β hβ)]
  unfold genNW
  by_cases h1 : ((nativeCoupleForest D hS q).nodeEmbedding a).1.2 ∈
      ((layeredReconstruction D hS layer hLayer).garden.tree ((nativeCoupleForest D hS q).nodeEmbedding a).1.1).branching
  · rw [dite_eq_left h1]
    refine ite_eq_right fun h2 => ?_
    exfalso
    obtain ⟨j, hj⟩ := h2
    have hst : OnCapStem (layeredReconstruction D hS layer hLayer) J
        (MkSlots.IntCapT.capT_emb (layeredReconstruction D hS layer hLayer) (nativeCoupleForest D hS q)
          (nativeCoupleForest_closed D hS q) a) := (MkSlotsS.mem_stemSetCap_iff'.1 hj).2.1
    obtain ⟨l, hl, -, -⟩ := un_onCapStem_emb_iff _ _ _ J a hst
    have hfl := (MkSlots.IntCapT.capT_isCapFlower_iff _ _ _ J _ (fun _ => rfl) l).2 hl
    have hin := MkSlots.IntGeo.leaf_inCapNative D hS J hcap _ (Or.inr hfl.2)
    have hin' : MkSlots.InCapNative D hS J (nativeNodeAt D hS (.inl q) l.toNode) := hin
    exact MkSlots.IntGeo.not_inCapNative_of_slot D hS J (.inl q)
      (fun q' hq' => (Sum.inl_injective hq') ▸ hq) l.toNode hin'
  · rw [dite_eq_right h1]

/-! ## Chains -/

/-- A native chain branch whose context node is a non-core capped-stem branch of the reconstruction. -/
def ChStem (b : GBranch S.tree) (c : GBranch (nativeChainLayered D hS layer hLayer b).garden.tree) : Prop :=
  (¬ ∃ β : GBranch S.tree, chainContextNode D hS b c.toNode = (D.coreBranch hS β).toNode) ∧
    ∃ B : GBranch (layeredReconstruction D hS layer hLayer).garden.tree,
      B.toNode = chainContextNode D hS b c.toNode ∧ ∃ j, B ∈ stemSetCap (layeredReconstruction D hS layer hLayer) J j

/-- The first filter layer of a native chain: σ's dyadic filters. -/
def chF (b : GBranch S.tree) : Finset (GBranch (nativeChainLayered D hS layer hLayer b).garden.tree) :=
  Finset.univ.filter fun c => ChStem D hS layer hLayer J b c ∧ (σ (chainContextNode D hS b c.toNode).1.1).isSome

/-- The radii of the first layer: `2^i L`. -/
def chM (b : GBranch S.tree) (c : GBranch (nativeChainLayered D hS layer hLayer b).garden.tree) : ℝ :=
  2 ^ ((σ (chainContextNode D hS b c.toNode).1.1).getD 0) * L

/-- The second filter layer of a native chain: the selection shells. -/
def chFu (b : GBranch S.tree) : Finset (GBranch (nativeChainLayered D hS layer hLayer b).garden.tree) :=
  Finset.univ.filter fun c => ChStem D hS layer hLayer J b c ∧
    (selCap (layeredReconstruction D hS layer hLayer) J kSel (chainContextNode D hS b c.toNode).1.1).isSome

/-- The radii of the second layer: `Rs j`. -/
def chMu (b : GBranch S.tree) (c : GBranch (nativeChainLayered D hS layer hLayer b).garden.tree) : ℝ :=
  Rs (chainContextNode D hS b c.toNode).1.1

/-- No selected vertex as a non-core native branch of the chain of `b`. -/
def NoSelCh (b : GBranch S.tree) : Prop :=
  ∀ c : GBranch (nativeChainLayered D hS layer hLayer b).garden.tree,
    (¬ ∃ β : GBranch S.tree, chainContextNode D hS b c.toNode = (D.coreBranch hS β).toNode) →
    ∀ v ∈ selSetCap (layeredReconstruction D hS layer hLayer) J kSel, v.1 ≠ (chainContextNode D hS b c.toNode).1

/-- **The per-node factor at a native chain branch** splits into the two filter layers. -/
theorem unNode_chain_branch (b : GBranch S.tree) (hsel : NoSelCh D hS layer hLayer J kSel b)
    (c : GBranch (nativeChainLayered D hS layer hLayer b).garden.tree) (x : ℝ) :
    unNode D hS layer hLayer J L σ kSel Rs (chainContextNode D hS b c.toNode) x =
      (if c ∈ chF D hS layer hLayer J σ b then ((chi0 (|x| / chM D hS layer hLayer L σ b c) : ℝ) : ℂ) else 1) *
        (if c ∈ chFu D hS layer hLayer J kSel b then ((chi0 (|x| / chMu D hS layer hLayer Rs b c) : ℝ) : ℂ)
          else 1) := by
  unfold unNode
  by_cases hc : ∃ β : GBranch S.tree, chainContextNode D hS b c.toNode = (D.coreBranch hS β).toNode
  · have h1 : c ∉ chF D hS layer hLayer J σ b := fun h => (Finset.mem_filter.1 h).2.1.1 hc
    have h2 : c ∉ chFu D hS layer hLayer J kSel b := fun h => (Finset.mem_filter.1 h).2.1.1 hc
    rw [ite_eq_left hc, ite_eq_right h1, ite_eq_right h2, mul_one]
  rw [ite_eq_right hc]
  by_cases hB : ∃ B : GBranch (layeredReconstruction D hS layer hLayer).garden.tree,
      B.toNode = chainContextNode D hS b c.toNode ∧ ∃ j, B ∈ stemSetCap (layeredReconstruction D hS layer hLayer) J j
  · obtain ⟨B, hBe, hBs⟩ := hB
    have hst : ChStem D hS layer hLayer J b c := ⟨hc, B, hBe, hBs⟩
    have hB1 : B.1.1 = (chainContextNode D hS b c.toNode).1.1 := by rw [← hBe]; rfl
    have hBsel : B ∉ selSetCap (layeredReconstruction D hS layer hLayer) J kSel := fun hm =>
      hsel c hc B hm (by rw [← hBe]; rfl)
    have hg : genNW (layeredReconstruction D hS layer hLayer) J L σ kSel Rs (chainContextNode D hS b c.toNode) x =
        genNW (layeredReconstruction D hS layer hLayer) J L σ kSel Rs B.toNode x := by rw [hBe]
    rw [hg, un_genNW_toNode, ite_eq_left hBs, ite_eq_right hBsel, mul_one]
    unfold MkSlotsG.radRaw
    rw [MkSlotsT.radProd_append]
    push_cast
    congr 1
    · unfold MkSlotsT.radSigma
      rw [hB1]
      rcases hσ : σ (chainContextNode D hS b c.toNode).1.1 with _ | i
      · have h1 : c ∉ chF D hS layer hLayer J σ b := fun h => by
          have := (Finset.mem_filter.1 h).2.2
          rw [hσ] at this
          exact absurd this (by simp)
        rw [ite_eq_right h1]
        simp [MkSlotsT.radProd]
      · have h1 : c ∈ chF D hS layer hLayer J σ b := Finset.mem_filter.2 ⟨Finset.mem_univ _, hst, by rw [hσ]; rfl⟩
        rw [ite_eq_left h1]
        have hM : chM D hS layer hLayer L σ b c = 2 ^ i * L := by unfold chM; rw [hσ]; rfl
        rw [hM]
        simp [MkSlotsT.radProd]
    · unfold MkSlotsG.shellRad
      rcases hv : selCap (layeredReconstruction D hS layer hLayer) J kSel (chainContextNode D hS b c.toNode).1.1
        with _ | v
      · have h2 : c ∉ chFu D hS layer hLayer J kSel b := fun h => by
          have := (Finset.mem_filter.1 h).2.2
          rw [hv] at this
          exact absurd this (by simp)
        have hne : ¬ ∃ v, selCap (layeredReconstruction D hS layer hLayer) J kSel B.1.1 = some v ∧ v ≠ B := by
          rintro ⟨v', hv', -⟩
          rw [hB1, hv] at hv'
          simp at hv'
        rw [ite_eq_right h2, ite_eq_right hne]
        simp [MkSlotsT.radProd]
      · have h2 : c ∈ chFu D hS layer hLayer J kSel b := Finset.mem_filter.2 ⟨Finset.mem_univ _, hst, by rw [hv]; rfl⟩
        have hvs : v ∈ selSetCap (layeredReconstruction D hS layer hLayer) J kSel :=
          Finset.mem_filter.2 ⟨Finset.mem_univ _, _, hv⟩
        have hyes : ∃ v, selCap (layeredReconstruction D hS layer hLayer) J kSel B.1.1 = some v ∧ v ≠ B :=
          ⟨v, by rw [hB1, hv], fun he => hBsel (he ▸ hvs)⟩
        rw [ite_eq_left h2, ite_eq_left hyes]
        have hMu : chMu D hS layer hLayer Rs b c = Rs B.1.1 := by unfold chMu; rw [hB1]
        rw [hMu]
        simp [MkSlotsT.radProd]
  · have h1 : c ∉ chF D hS layer hLayer J σ b := fun h => hB (Finset.mem_filter.1 h).2.1.2
    have h2 : c ∉ chFu D hS layer hLayer J kSel b := fun h => hB (Finset.mem_filter.1 h).2.1.2
    rw [ite_eq_right h1, ite_eq_right h2, mul_one]
    unfold genNW
    by_cases hb : (chainContextNode D hS b c.toNode).1.2 ∈
        ((layeredReconstruction D hS layer hLayer).garden.tree (chainContextNode D hS b c.toNode).1.1).branching
    · rw [dite_eq_left hb]
      exact ite_eq_right fun hs => absurd ⟨⟨_, hb⟩, rfl, hs⟩ hB
    · rw [dite_eq_right hb]

/-- **The node product of `unNode` on a native chain** is the product of the two filter layers. -/
theorem prod_unNode_chain (b : GBranch S.tree) (hsel : NoSelCh D hS layer hLayer J kSel b)
    (k' : GNode (nativeChainLayered D hS layer hLayer b).garden.tree → Mom d) :
    ∏ a, unNode D hS layer hLayer J L σ kSel Rs (chainContextNode D hS b a) (MkSlotsS.omegaAt k' a) =
      ProtDefs.filtWeight (chF D hS layer hLayer J σ b) (fun _ => false) (chM D hS layer hLayer L σ b) k' *
        ProtDefs.filtWeight (chFu D hS layer hLayer J kSel b) (fun _ => false) (chMu D hS layer hLayer Rs b) k' := by
  have h1 : ∀ a, unNode D hS layer hLayer J L σ kSel Rs (chainContextNode D hS b a) (MkSlotsS.omegaAt k' a) =
      MkSlotsT.brExt (fun c => unNode D hS layer hLayer J L σ kSel Rs (chainContextNode D hS b c.toNode)
        (omegaNode (nativeChainLayered D hS layer hLayer b).garden k' c)) a := by
    intro a
    unfold MkSlotsT.brExt
    split_ifs with hb
    · exact congrArg _ (un_omegaAt_of_branch k' a hb)
    · unfold unNode
      split_ifs with hc
      · rfl
      · unfold genNW
        by_cases hb' : (chainContextNode D hS b a).1.2 ∈
            ((layeredReconstruction D hS layer hLayer).garden.tree (chainContextNode D hS b a).1.1).branching
        · exact absurd (un_chain_branch_of_branch D hS b a hb' fun he => hc ⟨b, he⟩) hb
        · rw [dite_eq_right hb']
  rw [Finset.prod_congr rfl (fun a _ => h1 a), MkSlotsT.prod_brExt]
  refine (Finset.prod_congr rfl fun c _ => unNode_chain_branch D hS layer hLayer J L σ kSel Rs b hsel c _).trans ?_
  refine Finset.prod_mul_distrib.trans ?_
  unfold ProtDefs.filtWeight
  congr 1
  · refine (Finset.prod_ite_mem _ _ _).trans ?_
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact Finset.prod_congr (Finset.univ_inter _) fun _ _ => rfl
  · refine (Finset.prod_ite_mem _ _ _).trans ?_
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact Finset.prod_congr (Finset.univ_inter _) fun _ _ => rfl

/-! ## The slot kernels -/

variable (γ δ : ℝ) (p : ℕ) (s : ℝ) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (roots : Fin w → (Fin d → ℤ))
  (Rf : Fin w → Option ℝ) (dag : Option (Fin w → Fin 3 → Mom d)) (fixG : GBranch (D.forest hS) → Option ℝ)

/-- **The unpinned non-cap couple slot kernel is `coupleLeavesTopR`** (frontier weights, weight layers `cplQ`). -/
theorem slotFn_cpl_eq (hcap : ∀ j ∈ J, (D.garden hS).tree j = TTree.leaf) (q : SourcePair S)
    (hq : ¬ MkSlots.IsCapPair S hS J q) (hfix : ∀ qb, MkSlots.fixNative D hS fixG (.inl q) qb = none)
    (ts : Fin 2 → ℝ) (k : Mom d) :
    MkSlotsB.slotFnGWFRL D hS L γ δ (MkSlots.anchProfiles J (layeredReconstruction D hS layer hLayer) h L roots)
        (MkSlots.chainW D hS layer hLayer L γ δ p s J Rf dag) (genΘs D hS layer hLayer J L σ kSel Rs) layer hLayer
        fixG (.inl q) ts k =
      coupleLeavesTopR L γ δ p (Stage1WNoVine.cplG D hS (fun j => frontierG (Rf j)) q)
        (Stage1WNoVine.cplQ D hS layer hLayer p q 0) (Stage1WNoVine.cplQ D hS layer hLayer p q 1)
        (nativeCoupleLayered D hS layer hLayer q)
        (RegRedLeaf.nativeCoupleProfiles D hS (typeProfiles (layeredReconstruction D hS layer hLayer) h) q)
        (ts 0) (ts 1) k := by
  rw [slotFnGWFRL_genΘs_inl D hS layer hLayer J L σ kSel Rs γ δ _ _ fixG q hfix ts k]
  have hnc := MkSlots.IntGeo.not_inCapNative_of_slot D hS J (.inl q)
    (fun q' hq' => (Sum.inl_injective hq') ▸ hq)
  have hA : (fun a : GNode (nativeCoupleLayered D hS layer hLayer q).garden.tree =>
      MkSlots.anchProfiles J (layeredReconstruction D hS layer hLayer) h L roots
        ((nativeCoupleForest D hS q).nodeEmbedding a).1) =
      fun a => RegRedLeaf.nativeCoupleProfiles D hS (typeProfiles (layeredReconstruction D hS layer hLayer) h) q
        a.1 := by
    funext a
    refine (MkSlots.IntGeo.anchProfiles_eq D hS layer hLayer J hcap h L roots (nativeNodeAt D hS (.inl q) a)
      (hnc a)).trans ?_
    unfold RegRedLeaf.nativeCoupleProfiles
    split_ifs with hh
    · rfl
    · exact absurd a.2 hh
  have hm : (fun k' : GNode (nativeCoupleLayered D hS layer hLayer q).garden.tree → Mom d =>
      (∏ a, MkSlots.chainW D hS layer hLayer L γ δ p s J Rf dag ((nativeCoupleForest D hS q).nodeEmbedding a)
        (k' a)) *
        ∏ a, unNode D hS layer hLayer J L σ kSel Rs ((nativeCoupleForest D hS q).nodeEmbedding a)
          (MkSlotsS.omegaAt k' a)) =
      rowTopWeightR p (Stage1WNoVine.cplG D hS (fun j => frontierG (Rf j)) q) (nativeCoupleLayered D hS layer hLayer q)
        ![Stage1WNoVine.cplQ D hS layer hLayer p q 0, Stage1WNoVine.cplQ D hS layer hLayer p q 1] := by
    funext k'
    have e1 : (∏ a, unNode D hS layer hLayer J L σ kSel Rs ((nativeCoupleForest D hS q).nodeEmbedding a)
        (MkSlotsS.omegaAt k' a)) = 1 :=
      Finset.prod_eq_one fun a _ => unNode_cpl_eq_one D hS layer hLayer J L σ kSel Rs hcap q hq a _
    have e2 : (∏ a, MkSlots.chainW D hS layer hLayer L γ δ p s J Rf dag ((nativeCoupleForest D hS q).nodeEmbedding a)
        (k' a)) = ∏ a, Stage1WNoVine.fwNode (layeredReconstruction D hS layer hLayer) p (fun j => frontierG (Rf j))
          ((nativeCoupleForest D hS q).nodeEmbedding a) (k' a) :=
      Finset.prod_congr rfl fun a _ => MkSlots.IntGeo.chainW_eq_fwNode D hS layer hLayer J hcap L γ δ p s Rf dag
        (nativeNodeAt D hS (.inl q) a) (k' a) (hnc a)
    rw [e1, mul_one, e2]
    refine (Stage1WNoVine.prod_fwNode_embed (layeredReconstruction D hS layer hLayer)
      (nativeCoupleLayered D hS layer hLayer q) (fun a => (nativeCoupleForest D hS q).nodeEmbedding a)
      (fun j => ((nativeCoupleForest D hS q).root j).1) (fun a => rfl) (fun a => rfl) p _ k').trans ?_
    rw [← Stage1WNoVine.fin2_vec (Stage1WNoVine.cplQ D hS layer hLayer p q)]
    rfl
  rw [hA, hm]
  rfl

/-- **The unpinned chain slot kernel without selected native vertex** is the leafwise kernel with the multiplier
`rowTopWeightR (treeQ) · filtWeight chF · filtWeight chFu`. -/
theorem slotFn_chain_eq (hcap : ∀ j ∈ J, (D.garden hS).tree j = TTree.leaf) (b : GBranch S.tree)
    (hsel : NoSelCh D hS layer hLayer J kSel b) (hfix : ∀ qb, MkSlots.fixNative D hS fixG (.inr b) qb = none)
    (ts : Fin 2 → ℝ) (k : Mom d) :
    MkSlotsB.slotFnGWFRL D hS L γ δ (MkSlots.anchProfiles J (layeredReconstruction D hS layer hLayer) h L roots)
        (MkSlots.chainW D hS layer hLayer L γ δ p s J Rf dag) (genΘs D hS layer hLayer J L σ kSel Rs) layer hLayer
        fixG (.inr b) ts k =
      kernelLeavesW L γ δ (nativeChainLayered D hS layer hLayer b)
        (RegRedLeaf.nativeChainProfiles D hS (typeProfiles (layeredReconstruction D hS layer hLayer) h) b)
        (fun _ => ts 0) (ts 1) k (fun _ => 0) 0
        (fun k' => rowTopWeightR p (fun _ => Stage1WNoVine.treeG D (fun j => frontierG (Rf j)) b)
            (nativeChainLayered D hS layer hLayer b) ![Stage1WNoVine.treeQ D hS layer hLayer p b] k' *
          (ProtDefs.filtWeight (chF D hS layer hLayer J σ b) (fun _ => false) (chM D hS layer hLayer L σ b) k' *
            ProtDefs.filtWeight (chFu D hS layer hLayer J kSel b) (fun _ => false) (chMu D hS layer hLayer Rs b)
              k')) := by
  rw [slotFnGWFRL_genΘs_inr D hS layer hLayer J L σ kSel Rs γ δ _ _ fixG b hfix ts k]
  have hnc := MkSlots.IntGeo.not_inCapNative_of_slot D hS J (.inr b) (fun q' hq' => absurd hq' (by simp))
  have hA : (fun a : GNode (nativeChainLayered D hS layer hLayer b).garden.tree =>
      MkSlots.anchProfiles J (layeredReconstruction D hS layer hLayer) h L roots (chainContextNode D hS b a).1) =
      fun a => RegRedLeaf.nativeChainProfiles D hS (typeProfiles (layeredReconstruction D hS layer hLayer) h) b
        a.1 := by
    funext a
    refine (MkSlots.IntGeo.anchProfiles_eq D hS layer hLayer J hcap h L roots (nativeNodeAt D hS (.inr b) a)
      (hnc a)).trans ?_
    unfold RegRedLeaf.nativeChainProfiles
    split_ifs with hh
    · rfl
    · exact absurd a.2 hh
  have hm : (fun k' : GNode (nativeChainLayered D hS layer hLayer b).garden.tree → Mom d =>
      (∏ a, MkSlots.chainW D hS layer hLayer L γ δ p s J Rf dag (chainContextNode D hS b a) (k' a)) *
        ∏ a, unNode D hS layer hLayer J L σ kSel Rs (chainContextNode D hS b a) (MkSlotsS.omegaAt k' a)) =
      fun k' => rowTopWeightR p (fun _ => Stage1WNoVine.treeG D (fun j => frontierG (Rf j)) b)
            (nativeChainLayered D hS layer hLayer b) ![Stage1WNoVine.treeQ D hS layer hLayer p b] k' *
          (ProtDefs.filtWeight (chF D hS layer hLayer J σ b) (fun _ => false) (chM D hS layer hLayer L σ b) k' *
            ProtDefs.filtWeight (chFu D hS layer hLayer J kSel b) (fun _ => false) (chMu D hS layer hLayer Rs b)
              k') := by
    funext k'
    have e2 : (∏ a, MkSlots.chainW D hS layer hLayer L γ δ p s J Rf dag (chainContextNode D hS b a) (k' a)) =
        ∏ a, Stage1WNoVine.fwNode (layeredReconstruction D hS layer hLayer) p (fun j => frontierG (Rf j))
          (chainContextNode D hS b a) (k' a) :=
      Finset.prod_congr rfl fun a _ => MkSlots.IntGeo.chainW_eq_fwNode D hS layer hLayer J hcap L γ δ p s Rf dag
        (nativeNodeAt D hS (.inr b) a) (k' a) (hnc a)
    rw [prod_unNode_chain D hS layer hLayer J L σ kSel Rs b hsel k', e2]
    congr 1
    refine (Stage1WNoVine.prod_fwNode_embed (layeredReconstruction D hS layer hLayer)
      (nativeChainLayered D hS layer hLayer b) (chainContextNode D hS b) (fun _ => inflatedPosition S D.tree b.toNode)
      (fun a => rfl) (fun a => rfl) p _ k').trans ?_
    have e : Stage1WNoVine.embQ (layeredReconstruction D hS layer hLayer) (nativeChainLayered D hS layer hLayer b)
        (chainContextNode D hS b) (fun _ => inflatedPosition S D.tree b.toNode) p =
        ![Stage1WNoVine.treeQ D hS layer hLayer p b] := Stage1WNoVine.fin1_vec _
    rw [e]
    rfl
  rw [hA, hm]
  rfl

end WaveTurbulence.Flower.MkSlotsO
