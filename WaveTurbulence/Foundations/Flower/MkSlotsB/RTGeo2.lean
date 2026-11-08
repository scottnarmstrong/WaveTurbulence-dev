/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.RTGeo1
public import WaveTurbulence.Foundations.Flower.MkSlotsB.RTDefs
public import WaveTurbulence.Foundations.Flower.MkSlotsI.SlotObl
public import WaveTurbulence.Foundations.Flower.MkSlotsO.RootTraceHyp
public import WaveTurbulence.Foundations.Flower.MkSlots.CapConv

/-! # B3s-HELPER3 B5(ii) geometry (R188), part 2: off-stem facts shared by both variants, and the chain fields

Shared (any slot whose native nodes lie below roots with no capped flower below): `genNW_eq_one`,
`selNative_eq_empty_of`, `clkPin_mem_Icc` (pinned clocks in their windows), `anchProfiles_eq_type_of`.

The fields of `RTChain` for a root-trace chain slot `.inr γ'` (`γ'` the skeleton child `i` of `β`, nontrivial chain,
top `r` = child `i` of the core capped flower parent `F = core β`, `dChild i`): `rtc_two_le` … `rtc_front_card`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open Set
open WaveTurbulence WaveTurbulence.LGSpine TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Represents
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineAlign
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.ProtDefs
open WaveTurbulence.Flower.Stage1WNoVine WaveTurbulence.Flower.Stage1W
open WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlots.IntRest

namespace WaveTurbulence.Flower.MkSlotsB

/-! ## Shared off-stem facts -/

section Shared
variable {w : ℕ}

/-- The general stem node weight is `1` off the capped stems. -/
theorem genNW_eq_one (LG : LayeredGarden w) (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ)
    (Rs : Fin w → ℝ) (z : GNode LG.garden.tree) (x : ℝ) (hz : ¬ OnCapStem LG J z) :
    MkSlotsI.genNW LG J L σ kSel Rs z x = 1 := by
  have h2 : ∀ h1 : z.1.2 ∈ (LG.garden.tree z.1.1).branching,
      ¬ ∃ j, (⟨z.1, h1⟩ : GBranch LG.garden.tree) ∈ stemSetCap LG J j :=
    fun _ ⟨_, hj⟩ => hz (ProtGeo.mem_stemSetCap.mp hj).2.1
  unfold MkSlotsI.genNW
  split_ifs with h1 h3 <;> first | rfl | exact absurd h3 (h2 h1)

/-- A selected vertex is on a capped stem in a tree with a selection. -/
theorem selSetCap_onStem {LG : LayeredGarden w} {J : Finset (Fin w)} {kSel : Fin w → Option ℕ}
    {v : GBranch LG.garden.tree} (hv : v ∈ selSetCap LG J kSel) :
    (kSel v.1.1).isSome ∧ OnCapStem LG J v.toNode :=
  ⟨(ProtGeo.selSetCap_spec hv).1, (ProtGeo.selSetCap_spec hv).2.2.1⟩

/-- A pinned clock lies in its layer window. -/
theorem clkPin_mem_Icc {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) {J : Finset (Fin w)} {p : ℕ}
    {pat : Fin w → FixPat} {t s : ℝ} (hG : CapGeo (layeredReconstruction D hS layer hLayer) J p)
    (hpat : CapPatValid (layeredReconstruction D hS layer hLayer) J pat p)
    (hroot : ∀ j ∉ J, ∃ ℓ : GLeaf (layeredReconstruction D hS layer hLayer).garden.tree,
      IsCapFlower (layeredReconstruction D hS layer hLayer) J ℓ ∧ ℓ.1.1 = j)
    (hs : s ∈ Ioo (p : ℝ) t) (ht : t ∈ Ioo (p : ℝ) (p + 1)) (y : ClkSrc S) (v : ℝ)
    (h : MkSlotsI.clkPin (fun _ => t) (fixCore D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s)) y =
      some v) :
    v ∈ Icc (clkLayer p (fun b => layer (D.coreBranch hS b).toNode) y : ℝ)
      (clkLayer p (fun b => layer (D.coreBranch hS b).toNode) y + 1) := by
  rcases y with j | b
  · simp only [MkSlotsI.clkPin, Option.some.injEq] at h
    subst h
    exact ⟨ht.1.le, ht.2.le⟩
  · have h' : fixCap (layeredReconstruction D hS layer hLayer) J pat t s (D.coreBranch hS b) = some v := h
    have hv := fixCap_val hG hpat hroot hs ht.2 h'
    exact ⟨hv.1.le, hv.2.1⟩

end Shared

/-! ## The chain fields -/

section Chain
variable {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat)
  (t s : ℝ) (hR : RTRec (p := p) a J pat)
  (β γ' : GBranch a.prime.skeleton.tree) (i : Fin 3) (r : GBranch (a.prime.data.forest a.prime.prime.1))
  (hF : IsCapFlowerParent (recLG a) J (a.prime.data.coreBranch a.prime.prime.1 β))
  (hpat : pat β.1.1 = FixPat.dChild i)
  (hr : r.toNode = (a.prime.data.coreBranch a.prime.prime.1 β).child i)
  (hnc : ∀ β' : GBranch a.prime.skeleton.tree, (a.prime.data.coreBranch a.prime.prime.1 β').toNode ≠ r.toNode)
  (hγ : γ'.toNode = β.child i) (h0 : (a.prime.data.tree γ').lonePath ≠ [])
  (hr1 : r.1 = inflatedPosition a.prime.skeleton a.prime.data.tree γ'.toNode)

include hR hF hr in
theorem rtc_noFlower : NoFlowerBelow (recLG a) J r.toNode := noFlowerBelow_child hR.geo hF i hr

include hr1 in
/-- Every node of the native chain lies below its top `r`. -/
theorem rtc_isDesc (z : GNode (decodedTree (a.prime.data.tree γ') (nodeSign a.prime.skeleton.sig γ'.1)).tree) :
    r.toNode.IsDesc (chainContextNode a.prime.data a.prime.prime.1 γ' z) := by
  refine ⟨?_, ?_⟩
  · show r.1.1 = (inflatedPosition a.prime.skeleton a.prime.data.tree γ'.toNode).1
    rw [hr1]
  · show r.1.2 <+: (inflatedPosition a.prime.skeleton a.prime.data.tree γ'.toNode).2 ++ z.1.2
    rw [hr1]
    exact List.prefix_append _ _

include hr1 in
theorem rtc_top_node : chainContextNode a.prime.data a.prime.prime.1 γ' (GNode.root _ 0) = r.toNode := by
  apply Subtype.ext
  show addrExt (inflatedPosition a.prime.skeleton a.prime.data.tree γ'.toNode) [] = r.1
  rw [hr1]
  simp [addrExt]

include hR hF hpat hr in
theorem rtc_fix_r : fixCap (recLG a) J pat t s r = some s := by
  have hp : pat (a.prime.data.coreBranch a.prime.prime.1 β).1.1 = FixPat.dChild i := by
    rw [show (a.prime.data.coreBranch a.prime.prime.1 β).1.1 = β.1.1 from
      inflatedPosition_index a.prime.skeleton a.prime.data.tree β.toNode]
    exact hpat
  exact fixCap_child_dChild hR.geo t s hF hp hr

include h0 in
theorem rtc_two_le : 2 ≤ (a.prime.data.tree γ').lonePath.length :=
  two_le_lonePath (fun h => h0 (by rw [h]; rfl))

theorem rtc_wf : (a.prime.data.tree γ').wf = true := a.prime.data.tree_wf γ'

include hR hF hpat hr hr1 in
theorem rtc_pins : ∀ q : GBranch (nativeChainLayered a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) γ').garden.tree,
    MkSlots.fixNative a.prime.data a.prime.prime.1 (fixCap (recLG a) J pat t s) (.inr γ') q =
      MkSlotsO.rootPins (fun _ => True) s q := by
  intro q
  show fixCap (recLG a) J pat t s (nativeBr a.prime.data a.prime.prime.1 (.inr γ') q) = _
  unfold MkSlotsO.rootPins
  have haddr : (nativeBr a.prime.data a.prime.prime.1 (.inr γ') q).1 =
      addrExt (inflatedPosition a.prime.skeleton a.prime.data.tree γ'.toNode) q.1.2 := rfl
  by_cases hq : q.1.2 = []
  · have he : nativeBr a.prime.data a.prime.prime.1 (.inr γ') q = r := by
      apply Subtype.ext
      rw [haddr, hq, hr1]
      simp [addrExt]
    rw [he, rtc_fix_r a J pat t s hR β i r hF hpat hr]
    simp [hq]
  · have hn : ¬ (q.1.2 = [] ∧ True) := fun h => hq h.1
    simp only [hn, ↓reduceIte]
    cases hc : fixCap (recLG a) J pat t s (nativeBr a.prime.data a.prime.prime.1 (.inr γ') q) with
    | none => rfl
    | some v =>
      exfalso
      have hd : r.toNode.IsDesc (nativeBr a.prime.data a.prime.prime.1 (.inr γ') q).toNode := by
        refine ⟨?_, ?_⟩
        · show r.1.1 = (nativeBr a.prime.data a.prime.prime.1 (.inr γ') q).1.1
          rw [haddr, hr1]; rfl
        · show r.1.2 <+: (nativeBr a.prime.data a.prime.prime.1 (.inr γ') q).1.2
          rw [haddr, hr1]; exact List.prefix_append _ _
      have he := pinned_below_eq (rtc_noFlower a J pat hR β i r hF hr) hd (by rw [hc]; rfl)
      have hv := congrArg (fun z : GNode (a.prime.data.forest a.prime.prime.1) => z.1.2) he
      change (nativeBr a.prime.data a.prime.prime.1 (.inr γ') q).1.2 = r.1.2 at hv
      rw [haddr, hr1] at hv
      simp only [addrExt] at hv
      exact hq (List.append_right_eq_self.mp hv)

include hR in
theorem rtc_layer_le : ∀ z, (nativeChainLayered a.prime.data a.prime.prime.1 (sourceLayer a)
    (sourceLayer_isLayering a) γ').layer z ≤ p := fun _ => hR.geo.layer_le _

include hR hF hpat hr hr1 in
theorem rtc_layer_root : (nativeChainLayered a.prime.data a.prime.prime.1 (sourceLayer a)
    (sourceLayer_isLayering a) γ').layer (GNode.root _ 0) = p := by
  show (recLG a).layer (chainContextNode a.prime.data a.prime.prime.1 γ' (GNode.root _ 0)) = p
  rw [rtc_top_node a γ' r hr1]
  exact fixCap_layer hR.geo hR.patv hR.root (rtc_fix_r a J pat 0 0 hR β i r hF hpat hr)

theorem rtc_layer_lone : ∀ z : GNode (nativeChainLayered a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) γ').garden.tree, z.1.2 = (a.prime.data.tree γ').lonePath →
    (nativeChainLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) γ').layer z =
      sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 γ').toNode := by
  intro z hz
  show sourceLayer a (chainContextNode a.prime.data a.prime.prime.1 γ' z) = _
  congr 1
  apply Subtype.ext
  show addrExt (inflatedPosition a.prime.skeleton a.prime.data.tree γ'.toNode) z.1.2 = a.prime.data.corePosition γ'
  rw [hz]
  rfl

include hR in
theorem rtc_amb : ProtAmbient p (a.prime.data.tree γ')
    (nativeChainLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) γ') := by
  refine ⟨2 * R, recLG a, inflatedPosition a.prime.skeleton a.prime.data.tree γ'.toNode,
    node3 (fun i => a.prime.data.inflateNode a.prime.prime.1 (γ'.child i)), hR.can,
    LFTwist.reconstruction_chainEmb a.prime.data a.prime.prime.1 (a.prime.data.garden_decodes a.prime.prime.1) γ',
    ?_, ?_⟩
  · show nodeSign a.prime.skeleton.sig (inflatedPosition a.prime.skeleton a.prime.data.tree γ'.toNode) =
      nodeSign a.prime.skeleton.sig γ'.1
    exact inflatedPosition_sign _ _ _
  · intro z
    show sourceLayer a (chainContextNode a.prime.data a.prime.prime.1 γ' z) = _
    exact (Links.layerAt_node (recLG a) (chainContextNode a.prime.data a.prime.prime.1 γ' z)).symm

include hR hF hr hr1 in
theorem rtc_genΘs_one : ∀ {d : ℕ} (L : ℝ) (σ kSel : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (k : Mom d)
    (κ : NativeRelativeDecoration a.prime.data a.prime.prime.1 d (.inr γ')),
    MkSlotsI.genΘs a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J L σ kSel Rs (.inr γ')
      k κ = 1 := by
  intro d L σ kSel Rs k κ
  refine Finset.prod_eq_one fun z _ => ?_
  split_ifs
  · rfl
  · exact genNW_eq_one _ J L σ kSel Rs _ _
      ((rtc_noFlower a J pat hR β i r hF hr).not_onCapStem (rtc_isDesc a γ' r hr1 z))

include hR hF hr hr1 in
theorem rtc_selNative_empty : ∀ kSel : Fin (2 * R) → Option ℕ,
    MkSlotsS.selNative a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel (.inr γ') = ∅ := by
  intro kSel
  refine Finset.filter_eq_empty_iff.mpr fun v hv => ?_
  rintro ⟨z, -, hz⟩
  have hst := (selSetCap_onStem hv).2
  have he : v.toNode = chainContextNode a.prime.data a.prime.prime.1 γ' z := Subtype.ext hz
  rw [he] at hst
  exact (rtc_noFlower a J pat hR β i r hF hr).not_onCapStem (rtc_isDesc a γ' r hr1 z) hst

include hR in
theorem rtc_chainW_eq : ∀ {d : ℕ} (L γ δ s' : ℝ) (Rf : Fin (2 * R) → Option ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom d))
    (z : GNode (decodedTree (a.prime.data.tree γ') (nodeSign a.prime.skeleton.sig γ'.1)).tree) (x : Mom d),
    MkSlots.chainW a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) L γ δ p s' J Rf dag
        (chainContextNode a.prime.data a.prime.prime.1 γ' z) x =
      fwNode (recLG a) p (fun j => frontierG (Rf j)) (chainContextNode a.prime.data a.prime.prime.1 γ' z) x := by
  intro d L γ δ s' Rf dag z x
  refine IntGeo.chainW_eq_fwNode a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J hR.cap
    L γ δ p s' Rf dag _ x ?_
  rintro ⟨q, hq, -⟩
  have h1 : slotOf a.prime.data a.prime.prime.1 (chainContextNode a.prime.data a.prime.prime.1 γ' z) = .inr γ' :=
    slotOf_nativeNodeAt a.prime.data a.prime.prime.1 (.inr γ') z
  rw [h1] at hq
  exact Sum.inr_ne_inl hq

include hγ in
theorem rtc_argSrc0 : argSrc a.prime.prime.1 (.inr γ') 0 = .inr β := by
  show clkOfNode a.prime.skeleton γ'.toNode = _
  rw [hγ]
  unfold clkOfNode
  rw [nodeToSlot_child]

include hF hγ in
theorem rtc_clk0 : MkSlotsI.clkPin (fun _ => t)
    (MkSlots.fixCore a.prime.data a.prime.prime.1 (fixCap (recLG a) J pat t s)) (argSrc a.prime.prime.1 (.inr γ') 0) =
      some s := by
  rw [rtc_argSrc0 a β γ' i hγ]
  show fixCap (recLG a) J pat t s (a.prime.data.coreBranch a.prime.prime.1 β) = some s
  unfold fixCap
  simp only [hF, ↓reduceIte]

include hR hF hγ in
theorem rtc_clkLayer0 : clkLayer p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
    (argSrc a.prime.prime.1 (.inr γ') 0) = p := by
  rw [rtc_argSrc0 a β γ' i hγ]
  exact layer_capFlowerParent hR.geo hF

include hR hF hr hnc hr1 in
theorem rtc_free : MkSlots.fixCore a.prime.data a.prime.prime.1 (fixCap (recLG a) J pat t s) γ' = none := by
  show fixCap (recLG a) J pat t s (a.prime.data.coreBranch a.prime.prime.1 γ') = none
  cases hc : fixCap (recLG a) J pat t s (a.prime.data.coreBranch a.prime.prime.1 γ') with
  | none => rfl
  | some v =>
    exfalso
    have hd : r.toNode.IsDesc (a.prime.data.coreBranch a.prime.prime.1 γ').toNode := by
      refine ⟨?_, ?_⟩
      · show r.1.1 = (a.prime.data.corePosition γ').1
        rw [hr1]; rfl
      · show r.1.2 <+: (a.prime.data.corePosition γ').2
        rw [hr1]; exact List.prefix_append _ _
    exact hnc γ' (pinned_below_eq (rtc_noFlower a J pat hR β i r hF hr) hd (by rw [hc]; rfl))

include hγ in
theorem rtc_nonroot : γ'.1.2 ≠ [] := by
  have h := congrArg (fun z : GNode a.prime.skeleton.tree => z.1.2) hγ
  change γ'.1.2 = β.1.2 ++ [i] at h
  rw [h]; simp

include hpat hγ in
theorem rtc_notSelAdj : ∀ kSel : Fin (2 * R) → Option ℕ, (∀ j, (kSel j).isSome → pat j = FixPat.plain) →
    ¬ MkSlotsI.SelAdj a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel (.inr γ') := by
  intro kSel hk ⟨k, β'', hsrc, v, hv, hve⟩
  have hβ'' : β''.1.1 = β.1.1 := by
    have hk : k = 0 ∨ k = 1 := by fin_cases k <;> simp
    rcases hk with rfl | rfl
    · rw [rtc_argSrc0 a β γ' i hγ] at hsrc
      have e := Sum.inr_injective hsrc
      rw [← e]
    · have h2 : argSrc a.prime.prime.1 (.inr γ') 1 = .inr γ' := rfl
      rw [h2] at hsrc
      have e := Sum.inr_injective hsrc
      rw [← e]
      exact congrArg (fun z : GNode a.prime.skeleton.tree => z.1.1) hγ
  have hvt : v.1.1 = β.1.1 := by
    rw [hve]
    exact (inflatedPosition_index a.prime.skeleton a.prime.data.tree β''.toNode).trans hβ''
  have := hk _ (selSetCap_onStem hv).1
  rw [hvt, hpat] at this
  exact absurd this (by simp)

include hR hF hpat hr hnc hr1 in
theorem rtc_prot : ∀ kSel : Fin (2 * R) → Option ℕ, MkSlotsI.HasProtNative a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a) (protI (recLG a) J pat t s kSel) (.inr γ') := by
  intro kSel
  refine ⟨(GNode.root _ 0 : GNode (decodedTree (a.prime.data.tree γ') (nodeSign a.prime.skeleton.sig γ'.1)).tree),
    ?_, r.toNode, ?_, ?_⟩
  · intro β' he
    have h1 : nativeNodeAt a.prime.data a.prime.prime.1 (.inr γ') (GNode.root _ 0) = r.toNode :=
      rtc_top_node a γ' r hr1
    exact hnc β' (he.symm.trans h1)
  · exact mem_protI_of_fixCap (by rw [rtc_fix_r a J pat t s hR β i r hF hpat hr]; rfl)
  · exact congrArg Subtype.val (rtc_top_node a γ' r hr1).symm

include hR hF hr hr1 in
theorem rtc_leafwise : ∀ {d : ℕ} (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom d → ℝ) (L : ℝ)
    (roots : Fin (2 * R) → (Fin d → ℤ)) (b : ℝ), 0 ≤ b →
    (∀ q ≤ p, ∀ j j', SNormR (40 * d) (40 * d) (h q j j') ≤ ENNReal.ofReal b) →
    LeafwiseControlled (nativeChainLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) γ')
      (MkSlots.capProfiles (nativeChainLayered a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a) γ')
        (fun z => MkSlots.anchProfiles J (MkSlots.recLG a) h L roots (chainContextNode a.prime.data a.prime.prime.1 γ' z).1))
      (nativeChainB a.prime.data a.prime.prime.1 (fun _ => b.toNNReal) γ') := by
  intro d h L roots b hb0 hb ℓ hℓ
  rw [MkSlots.capProfiles_leaf]
  have hmark := (Finset.mem_filter.mp hℓ).2.2
  have hne : ℓ.1.2 ≠ (a.prime.data.tree γ').lonePath := by
    intro he
    have hm := (decodedTree_decodes (a.prime.data.tree γ') (nodeSign a.prime.skeleton.sig γ'.1)).2.1 ℓ
    change (decodedTree (a.prime.data.tree γ') (nodeSign a.prime.skeleton.sig γ'.1)).mark ℓ = none at hmark
    rw [hm] at hmark
    simp [he] at hmark
  let e : GLeaf (recLG a).garden.tree := chainContextLeaf a.prime.data a.prime.prime.1 γ' ⟨ℓ, hne⟩
  have he : e.toNode = chainContextNode a.prime.data a.prime.prime.1 γ' ℓ.toNode :=
    chainContextLeaf_toNode a.prime.data a.prime.prime.1 γ' ⟨ℓ, hne⟩
  have hd : r.toNode.IsDesc e.toNode := he ▸ rtc_isDesc a γ' r hr1 ℓ.toNode
  have hNF := rtc_noFlower a J pat hR β i r hF hr
  have h1 : e.1.1 ∉ J := by
    have e1 : e.1.1 = r.1.1 := hd.1.symm
    rw [e1]
    exact branch_not_cap hR.geo r
  have h2 : ((recLG a).garden.pair e).1.1 ∉ J := fun hJ => hNF e ⟨h1, hJ⟩ hd
  show SNormR (40 * d) (40 * d) (MkSlots.anchProfiles J (recLG a) h L roots e.1) ≤ _
  unfold MkSlots.anchProfiles
  rw [pairTrees_leaf]
  simp only [h1, h2, ↓reduceIte]
  rw [typeProfiles_leaf]
  have hB : (nativeChainB a.prime.data a.prime.prime.1 (fun _ => b.toNNReal) γ' ℓ.1 : ℝ) = b := by
    have hmem : ℓ.1.2 ∈ ((decodedTree (a.prime.data.tree γ') (nodeSign a.prime.skeleton.sig γ'.1)).tree ℓ.1.1).nodes :=
      TTree.leaves_subset_nodes _ ℓ.2
    unfold nativeChainB
    simp only [hmem, ↓reduceDIte]
    exact Real.coe_toNNReal b hb0
  rw [hB]
  exact hb _ (hR.geo.layer_le _) _ _

theorem rtc_front_card : (frontNat a (chainContextNode a.prime.data a.prime.prime.1 γ') p).card ≤
    slotNr a.prime.data a.prime.prime.1 (.inr γ') := by
  unfold frontNat slotNr
  exact Finset.card_le_card (@Finset.monotone_filter_right _ _ _ _ _ _ fun z _ hz => hz.1)

end Chain

end WaveTurbulence.Flower.MkSlotsB
