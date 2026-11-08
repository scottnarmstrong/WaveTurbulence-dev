/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.RTGeo2

/-! # B3s-HELPER3 B5(ii) geometry (R188), part 3: the fields of `RTCouple` for a non-cap leaf pair

For a leaf-pair slot `.inl q'` that is not a cap pair, neither root of its native couple has a capped flower below it
(`noFlowerBelow_root_of_notCap`) and neither is a garden root (`root_nonroot_of_notCap`): the only branches that can be
pinned are the roots, pinned by `dChild` at `s` (`rcp_pins`), each with its clock the core of a capped flower parent
pinned at `s` (`rcp_clock`). `rtRoots a J pat t s q' j`: root `j` is a pinned branch. -/

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

/-! ## Generic: the parent of a pinned root and the clock layer of an attached node -/

section Generic
variable {w : ℕ}

/-- A pinned non-root branch with no capped flower below is a child of a capped flower parent. -/
theorem pinned_parent_cfp {LG : LayeredGarden w} {J : Finset (Fin w)} {pat : Fin w → FixPat} {t s : ℝ}
    {b : GBranch LG.garden.tree} (hx : NoFlowerBelow LG J b.toNode) (hnr : b.1.2 ≠ [])
    (hpin : (fixCap LG J pat t s b).isSome) :
    ∃ c : GBranch LG.garden.tree, IsCapFlowerParent LG J c ∧ b.IsChildOf c := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hpin
  rcases fixCap_cases hv with ⟨hc, -⟩ | ⟨-, -, h0, -⟩ | ⟨-, -, ⟨C, hC, hCb⟩, -⟩ | ⟨i, -, -, ⟨c, hc, h1, h2⟩, -⟩
  · exact absurd hc (hx.not_cfp (isDesc_refl _))
  · exact absurd h0 hnr
  · exfalso
    obtain ⟨g1, k, g2⟩ := hCb
    exact hx.not_cfp ⟨g1.symm, ⟨[k], g2.symm⟩⟩ hC
  · exact ⟨c, hc, h1, i, h2⟩

variable {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)

include hLayer in
/-- The layer of the node attached at a skeleton node is at most its clock layer. -/
theorem layer_attached_le_clk (p : ℕ) (hlay : ∀ z, layer z ≤ p) (x : GNode S.tree) :
    layer (attachedNode D hS x) ≤ clkLayer p (fun b => layer (D.coreBranch hS b).toNode) (clkOfNode S x) := by
  by_cases h : x.1.2 = []
  · have h2 : clkOfNode S x = .inl x.1.1 := by
      unfold clkOfNode nodeToSlot; simp [h]
    rw [h2]
    exact hlay _
  · obtain ⟨b, i, rfl⟩ : ∃ (b : GBranch S.tree) (i : Fin 3), x = b.child i :=
      ⟨_, _, (Skeleton.child_parent x h).symm⟩
    have h2 : clkOfNode S (b.child i) = .inr b := by
      unfold clkOfNode; rw [nodeToSlot_child]
    rw [h2, attachedNode_child]
    exact hLayer.1 _ i

/-- The clock of a non-root attached node whose parent is the core branch `c`: the clock source is `.inr b` with
`c = D.coreBranch hS b`. -/
theorem clock_of_parent (x : GNode S.tree) (P : GBranch (D.forest hS)) (hxP : (⟨(attachedNode D hS x).1, (attachedNode D hS x).2⟩ :
      GNode (D.forest hS)).1.1 = P.1.1 ∧ ∃ k : Fin 3, (attachedNode D hS x).1.2 = P.1.2 ++ [k]) :
    ∃ b : GBranch S.tree, clkOfNode S x = .inr b ∧ P = D.coreBranch hS b := by
  have hnr : x.1.2 ≠ [] := by
    intro h0
    have he : x = GNode.root S.tree x.1.1 := Subtype.ext (Prod.ext rfl h0)
    obtain ⟨-, k, hk⟩ := hxP
    have : (attachedNode D hS x).1.2 = [] := by rw [he, attachedNode_root]; rfl
    rw [this] at hk
    simp at hk
  obtain ⟨b, i, rfl⟩ : ∃ (b : GBranch S.tree) (i : Fin 3), x = b.child i :=
    ⟨_, _, (Skeleton.child_parent x hnr).symm⟩
  refine ⟨b, by unfold clkOfNode; rw [nodeToSlot_child], ?_⟩
  have ha : attachedNode D hS (b.child i) = (D.coreBranch hS b).child i := attachedNode_child D hS b i
  obtain ⟨h1, k, h2⟩ := hxP
  have hv := congrArg Subtype.val ha
  have e1 : (attachedNode D hS (b.child i)).1.1 = (D.coreBranch hS b).1.1 := by
    have h := congrArg Prod.fst hv; exact h
  have e2 : (attachedNode D hS (b.child i)).1.2 = (D.coreBranch hS b).1.2 ++ [i] := by
    have h := congrArg Prod.snd hv; exact h
  apply Subtype.ext
  refine Prod.ext (h1.symm.trans e1) ?_
  have := h2.symm.trans e2
  exact (List.append_inj' this rfl).1

end Generic

/-! ## The couple fields -/

section Couple
variable {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat)
  (t s : ℝ) (hR : RTRec (p := p) a J pat) (q' : SourcePair a.prime.skeleton)
  (hnc : ¬ IsCapPair a.prime.skeleton a.prime.prime.1 J q')

/-- **Root `j` of the native couple of `q'` is a pinned branch.** -/
def rtRoots (j : Fin 2) : Prop :=
  ∃ hb : ([] : Path) ∈ ((nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) q').garden.tree j).branching,
    (MkSlots.fixNative a.prime.data a.prime.prime.1 (fixCap (recLG a) J pat t s) (.inl q')
      (⟨(j, []), hb⟩ : GBranch (decodedCouple (a.prime.data.couple q')).tree)).isSome

include hnc in
theorem rcp_noFlower (k : Fin 2) :
    NoFlowerBelow (recLG a) J ((nativeCoupleForest a.prime.data a.prime.prime.1 q').root k) :=
  noFlowerBelow_root_of_notCap a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J hnc k

include hR hnc in
theorem rcp_nonroot (k : Fin 2) : ((nativeCoupleForest a.prime.data a.prime.prime.1 q').root k).1.2 ≠ [] :=
  root_nonroot_of_notCap a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J hnc hR.root k

/-- The garden branch of a native couple branch. -/
abbrev cbr (q : GBranch (decodedCouple (a.prime.data.couple q')).tree) : GBranch (a.prime.data.forest a.prime.prime.1) :=
  subforestBranchEmbedding (nativeCoupleForest a.prime.data a.prime.prime.1 q') q

include hR hnc in
/-- A pinned native couple branch is a root, pinned at `s`. -/
theorem rcp_pinned_root (q : GBranch (decodedCouple (a.prime.data.couple q')).tree)
    (hq : (fixCap (recLG a) J pat t s (cbr a q' q)).isSome) :
    q.1.2 = [] ∧ fixCap (recLG a) J pat t s (cbr a q' q) = some s := by
  have he := pinned_below_eq (rcp_noFlower a J q' hnc q.1.1) (root_isDesc_emb _ _ q' q) hq
  have h0 : q.1.2 = [] := by
    have h := congrArg (fun z : GNode (a.prime.data.forest a.prime.prime.1) => z.1.2) he
    change ((nativeCoupleForest a.prime.data a.prime.prime.1 q').root q.1.1).1.2 ++ q.1.2 =
      ((nativeCoupleForest a.prime.data a.prime.prime.1 q').root q.1.1).1.2 at h
    exact List.append_right_eq_self.mp h
  refine ⟨h0, ?_⟩
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hq
  rcases fixCap_value hv with h | ⟨-, hr, -⟩
  · rw [hv, h]
  · exfalso
    apply rcp_nonroot a J pat hR q' hnc q.1.1
    have h := congrArg (fun z : GNode (a.prime.data.forest a.prime.prime.1) => z.1.2) he
    change (cbr a q' q).1.2 = _ at h
    rw [← h]; exact hr

include hR hnc in
theorem rcp_pins : ∀ q : GBranch (nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) q').garden.tree,
    MkSlots.fixNative a.prime.data a.prime.prime.1 (fixCap (recLG a) J pat t s) (.inl q') q =
      MkSlotsO.rootPins (rtRoots a J pat t s q') s q := by
  intro q
  show fixCap (recLG a) J pat t s (cbr a q' q) = _
  unfold MkSlotsO.rootPins
  by_cases hq : q.1.2 = [] ∧ rtRoots a J pat t s q' q.1.1
  · simp only [hq, and_self, ↓reduceIte]
    obtain ⟨h0, hb, hpin⟩ := hq
    have heq : q = ⟨(q.1.1, []), hb⟩ := Subtype.ext (Prod.ext rfl h0)
    have hpin' : (fixCap (recLG a) J pat t s (cbr a q' q)).isSome := by rw [heq]; exact hpin
    exact (rcp_pinned_root a J pat t s hR q' hnc q hpin').2
  · simp only [hq, ↓reduceIte]
    cases hc : fixCap (recLG a) J pat t s (cbr a q' q) with
    | none => rfl
    | some v =>
      exfalso
      have hpin : (fixCap (recLG a) J pat t s (cbr a q' q)).isSome := by rw [hc]; rfl
      have h0 := (rcp_pinned_root a J pat t s hR q' hnc q hpin).1
      refine hq ⟨h0, ?_, ?_⟩
      · rw [← h0]; exact q.2
      · have heq : (⟨(q.1.1, []), by rw [← h0]; exact q.2⟩ : GBranch (decodedCouple (a.prime.data.couple q')).tree) =
            q := Subtype.ext (Prod.ext rfl h0.symm)
        show (fixCap (recLG a) J pat t s (cbr a q' _)).isSome
        rw [heq]; exact hpin

theorem rcp_wf : (a.prime.data.couple q').wf = true := a.prime.data.couple_wf q'

include hR in
theorem rcp_layer_le : ∀ z, (nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a)
    (sourceLayer_isLayering a) q').layer z ≤ p := fun _ => hR.geo.layer_le _

include hR in
theorem rcp_root_pinned : ∀ j, rtRoots a J pat t s q' j →
    ([] : Path) ∈ ((nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) q').garden.tree j).branching ∧
    (nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) q').layer
      (GNode.root _ j) = p := by
  rintro j ⟨hb, hpin⟩
  refine ⟨hb, ?_⟩
  show (recLG a).layer ((nativeCoupleForest a.prime.data a.prime.prime.1 q').nodeEmbedding (GNode.root _ j)) = p
  have he : (nativeCoupleForest a.prime.data a.prime.prime.1 q').nodeEmbedding (GNode.root _ j) =
      (cbr a q' ⟨(j, []), hb⟩).toNode := Subtype.ext rfl
  rw [he]
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hpin
  exact fixCap_layer hR.geo hR.patv hR.root hv

theorem rcp_root_eq (j : Fin 2) : (nativeCoupleForest a.prime.data a.prime.prime.1 q').root j =
    attachedNode a.prime.data a.prime.prime.1
      (if j = 0 then (q'.firstLeaf a.prime.prime.1).toNode else (q'.secondLeaf a.prime.prime.1).toNode) := by
  fin_cases j <;> rfl

theorem rcp_argSrc (j : Fin 2) : argSrc a.prime.prime.1 (.inl q') j =
    clkOfNode a.prime.skeleton
      (if j = 0 then (q'.firstLeaf a.prime.prime.1).toNode else (q'.secondLeaf a.prime.prime.1).toNode) := by
  fin_cases j <;> rfl

include hR in
theorem rcp_root_le : ∀ j, (nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) q').layer (GNode.root _ j) ≤
    clkLayer p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
      (argSrc a.prime.prime.1 (.inl q') j) := by
  intro j
  show (recLG a).layer ((nativeCoupleForest a.prime.data a.prime.prime.1 q').nodeEmbedding (GNode.root _ j)) ≤ _
  rw [subforest_node_root, rcp_root_eq, rcp_argSrc]
  exact layer_attached_le_clk a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) p
    (fun z => hR.geo.layer_le z) _

include hR in
theorem rcp_amb : MkSlotsO.CplAmbient p
    (clkLayer p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
      (argSrc a.prime.prime.1 (.inl q') 0))
    (clkLayer p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
      (argSrc a.prime.prime.1 (.inl q') 1))
    (a.prime.data.couple q')
    (nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) q') := by
  refine ⟨2 * R, recLG a, inflatedPosition a.prime.skeleton a.prime.data.tree (q'.firstLeaf a.prime.prime.1).toNode,
    inflatedPosition a.prime.skeleton a.prime.data.tree (q'.secondLeaf a.prime.prime.1).toNode, hR.can,
    LFTwist.reconstruction_coupleEmb a.prime.data a.prime.prime.1 (a.prime.data.garden_decodes a.prime.prime.1) q',
    ?_, ?_, ?_, ?_, ?_⟩
  · show nodeSign a.prime.skeleton.sig (inflatedPosition a.prime.skeleton a.prime.data.tree
      (q'.firstLeaf a.prime.prime.1).toNode) = 1
    rw [inflatedPosition_sign]
    exact sourcePair_first_sign a.prime.skeleton a.prime.prime.1 q'
  · show nodeSign a.prime.skeleton.sig (inflatedPosition a.prime.skeleton a.prime.data.tree
      (q'.secondLeaf a.prime.prime.1).toNode) = -1
    rw [inflatedPosition_sign]
    exact sourcePair_second_sign a.prime.skeleton a.prime.prime.1 q'
  · unfold Links.parAt
    have hm : (inflatedPosition a.prime.skeleton a.prime.data.tree (q'.firstLeaf a.prime.prime.1).toNode).2 ∈
        ((recLG a).garden.tree (inflatedPosition a.prime.skeleton a.prime.data.tree
          (q'.firstLeaf a.prime.prime.1).toNode).1).nodes :=
      (attachedNode a.prime.data a.prime.prime.1 (q'.firstLeaf a.prime.prime.1).toNode).2
    simp only [hm, ↓reduceDIte]
    exact parentLayer_inflated a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) p _ _ rfl
  · unfold Links.parAt
    have hm : (inflatedPosition a.prime.skeleton a.prime.data.tree (q'.secondLeaf a.prime.prime.1).toNode).2 ∈
        ((recLG a).garden.tree (inflatedPosition a.prime.skeleton a.prime.data.tree
          (q'.secondLeaf a.prime.prime.1).toNode).1).nodes :=
      (attachedNode a.prime.data a.prime.prime.1 (q'.secondLeaf a.prime.prime.1).toNode).2
    simp only [hm, ↓reduceDIte]
    exact parentLayer_inflated a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) p _ _ rfl
  · intro z
    show (recLG a).layer ((nativeCoupleForest a.prime.data a.prime.prime.1 q').nodeEmbedding z) = _
    have e := (Links.layerAt_node (recLG a) ((nativeCoupleForest a.prime.data a.prime.prime.1 q').nodeEmbedding z)).symm
    refine e.trans (congrArg (Links.layerAt (recLG a)) ?_)
    obtain ⟨⟨j, r⟩, hz⟩ := z
    fin_cases j <;> rfl

include hnc in
theorem rcp_genΘs_one : ∀ {d : ℕ} (L : ℝ) (σ kSel : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (k : Mom d)
    (κ : NativeRelativeDecoration a.prime.data a.prime.prime.1 d (.inl q')),
    MkSlotsI.genΘs a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J L σ kSel Rs (.inl q')
      k κ = 1 := by
  intro d L σ kSel Rs k κ
  refine Finset.prod_eq_one fun z _ => ?_
  split_ifs
  · rfl
  · exact genNW_eq_one _ J L σ kSel Rs _ _
      ((rcp_noFlower a J q' hnc z.1.1).not_onCapStem (root_isDesc_node _ _ q' z))

include hnc in
theorem rcp_selNative_empty : ∀ kSel : Fin (2 * R) → Option ℕ,
    MkSlotsS.selNative a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel (.inl q') = ∅ := by
  intro kSel
  refine Finset.filter_eq_empty_iff.mpr fun v hv => ?_
  rintro ⟨z, -, hz⟩
  have hst := (selSetCap_onStem hv).2
  have he : v.toNode = (nativeCoupleForest a.prime.data a.prime.prime.1 q').nodeEmbedding z := Subtype.ext hz
  rw [he] at hst
  exact (rcp_noFlower a J q' hnc z.1.1).not_onCapStem (root_isDesc_node _ _ q' z) hst

include hR hnc in
theorem rcp_chainW_eq : ∀ {d : ℕ} (L γ δ s' : ℝ) (Rf : Fin (2 * R) → Option ℝ)
    (dag : Option (Fin (2 * R) → Fin 3 → Mom d))
    (z : GNode (nativeCoupleGarden a.prime.data a.prime.prime.1 q').tree) (x : Mom d),
    MkSlots.chainW a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) L γ δ p s' J Rf dag
        ((nativeCoupleForest a.prime.data a.prime.prime.1 q').nodeEmbedding z) x =
      fwNode (recLG a) p (fun j => frontierG (Rf j))
        ((nativeCoupleForest a.prime.data a.prime.prime.1 q').nodeEmbedding z) x := by
  intro d L γ δ s' Rf dag z x
  refine IntGeo.chainW_eq_fwNode a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J hR.cap
    L γ δ p s' Rf dag _ x ?_
  rintro ⟨q, hq, hcq⟩
  have h1 : slotOf a.prime.data a.prime.prime.1 ((nativeCoupleForest a.prime.data a.prime.prime.1 q').nodeEmbedding z) =
      .inl q' := slotOf_nativeNodeAt a.prime.data a.prime.prime.1 (.inl q') z
  rw [h1] at hq
  rw [← Sum.inl_injective hq] at hcq
  exact hnc hcq

include hR hnc in
/-- **The clock of a pinned root is the core of a capped flower parent**, pinned at `s`. -/
theorem rcp_clock (j : Fin 2) (hj : rtRoots a J pat t s q' j) :
    ∃ β : GBranch a.prime.skeleton.tree, argSrc a.prime.prime.1 (.inl q') j = .inr β ∧
      IsCapFlowerParent (recLG a) J (a.prime.data.coreBranch a.prime.prime.1 β) := by
  obtain ⟨hb, hpin⟩ := hj
  set T := cbr a q' ⟨(j, []), hb⟩ with hT
  have hTn : T.toNode = (nativeCoupleForest a.prime.data a.prime.prime.1 q').root j := Subtype.ext (by
    show (((nativeCoupleForest a.prime.data a.prime.prime.1 q').root j).1.1,
      ((nativeCoupleForest a.prime.data a.prime.prime.1 q').root j).1.2 ++ []) = _
    rw [List.append_nil])
  have hNF : NoFlowerBelow (recLG a) J T.toNode := hTn ▸ rcp_noFlower a J q' hnc j
  have hnr : T.1.2 ≠ [] := by
    have h := rcp_nonroot a J pat hR q' hnc j
    have h2 := congrArg (fun z : GNode (a.prime.data.forest a.prime.prime.1) => z.1.2) hTn
    change T.1.2 = _ at h2
    rw [h2]; exact h
  obtain ⟨c, hc, h1, k, h2⟩ := pinned_parent_cfp hNF hnr hpin
  have hroot := rcp_root_eq a q' j
  rw [← hTn] at hroot
  obtain ⟨β, hβ, hcβ⟩ := clock_of_parent a.prime.data a.prime.prime.1 _ c
    ⟨by rw [← hroot]; exact h1, k, by rw [← hroot]; exact h2⟩
  refine ⟨β, by rw [rcp_argSrc]; exact hβ, hcβ ▸ hc⟩

include hR hnc in
theorem rcp_notSelAdj : rtRoots a J pat t s q' 0 ∧ rtRoots a J pat t s q' 1 → ∀ kSel : Fin (2 * R) → Option ℕ,
    ¬ MkSlotsI.SelAdj a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel (.inl q') := by
  rintro ⟨h0, h1⟩ kSel ⟨k, β'', hsrc, v, hv, hve⟩
  have hk : rtRoots a J pat t s q' k := by fin_cases k; exacts [h0, h1]
  obtain ⟨β, hβ, hcf⟩ := rcp_clock a J pat t s hR q' hnc k hk
  rw [hβ] at hsrc
  obtain rfl := Sum.inr_injective hsrc
  have hvc : v = a.prime.data.coreBranch a.prime.prime.1 β := Subtype.ext hve
  exact (ProtGeo.selSetCap_spec hv).2.2.2 (hvc ▸ hcf)

theorem rcp_prot (j : Fin 2) (hj : rtRoots a J pat t s q' j) : ∀ kSel : Fin (2 * R) → Option ℕ,
    MkSlotsI.HasProtNative a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
      (protI (recLG a) J pat t s kSel) (.inl q') := by
  intro kSel
  obtain ⟨hb, hpin⟩ := hj
  have hTn : (cbr a q' ⟨(j, []), hb⟩).toNode = nativeNodeAt a.prime.data a.prime.prime.1 (.inl q')
      (GNode.root (decodedCouple (a.prime.data.couple q')).tree j) := Subtype.ext rfl
  refine ⟨GNode.root _ j, ?_, (cbr a q' ⟨(j, []), hb⟩).toNode, mem_protI_of_fixCap hpin, by rw [hTn]⟩
  intro β' he
  have h1 := slotOf_nativeNodeAt a.prime.data a.prime.prime.1 (.inl q')
    (GNode.root (decodedCouple (a.prime.data.couple q')).tree j)
  rw [he, slotOf_core] at h1
  exact Sum.inr_ne_inl h1

include hR hnc in
theorem rcp_leafwise : ∀ {d : ℕ} (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom d → ℝ) (L : ℝ)
    (roots : Fin (2 * R) → (Fin d → ℤ)) (b : ℝ), 0 ≤ b →
    (∀ q ≤ p, ∀ j j', SNormR (40 * d) (40 * d) (h q j j') ≤ ENNReal.ofReal b) →
    LeafwiseControlled (nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) q')
      (MkSlots.capProfiles (nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a) q')
        (fun z => MkSlots.anchProfiles J (MkSlots.recLG a) h L roots
          ((nativeCoupleForest a.prime.data a.prime.prime.1 q').nodeEmbedding z).1))
      (nativeCoupleB a.prime.data a.prime.prime.1 (fun _ => b.toNNReal) q') := by
  intro d h L roots b hb0 hb ℓ hℓ
  rw [MkSlots.capProfiles_leaf]
  let e : GLeaf (recLG a).garden.tree := (nativeCoupleForest a.prime.data a.prime.prime.1 q').leafEmbedding ℓ
  have he : e.toNode = (nativeCoupleForest a.prime.data a.prime.prime.1 q').nodeEmbedding ℓ.toNode :=
    subforest_leaf_node _ ℓ
  have hd : ((nativeCoupleForest a.prime.data a.prime.prime.1 q').root ℓ.1.1).IsDesc e.toNode :=
    he ▸ root_isDesc_node _ _ q' ℓ.toNode
  have hNF := rcp_noFlower a J q' hnc ℓ.1.1
  have h1 : e.1.1 ∉ J := by
    have e1 : e.1.1 = ((nativeCoupleForest a.prime.data a.prime.prime.1 q').root ℓ.1.1).1.1 := hd.1.symm
    rw [e1]
    exact root_tree_not_cap a.prime.data a.prime.prime.1 J hnc _
  have h2 : ((recLG a).garden.pair e).1.1 ∉ J := fun hJ => hNF e ⟨h1, hJ⟩ hd
  show SNormR (40 * d) (40 * d) (MkSlots.anchProfiles J (recLG a) h L roots e.1) ≤ _
  unfold MkSlots.anchProfiles
  rw [pairTrees_leaf]
  simp only [h1, h2, ↓reduceIte]
  rw [typeProfiles_leaf]
  have hB : (nativeCoupleB a.prime.data a.prime.prime.1 (fun _ => b.toNNReal) q' ℓ.1 : ℝ) = b := by
    have hmem : ℓ.1.2 ∈ ((nativeCoupleGarden a.prime.data a.prime.prime.1 q').tree ℓ.1.1).nodes :=
      TTree.leaves_subset_nodes _ ℓ.2
    unfold nativeCoupleB
    simp only [hmem, ↓reduceDIte]
    exact Real.coe_toNNReal b hb0
  rw [hB]
  exact hb _ (hR.geo.layer_le _) _ _

theorem rcp_front_card : (frontNat2 a ((nativeCoupleForest a.prime.data a.prime.prime.1 q').nodeEmbedding) p).card ≤
    slotNr a.prime.data a.prime.prime.1 (.inl q') := by
  unfold frontNat2 slotNr
  exact Finset.card_le_card (@Finset.monotone_filter_right _ _ _ _ _ _ fun z _ hz => hz.1)

include hR hnc in
theorem rcp_box (ht : t ∈ Ioo (p : ℝ) (p + 1)) (hs : s ∈ Ioo (p : ℝ) t) :
    MkSlotsI.genBoxAt p a J pat t s (.inl q') ⊆
      timeBox (clkLayer p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
          (argSrc a.prime.prime.1 (.inl q') 0))
        (clkLayer p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
          (argSrc a.prime.prime.1 (.inl q') 1)) ∩ {ts | ∀ j, rtRoots a J pat t s q' j → s ≤ ts j} := by
  rintro ts ⟨hpin, hfree⟩
  refine ⟨?_, fun j hj => ?_⟩
  · by_cases hex : ∃ i : Fin 2, MkSlotsI.clkPin (fun _ => t)
        (fixCore a.prime.data a.prime.prime.1 (fixCap (recLG a) J pat t s)) (argSrc a.prime.prime.1 (.inl q') i) = none
    · exact hfree hex
    · push Not at hex
      have hmem : ∀ i : Fin 2, ts i ∈ Icc (clkLayer p (fun b => sourceLayer a
          (a.prime.data.coreBranch a.prime.prime.1 b).toNode) (argSrc a.prime.prime.1 (.inl q') i) : ℝ)
          (clkLayer p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
            (argSrc a.prime.prime.1 (.inl q') i) + 1) := by
        intro i
        obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (hex i)
        rw [hpin i v hv]
        exact clkPin_mem_Icc a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) hR.geo
          hR.patv hR.root hs ht _ v hv
      exact ⟨hmem 0, hmem 1⟩
  · obtain ⟨β, hβ, hcf⟩ := rcp_clock a J pat t s hR q' hnc j hj
    have hv : MkSlotsI.clkPin (fun _ => t) (fixCore a.prime.data a.prime.prime.1 (fixCap (recLG a) J pat t s))
        (argSrc a.prime.prime.1 (.inl q') j) = some s := by
      rw [hβ]
      show fixCap (recLG a) J pat t s (a.prime.data.coreBranch a.prime.prime.1 β) = some s
      unfold fixCap
      simp only [hcf, ↓reduceIte]
    rw [hpin j s hv]

end Couple

end WaveTurbulence.Flower.MkSlotsB
