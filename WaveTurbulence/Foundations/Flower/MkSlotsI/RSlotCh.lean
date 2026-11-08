/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.RSlotCpl
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ChainPairRecovery
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ChainHoleReplacement
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReplacementBranches
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.ReplacementLeaves
public import WaveTurbulence.Foundations.RegStruct.ChainSubtreeFrames
public import WaveTurbulence.Foundations.RegStruct.ChainNodeBounds
public import WaveTurbulence.Foundations.Molecule.RegRedDraft.AttachmentMomenta

/-! # B3s-HELPER7 WP6 (R-slot, part 2): the ambient data at the nodes of a native chain

On the reconstruction `LG = layeredReconstruction D hS layer hLayer`, the native chain of a skeleton branch `β`
(addresses below `pos = inflatedPosition β`, lone leaf at `λ = lonePath (D.tree β)`: the core of `β`) carries:

* `chain_core_iff`: its only core node is the lone leaf;
* `chain_partner_tree`, `pairTrees_chain`, `anch_ch`: its non-lone leaves are paired inside the chain, so the
  anchored profile is the type profile `h (layer) (tree) (tree)`;
* `chainW_ch`: the node weight is the frontier weight `fwI` (root factor at B3's `wLay`, `chQW`);
* the four predicates of the pattern pins at a chain branch: never a capped flower parent (`not_cfp_chain`), root
  iff root of the chain at a skeleton root (`chRR`), `dParent` iff it is the parent of the lone leaf and the core of `β`
  is a capped flower parent, `dChild i` iff it is the chain top below a capped flower parent at letter `i` (`chRC`);
* `onCapStem_ch`: a non-lone chain node is on the capped stem iff it lies on the lone path and the core of `β` is on
  the capped stem; hence the stem node weight `genNode_ch` (`genT`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlots
open WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.Stage1WNoVine

namespace WaveTurbulence.Flower.MkSlotsI

/-! ## Pairs of a chain (copied from main's `chain_pair_mem_of_ambient`) -/

/-- The partner of a non-lone leaf of a chain inflated at `a` lies in the tree of `a`. -/
theorem chain_partner_tree' {w : ℕ} (X : RegChain) (ζ : ℤˣ) (G : Garden w) (a : Address w) (x : Address 1)
    (ℓ : GLeaf G.tree) (hx : x.2 ∈ (X.plug ζ .leaf).leaves) (hn : x.2 ≠ X.lonePath)
    (hℓ : ℓ.1 = addrExt a x.2) (hP : ∀ p ∈ X.pairsAt ζ a, p ∈ sourcePairs G) :
    (G.pair ℓ).1.1 = a.1 := by
  have hxP : x ∈ pairEndpoints (X.pairsAt ζ (0,[])) := by
    have hm := (leafAddresses_one_root (X.plug ζ .leaf) x).mpr hx
    rw [chain_leafAddresses, leafAddresses_leaf, Finset.mem_union, Finset.mem_singleton] at hm
    rcases hm with hm | hm
    · exact hm
    · exact (hn (congrArg (fun z : Address 1 => z.2) hm)).elim
  obtain ⟨p, hp, he⟩ := (mem_pairEndpoints_iff _ _).mp hxP
  let f : Address 1 → Address w := fun z => addrExt a z.2
  have hmap : X.pairsAt ζ a = (X.pairsAt ζ ((0 : Fin 1), [])).map (fun z => (f z.1, f z.2)) := by
    have hh := chain_pairsAt_map X f (by intro z r; simp [f, addrExt, List.append_assoc]) ζ (0, [])
    simpa only [f, addrExt, List.nil_append, List.append_nil] using hh
  have hm : (f p.1, f p.2) ∈ sourcePairs G := hP _ (by rw [hmap]; exact List.mem_map.mpr ⟨p, hp, rfl⟩)
  obtain ⟨u, v, hu, hv, huv⟩ := sourcePairs_actual_endpoints G _ hm
  rcases he with he | he
  · have hlu : ℓ = u := Subtype.ext (hℓ.trans ((congrArg f he).trans hu.symm))
    rw [hlu, huv, hv]
    rfl
  · have hlv : ℓ = v := Subtype.ext (hℓ.trans ((congrArg f he).trans hv.symm))
    rw [hlv, ← huv, G.pair_pair, hu]
    rfl

section Chain

variable {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (J : Finset (Fin w))
  (β : GBranch S.tree)

/-- The tree index of the chain of `β`. -/
def chRI : Fin w := (inflatedPosition S D.tree β.toNode).1

/-- The chain of `β` sits at a garden root. -/
def chRR : Prop := (inflatedPosition S D.tree β.toNode).2 = []

/-- The depth of the top of the chain of `β`. -/
def chRD : ℕ := (inflatedPosition S D.tree β.toNode).2.length

/-- The capped-flower-parent letter above the top of the chain of `β`. -/
def chRC : Option (Fin 3) := rcOf (layeredReconstruction D hS layer hLayer) J (attachedNode D hS β.toNode)

/-- The weight layer of the upper clock source of the chain of `β` (B3's `wLay`). -/
def chQW (p : ℕ) : ℕ :=
  Stage1WVine.wLay p (fun b => layer (D.coreBranch hS b).toNode) (Represents.argSrc hS (.inr β) 0)

/-- The stem node weight on a native chain (lone path `lp`, core stem test `sb`, top depth `rd`). -/
def genT (N : LayeredGarden 1) (ri : Fin w) (lp : Path) (sb : Prop) (rd : ℕ) (ex : Fin w → Prop) (L : ℝ)
    (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ) (a : GNode N.garden.tree) (v : ℝ) : ℂ :=
  if a.1.2 = lp then 1 else
    if a.1.2 ∈ (N.garden.tree a.1.1).branching then
      genD L σ kSel Rs (a.1.2 <+: lp ∧ sb) ri (rd + a.1.2.length) (ex ri) v
    else 1

theorem chain_val (a : GNode (nativeChainLayered D hS layer hLayer β).garden.tree) :
    (chainContextNode D hS β a).1 =
      ((inflatedPosition S D.tree β.toNode).1, (inflatedPosition S D.tree β.toNode).2 ++ a.1.2) := rfl

theorem chain_subtree :
    Comb.subtree (D.forest hS (inflatedPosition S D.tree β.toNode).1) (inflatedPosition S D.tree β.toNode).2 =
      some ((D.tree β).plug (nodeSign S.sig β.1) (node3 fun i => D.inflateNode hS (β.child i))) :=
  (D.forest_subtree_position hS β.toNode).trans (congrArg some (D.inflateNode_branch hS β))

/-- **The only core node of a native chain is its lone leaf.** -/
theorem chain_core_iff (a : GNode (nativeChainLayered D hS layer hLayer β).garden.tree) :
    (∃ β' : GBranch S.tree, chainContextNode D hS β a = (D.coreBranch hS β').toNode) ↔
      a.1.2 = (D.tree β).lonePath := by
  constructor
  · rintro ⟨β', hβ'⟩
    have h2 : nativeNodeMap D hS ⟨.inr β, a⟩ =
        nativeNodeMap D hS ⟨.inr β', (chainLoneLeaf (D.tree β') (nodeSign S.sig β'.1)).toNode⟩ :=
      hβ'.trans (chainContextNode_lone D hS β').symm
    have h3 := nativeNodeMap_injective D hS h2
    have h4 : β = β' := Sum.inr_injective (congrArg Sigma.fst h3)
    subst h4
    have h5 := eq_of_heq (Sigma.mk.inj_iff.mp h3).2
    rw [h5]
    rfl
  · intro h
    refine ⟨β, ?_⟩
    have ha : a = (chainLoneLeaf (D.tree β) (nodeSign S.sig β.1)).toNode :=
      Subtype.ext (Prod.ext (Subsingleton.elim _ _) h)
    rw [ha]
    exact chainContextNode_lone D hS β

/-- A chain node whose image is a branch and not the core is a branch of the chain (copied from WP4's
`chain_branch_of_branch`). -/
theorem chain_branch_of_branch' (a : GNode (decodedTree (D.tree β) (nodeSign S.sig β.1)).tree)
    (h : (chainContextNode D hS β a).1.2 ∈ ((D.forest hS) (chainContextNode D hS β a).1.1).branching)
    (hnc : chainContextNode D hS β a ≠ (D.coreBranch hS β).toNode) :
    a.1.2 ∈ ((decodedTree (D.tree β) (nodeSign S.sig β.1)).tree a.1.1).branching := by
  have hs := chain_subtree D hS β
  have h1 := (Comb.subtree_branching_iff hs a.1.2).mpr h
  have he := branching_replaceAt_eq (plug_subtree_lonePath (D.tree β) (nodeSign S.sig β.1) .leaf)
    (node3 fun i => D.inflateNode hS (β.child i))
  rw [replaceAt_plug_lonePath] at he
  rw [he] at h1
  rcases Finset.mem_union.mp h1 with h2 | h2
  · exact (Finset.mem_filter.mp h2).1
  · exfalso
    obtain ⟨r, -, hr⟩ := Finset.mem_image.mp h2
    have hlp : (D.tree β).lonePath = a.1.2 :=
      leaf_prefix_node_eq (chain_lone_mem_leaves (D.tree β) (nodeSign S.sig β.1)) a.2 ⟨r, hr⟩
    apply hnc
    rw [← chainContextNode_lone D hS β]
    congr 1
    apply Subtype.ext
    exact Prod.ext (Subsingleton.elim _ _) hlp.symm

/-- The partner of a non-lone chain leaf lies in the tree of the chain. -/
theorem chain_partner_tree (a : GNode (nativeChainLayered D hS layer hLayer β).garden.tree)
    (ha : a.1.2 ≠ (D.tree β).lonePath) (ℓ : GLeaf (D.forest hS)) (hℓ : ℓ.1 = (chainContextNode D hS β a).1) :
    ((D.garden hS).pair ℓ).1.1 = chRI D β := by
  have hleaf : a.1.2 ∈ ((D.tree β).plug (nodeSign S.sig β.1) .leaf).leaves := by
    rcases (Comb.TreePath.mem_nodes_iff _ _).mp a.2 with h | h
    · exact h
    · exfalso
      have hb := chain_branching_subset_plug (D.tree β) (nodeSign S.sig β.1)
        (node3 fun i => D.inflateNode hS (β.child i)) h
      have hb' := (Comb.subtree_branching_iff (chain_subtree D hS β) a.1.2).mp hb
      have hl := ℓ.2
      rw [hℓ] at hl
      exact Comb.TreePath.not_mem_branching_of_mem_leaves _ hl hb'
  exact chain_partner_tree' (D.tree β) (nodeSign S.sig β.1) (D.garden hS) (inflatedPosition S D.tree β.toNode)
    a.1 ℓ hleaf ha hℓ (fun p hp => D.chain_pair_mem hS (D.garden_decodes hS) β p hp)

/-- The pair trees at a native chain node are the tree of the chain. -/
theorem pairTrees_chain (a : GNode (nativeChainLayered D hS layer hLayer β).garden.tree) :
    pairTrees (D.garden hS) (chainContextNode D hS β a).1 = (chRI D β, chRI D β) := by
  unfold pairTrees
  by_cases hl : ∃ ℓ : GLeaf (D.garden hS).tree, ℓ.1 = (chainContextNode D hS β a).1
  · rw [dite_eq_left hl]
    have ha : a.1.2 ≠ (D.tree β).lonePath := by
      intro h
      have hc := (chain_core_iff D hS layer hLayer β a).mpr h
      obtain ⟨β', hβ'⟩ := hc
      have hb := (D.coreBranch hS β').2
      have hl2 := hl.choose.2
      rw [hl.choose_spec, hβ'] at hl2
      exact Comb.TreePath.not_mem_branching_of_mem_leaves _ hl2 hb
    exact Prod.ext rfl (chain_partner_tree D hS layer hLayer β a ha hl.choose hl.choose_spec)
  · rw [dite_eq_right hl]
    rfl

/-- **The anchored profile at a native chain node** is the type profile of the chain's tree. -/
theorem anch_ch (hcap : ∀ j ∈ J, (D.garden hS).tree j = TTree.leaf) {d' : ℕ}
    (h : ℕ → Fin w → Fin w → Mom d' → ℝ) (L : ℝ) (roots : Fin w → (Fin d' → ℤ))
    (a : GNode (nativeChainLayered D hS layer hLayer β).garden.tree) :
    anchProfiles J (layeredReconstruction D hS layer hLayer) h L roots (chainContextNode D hS β a).1 =
      h ((nativeChainLayered D hS layer hLayer β).layer a) (chRI D β) (chRI D β) := by
  have hnc : ¬ InCapNative D hS J (chainContextNode D hS β a) :=
    IntGeo.not_inCapNative_of_slot D hS J (.inr β) (fun q h => by cases h) a
  rw [IntGeo.anchProfiles_eq D hS layer hLayer J hcap h L roots _ hnc]
  have e := pairTrees_chain D hS layer hLayer β a
  change pairTrees (layeredReconstruction D hS layer hLayer).garden (chainContextNode D hS β a).1 = _ at e
  unfold typeProfiles
  split_ifs with hn
  · rw [e]
    rfl
  · exact absurd (chainContextNode D hS β a).2 hn

/-- **The node weight at a native chain node** is the frontier weight. -/
theorem chainW_ch (hcap : ∀ j ∈ J, (D.garden hS).tree j = TTree.leaf) (L γ δ : ℝ) (p : ℕ) (s : ℝ)
    (Rf : Fin w → Option ℝ) (dag : Option (Fin w → Fin 3 → Mom d))
    (a : GNode (nativeChainLayered D hS layer hLayer β).garden.tree) (x : Mom d) :
    chainW D hS layer hLayer L γ δ p s J Rf dag (chainContextNode D hS β a) x =
      fwI p (fun j => frontierG (Rf j)) (nativeChainLayered D hS layer hLayer β) (fun _ => chRI D β)
        (fun _ => chQW D hS layer β p) a x := by
  have hnc : ¬ InCapNative D hS J (chainContextNode D hS β a) :=
    IntGeo.not_inCapNative_of_slot D hS J (.inr β) (fun q h => by cases h) a
  rw [IntGeo.chainW_eq_fwNode D hS layer hLayer J hcap L γ δ p s Rf dag _ x hnc]
  rw [fwNode_embed (layeredReconstruction D hS layer hLayer) (nativeChainLayered D hS layer hLayer β)
    (chainContextNode D hS β) (fun _ => inflatedPosition S D.tree β.toNode)
    (fun a => rfl) (fun a => rfl) p (fun j => frontierG (Rf j)) a x]
  unfold fwI
  by_cases ha : a.1.2 = []
  · have har : a = GNode.root (nativeChainLayered D hS layer hLayer β).garden.tree 0 :=
      Subtype.ext (Prod.ext (Subsingleton.elim _ _) ha)
    unfold rowParentLayer
    rw [ite_eq_left ha, ite_eq_left ha]
    have e := Stage1WVine.treeQ_root_factor D hS layer hLayer p (frontierG (Rf (chRI D β))) β x
    rw [← har] at e
    exact e
  · unfold rowParentLayer
    rw [ite_eq_right ha, ite_eq_right ha]
    rfl

/-! ### The pins at a chain branch -/

variable (hcap : ∀ j ∈ J, (D.garden hS).tree j = TTree.leaf)
include hcap

/-- No branch at a non-lone chain node is a capped flower parent. -/
theorem not_cfp_chain (x : GNode (nativeChainLayered D hS layer hLayer β).garden.tree)
    (hx : x.1.2 ≠ (D.tree β).lonePath) (B : GBranch (D.forest hS)) (hB : B.toNode = chainContextNode D hS β x) :
    ¬ IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J B := by
  intro hcfp
  have hnc : ∀ b, B ≠ D.coreBranch hS b := fun b he =>
    hx ((chain_core_iff D hS layer hLayer β x).mp ⟨b, hB.symm.trans (by rw [he])⟩)
  have hin := (IntGeo.capParent_inCapNative D hS layer hLayer J hcap B hcfp hnc).1
  rw [hB] at hin
  exact IntGeo.not_inCapNative_of_slot D hS J (.inr β) (fun q h => by cases h) x hin

omit hcap in
theorem nativeBr_inr_node (b : GBranch (nativeChainLayered D hS layer hLayer β).garden.tree) :
    (MkSlotsB.nativeBr D hS (.inr β) b).toNode = chainContextNode D hS β b.toNode := Subtype.ext rfl

omit hcap in
theorem lone_not_branch (b : GBranch (nativeChainLayered D hS layer hLayer β).garden.tree) :
    b.1.2 ≠ (D.tree β).lonePath := by
  intro h
  have hb := b.2
  rw [h] at hb
  exact Comb.TreePath.not_mem_branching_of_mem_leaves _
    (chain_lone_mem_leaves (D.tree β) (nodeSign S.sig β.1)) hb

omit hcap in
theorem cfp_nativeBr_ch' (b : GBranch (nativeChainLayered D hS layer hLayer β).garden.tree) :
    (MkSlotsB.nativeBr D hS (.inr β) b).1 =
      ((inflatedPosition S D.tree β.toNode).1, (inflatedPosition S D.tree β.toNode).2 ++ b.1.2) := rfl

/-- A chain branch is never a capped flower parent. -/
theorem cfp_nativeBr_ch (b : GBranch (nativeChainLayered D hS layer hLayer β).garden.tree) :
    ¬ IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (MkSlotsB.nativeBr D hS (.inr β) b) :=
  not_cfp_chain D hS layer hLayer J β hcap b.toNode (lone_not_branch D hS layer hLayer β b) _
    (nativeBr_inr_node D hS layer hLayer β b)

omit hcap in
/-- Root predicate at a chain branch. -/
theorem root_nativeBr_ch (b : GBranch (nativeChainLayered D hS layer hLayer β).garden.tree) :
    (MkSlotsB.nativeBr D hS (.inr β) b).1.2 = [] ↔ b.1.2 = [] ∧ chRR D β := by
  show (inflatedPosition S D.tree β.toNode).2 ++ b.1.2 = [] ↔ _
  rw [List.append_eq_nil_iff]
  exact And.comm

/-- `dParent` predicate at a chain branch: the parent of the lone leaf, below a capped flower parent core. -/
theorem par_nativeBr_ch (b : GBranch (nativeChainLayered D hS layer hLayer β).garden.tree) :
    (∃ C : GBranch (D.forest hS), IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J C ∧
        C.IsChildOf (MkSlotsB.nativeBr D hS (.inr β) b)) ↔
      (∃ i : Fin 3, b.1.2 ++ [i] = (D.tree β).lonePath) ∧
        IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS β) := by
  constructor
  · rintro ⟨C, hC, h1, i, h2⟩
    have hCn : C.toNode = chainContextNode D hS β (b.child i) := by
      apply Subtype.ext
      show C.1 = ((inflatedPosition S D.tree β.toNode).1, (inflatedPosition S D.tree β.toNode).2 ++ (b.1.2 ++ [i]))
      refine Prod.ext h1 ?_
      rw [h2]
      exact List.append_assoc _ _ _
    by_cases hl : b.1.2 ++ [i] = (D.tree β).lonePath
    · refine ⟨⟨i, hl⟩, ?_⟩
      have hcore := (chain_core_iff D hS layer hLayer β (b.child i)).mpr hl
      obtain ⟨β', hβ'⟩ := hcore
      have hβ : β' = β := by
        have h3 := (chain_core_iff D hS layer hLayer β (b.child i)).mpr hl
        have h4 : chainContextNode D hS β (b.child i) = (D.coreBranch hS β).toNode := by
          have ha : b.child i = (chainLoneLeaf (D.tree β) (nodeSign S.sig β.1)).toNode :=
            Subtype.ext (Prod.ext (Subsingleton.elim _ _) hl)
          rw [ha]
          exact chainContextNode_lone D hS β
        have h5 : nativeNodeMap D hS ⟨.inr β', (chainLoneLeaf (D.tree β') (nodeSign S.sig β'.1)).toNode⟩ =
            nativeNodeMap D hS ⟨.inr β, (chainLoneLeaf (D.tree β) (nodeSign S.sig β.1)).toNode⟩ :=
          (chainContextNode_lone D hS β').trans (hβ'.symm.trans (h4.trans (chainContextNode_lone D hS β).symm))
        exact Sum.inr_injective (congrArg Sigma.fst (nativeNodeMap_injective D hS h5))
      subst hβ
      have hCv := congrArg Subtype.val (hCn.trans hβ')
      have hCe : C = D.coreBranch hS β' := Subtype.ext hCv
      rw [← hCe]
      exact hC
    · exact (not_cfp_chain D hS layer hLayer J β hcap (b.child i) hl C hCn hC).elim
  · rintro ⟨⟨i, hi⟩, hcb⟩
    refine ⟨D.coreBranch hS β, hcb, rfl, i, ?_⟩
    show (inflatedPosition S D.tree β.toNode).2 ++ (D.tree β).lonePath =
      ((inflatedPosition S D.tree β.toNode).2 ++ b.1.2) ++ [i]
    rw [← hi, List.append_assoc]

/-- `dChild` predicate at a chain branch: the chain top below a capped flower parent, at letter `i`. -/
theorem ch_nativeBr_ch (b : GBranch (nativeChainLayered D hS layer hLayer β).garden.tree) (i : Fin 3) :
    (∃ C : GBranch (D.forest hS), IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J C ∧
        (MkSlotsB.nativeBr D hS (.inr β) b).1.1 = C.1.1 ∧
        (MkSlotsB.nativeBr D hS (.inr β) b).1.2 = C.1.2 ++ [i]) ↔
      b.1.2 = [] ∧ chRC D hS layer hLayer J β = some i := by
  constructor
  · rintro ⟨C, hC, h1, h2⟩
    change (inflatedPosition S D.tree β.toNode).2 ++ b.1.2 = C.1.2 ++ [i] at h2
    by_cases hb : b.1.2 = []
    · refine ⟨hb, ?_⟩
      rw [hb, List.append_nil] at h2
      have hR : (attachedNode D hS β.toNode).1.2 ≠ [] := by
        show (inflatedPosition S D.tree β.toNode).2 ≠ []
        rw [h2]; simp
      have hpar : GNode.parent (tree := (layeredReconstruction D hS layer hLayer).garden.tree)
          (attachedNode D hS β.toNode) hR = C := by
        apply Subtype.ext
        show ((inflatedPosition S D.tree β.toNode).1, (inflatedPosition S D.tree β.toNode).2.dropLast) = C.1
        rw [h2, List.dropLast_concat]
        exact Prod.ext h1 rfl
      unfold chRC rcOf
      rw [dite_eq_left hR, hpar, ite_eq_left hC]
      exact congrArg some (getLast_of_eq' h2 hR)
    · exfalso
      have hb' : b.1.2 = b.1.2.dropLast ++ [b.1.2.getLast hb] := (List.dropLast_append_getLast hb).symm
      rw [hb', ← List.append_assoc] at h2
      obtain ⟨h3, -⟩ := List.append_inj' h2 rfl
      set c := b.toNode.parent hb
      have hCn : C.toNode = chainContextNode D hS β c.toNode := by
        apply Subtype.ext
        show C.1 = ((inflatedPosition S D.tree β.toNode).1, (inflatedPosition S D.tree β.toNode).2 ++ b.1.2.dropLast)
        exact Prod.ext h1.symm h3.symm
      exact not_cfp_chain D hS layer hLayer J β hcap c.toNode (lone_not_branch D hS layer hLayer β c) C hCn hC
  · rintro ⟨hb, hrc⟩
    unfold chRC rcOf at hrc
    by_cases hR : (attachedNode D hS β.toNode).1.2 ≠ []
    · rw [dite_eq_left hR] at hrc
      by_cases hC : IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J
          (GNode.parent (tree := (layeredReconstruction D hS layer hLayer).garden.tree)
            (attachedNode D hS β.toNode) hR)
      · rw [ite_eq_left hC] at hrc
        have hi := Option.some.inj hrc
        refine ⟨GNode.parent (tree := (layeredReconstruction D hS layer hLayer).garden.tree)
          (attachedNode D hS β.toNode) hR, hC, rfl, ?_⟩
        show (inflatedPosition S D.tree β.toNode).2 ++ b.1.2 = (inflatedPosition S D.tree β.toNode).2.dropLast ++ [i]
        rw [hb, List.append_nil, ← hi]
        exact (List.dropLast_append_getLast hR).symm
      · rw [ite_eq_right hC] at hrc
        exact absurd hrc (by simp)
    · rw [dite_eq_right hR] at hrc
      exact absurd hrc (by simp)

/-! ### The stem at a chain node -/

/-- **A non-lone chain node is on the capped stem iff it lies on the lone path and the core is on the stem.** -/
theorem onCapStem_ch (a : GNode (nativeChainLayered D hS layer hLayer β).garden.tree)
    (ha : a.1.2 ≠ (D.tree β).lonePath) :
    OnCapStem (layeredReconstruction D hS layer hLayer) J (chainContextNode D hS β a) ↔
      a.1.2 <+: (D.tree β).lonePath ∧
        OnCapStem (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS β).toNode := by
  constructor
  · rintro ⟨ℓ, hℓ, h1, r, h2⟩
    have h2' : ((inflatedPosition S D.tree β.toNode).2 ++ a.1.2) ++ r = ℓ.1.2 := h2
    have h1' : ℓ.1.1 = (inflatedPosition S D.tree β.toNode).1 := h1.symm
    have hmem : a.1.2 ++ r ∈
        ((D.tree β).plug (nodeSign S.sig β.1) (node3 fun i => D.inflateNode hS (β.child i))).leaves := by
      rw [Comb.subtree_leaves_iff (chain_subtree D hS β)]
      have h := ℓ.2
      rw [h1', ← h2', List.append_assoc] at h
      exact h
    have he := Comb.leaves_replaceAt_eq (plug_subtree_lonePath (D.tree β) (nodeSign S.sig β.1) .leaf)
      (node3 fun i => D.inflateNode hS (β.child i))
    rw [replaceAt_plug_lonePath] at he
    rw [he] at hmem
    rcases Finset.mem_union.mp hmem with h3 | h3
    · exfalso
      obtain ⟨h4, h5⟩ := Finset.mem_filter.mp h3
      have hn : a.1.2 ++ r ≠ (D.tree β).lonePath := fun h => h5 (h ▸ List.prefix_refl _)
      let x : GNode (nativeChainLayered D hS layer hLayer β).garden.tree :=
        ⟨((0 : Fin 1), a.1.2 ++ r), (Comb.TreePath.mem_nodes_iff _ _).mpr (Or.inl h4)⟩
      have hx : ℓ.1 = (chainContextNode D hS β x).1 := by
        show ℓ.1 = ((inflatedPosition S D.tree β.toNode).1, (inflatedPosition S D.tree β.toNode).2 ++ (a.1.2 ++ r))
        refine Prod.ext h1' ?_
        rw [← h2', List.append_assoc]
      have hp := chain_partner_tree D hS layer hLayer β x hn ℓ hx
      have hJ := hℓ.2
      change ((D.garden hS).pair ℓ).1.1 ∈ J at hJ
      rw [hp] at hJ
      have e : chRI D β = β.1.1 := inflatedPosition_index S D.tree β.toNode
      rw [e] at hJ
      exact IntCore.branch_tree_not_mem D hS J hcap β hJ
    · obtain ⟨ρ, -, hρ⟩ := Finset.mem_image.mp h3
      refine ⟨?_, ℓ, hℓ, h1'.symm, ρ, ?_⟩
      · rcases List.prefix_or_prefix_of_prefix (List.prefix_append a.1.2 r) (hρ ▸ List.prefix_append _ ρ) with
          h | h
        · exact h
        · exact (ha (leaf_prefix_node_eq (chain_lone_mem_leaves (D.tree β) (nodeSign S.sig β.1)) a.2 h).symm).elim
      · show ((inflatedPosition S D.tree β.toNode).2 ++ (D.tree β).lonePath) ++ ρ = ℓ.1.2
        rw [← h2', List.append_assoc, List.append_assoc, ← hρ]
  · rintro ⟨hp, ℓ, hℓ, h1, r, h2⟩
    refine ⟨ℓ, hℓ, h1, ((D.tree β).lonePath.drop a.1.2.length) ++ r, ?_⟩
    have hd : a.1.2 ++ (D.tree β).lonePath.drop a.1.2.length = (D.tree β).lonePath := by
      obtain ⟨t, ht⟩ := hp
      rw [← ht]
      simp
    change ((inflatedPosition S D.tree β.toNode).2 ++ (D.tree β).lonePath) ++ r = ℓ.1.2 at h2
    show ((inflatedPosition S D.tree β.toNode).2 ++ a.1.2) ++ ((D.tree β).lonePath.drop a.1.2.length ++ r) = ℓ.1.2
    rw [← h2, ← hd]
    simp [List.append_assoc]

/-- **The per-node factor of `genΘs` at a native chain node.** -/
theorem genNode_ch (L : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)
    (hone : MkSlotsS.OneFlower (layeredReconstruction D hS layer hLayer) J)
    (a : GNode (nativeChainLayered D hS layer hLayer β).garden.tree) (v : ℝ) :
    genNode D hS layer hLayer J L σ kSel Rs (chainContextNode D hS β a) v =
      genT (nativeChainLayered D hS layer hLayer β) (chRI D β) (D.tree β).lonePath
        (OnCapStem (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS β).toNode) (chRD D β)
        (fun j => (selCap (layeredReconstruction D hS layer hLayer) J kSel j).isSome) L σ kSel Rs a v := by
  unfold genNode genT
  by_cases hl : a.1.2 = (D.tree β).lonePath
  · rw [ite_eq_left ((chain_core_iff D hS layer hLayer β a).mpr hl), ite_eq_left hl]
  · rw [ite_eq_right (fun h => hl ((chain_core_iff D hS layer hLayer β a).mp h)), ite_eq_right hl]
    by_cases hb : a.1.2 ∈ ((nativeChainLayered D hS layer hLayer β).garden.tree a.1.1).branching
    · rw [ite_eq_left hb]
      have he : chainContextNode D hS β a = (MkSlotsB.nativeBr D hS (.inr β) ⟨a.1, hb⟩).toNode := Subtype.ext rfl
      rw [he]
      refine (genNW_genD (LG := layeredReconstruction D hS layer hLayer) L σ kSel Rs hone
        (MkSlotsB.nativeBr D hS (.inr β) ⟨a.1, hb⟩) v).trans ?_
      have hst : (OnCapStem (layeredReconstruction D hS layer hLayer) J
            (MkSlotsB.nativeBr D hS (.inr β) ⟨a.1, hb⟩).toNode ∧
          ¬ IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (MkSlotsB.nativeBr D hS (.inr β) ⟨a.1, hb⟩)) ↔
          (a.1.2 <+: (D.tree β).lonePath ∧
            OnCapStem (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS β).toNode) := by
        rw [← he, onCapStem_ch D hS layer hLayer J β hcap a hl]
        exact and_iff_left (cfp_nativeBr_ch D hS layer hLayer J β hcap ⟨a.1, hb⟩)
      have hlen : (MkSlotsB.nativeBr D hS (.inr β) ⟨a.1, hb⟩).1.2.length = chRD D β + a.1.2.length := by
        show ((inflatedPosition S D.tree β.toNode).2 ++ a.1.2).length = _
        rw [List.length_append]
        rfl
      rw [hlen]
      exact congrArg (fun P => genD L σ kSel Rs P (chRI D β) (chRD D β + a.1.2.length)
        ((selCap (layeredReconstruction D hS layer hLayer) J kSel (chRI D β)).isSome) v) (propext hst)
    · rw [ite_eq_right hb]
      apply genNW_not_branch
      intro h
      exact hb (chain_branch_of_branch' D hS β a h
        (fun he => hl ((chain_core_iff D hS layer hLayer β a).mp ⟨β, he⟩)))

end Chain

end WaveTurbulence.Flower.MkSlotsI
