/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsO.Split
public import WaveTurbulence.Foundations.Flower.MkSlots.IntGeo
public import WaveTurbulence.Foundations.Flower.MkSlotsB.PatGeoLb
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ChainPairRecovery
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ChainHoleReplacement
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReplacementBranches
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.ReplacementLeaves
public import WaveTurbulence.Foundations.RegStruct.ChainSubtreeFrames
public import WaveTurbulence.Foundations.RegStruct.ChainNodeBounds
public import WaveTurbulence.Foundations.Molecule.RegRedDraft.AttachmentMomenta

/-! # PROT-CHAIN (B3s-HELPER8 sub-agent `Pc`): the native chain of a chain slot in the reconstruction

Copied by source from HELPER7's `MkSlotsI/RSlotCh.lean` (sha256 b14831bc…, see `COPIED-SHA256SUMS`), names prefixed
`pc_`, without the frontier/stem-weight parts (`chRD`, `chRC`, `chQW`, `genT`, `chainW_ch`, `ch_nativeBr_ch`,
`genNode_ch`), so that this area does not depend on work in progress elsewhere. On the reconstruction
`LG = layeredReconstruction D hS layer hLayer`, the native chain of a skeleton branch `β` (addresses below
`pos = inflatedPosition β`, lone leaf at `λ = lonePath (D.tree β)`: the core of `β`):

* `pc_chain_core_iff`: its only core node is the lone leaf;
* `pc_chain_partner_tree`, `pc_pairTrees_chain`, `pc_anch_ch`: its non-lone leaves are paired inside the chain, so the
  anchored profile is the type profile `h (layer) (tree) (tree)`;
* the pattern-pin predicates at a chain branch: never a capped flower parent (`pc_not_cfp_chain`), root iff root of
  the chain at a skeleton root (`pc_root_nativeBr_ch`), `dParent` iff it is the parent of the lone leaf and the core of
  `β` is a capped flower parent (`pc_par_nativeBr_ch`);
* `pc_onCapStem_ch`: a non-lone chain node is on the capped stem iff it lies on the lone path and the core of `β` is
  on the capped stem. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlots
open WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.Stage1WNoVine

namespace WaveTurbulence.Flower.MkSlotsO

/-! ## Pairs of a chain (copied from main's `chain_pair_mem_of_ambient`) -/

/-- The partner of a non-lone leaf of a chain inflated at `a` lies in the tree of `a`. -/
theorem pc_chain_partner_tree' {w : ℕ} (X : RegChain) (ζ : ℤˣ) (G : Garden w) (a : Address w) (x : Address 1)
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
def pcRI : Fin w := (inflatedPosition S D.tree β.toNode).1

/-- The chain of `β` sits at a garden root. -/
def pcRR : Prop := (inflatedPosition S D.tree β.toNode).2 = []


theorem pc_chain_val (a : GNode (nativeChainLayered D hS layer hLayer β).garden.tree) :
    (chainContextNode D hS β a).1 =
      ((inflatedPosition S D.tree β.toNode).1, (inflatedPosition S D.tree β.toNode).2 ++ a.1.2) := rfl

theorem pc_chain_subtree :
    Comb.subtree (D.forest hS (inflatedPosition S D.tree β.toNode).1) (inflatedPosition S D.tree β.toNode).2 =
      some ((D.tree β).plug (nodeSign S.sig β.1) (node3 fun i => D.inflateNode hS (β.child i))) :=
  (D.forest_subtree_position hS β.toNode).trans (congrArg some (D.inflateNode_branch hS β))

/-- **The only core node of a native chain is its lone leaf.** -/
theorem pc_chain_core_iff (a : GNode (nativeChainLayered D hS layer hLayer β).garden.tree) :
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
theorem pc_chain_branch_of_branch' (a : GNode (decodedTree (D.tree β) (nodeSign S.sig β.1)).tree)
    (h : (chainContextNode D hS β a).1.2 ∈ ((D.forest hS) (chainContextNode D hS β a).1.1).branching)
    (hnc : chainContextNode D hS β a ≠ (D.coreBranch hS β).toNode) :
    a.1.2 ∈ ((decodedTree (D.tree β) (nodeSign S.sig β.1)).tree a.1.1).branching := by
  have hs := pc_chain_subtree D hS β
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
theorem pc_chain_partner_tree (a : GNode (nativeChainLayered D hS layer hLayer β).garden.tree)
    (ha : a.1.2 ≠ (D.tree β).lonePath) (ℓ : GLeaf (D.forest hS)) (hℓ : ℓ.1 = (chainContextNode D hS β a).1) :
    ((D.garden hS).pair ℓ).1.1 = pcRI D β := by
  have hleaf : a.1.2 ∈ ((D.tree β).plug (nodeSign S.sig β.1) .leaf).leaves := by
    rcases (Comb.TreePath.mem_nodes_iff _ _).mp a.2 with h | h
    · exact h
    · exfalso
      have hb := chain_branching_subset_plug (D.tree β) (nodeSign S.sig β.1)
        (node3 fun i => D.inflateNode hS (β.child i)) h
      have hb' := (Comb.subtree_branching_iff (pc_chain_subtree D hS β) a.1.2).mp hb
      have hl := ℓ.2
      rw [hℓ] at hl
      exact Comb.TreePath.not_mem_branching_of_mem_leaves _ hl hb'
  exact pc_chain_partner_tree' (D.tree β) (nodeSign S.sig β.1) (D.garden hS) (inflatedPosition S D.tree β.toNode)
    a.1 ℓ hleaf ha hℓ (fun p hp => D.chain_pair_mem hS (D.garden_decodes hS) β p hp)

/-- The pair trees at a native chain node are the tree of the chain. -/
theorem pc_pairTrees_chain (a : GNode (nativeChainLayered D hS layer hLayer β).garden.tree) :
    pairTrees (D.garden hS) (chainContextNode D hS β a).1 = (pcRI D β, pcRI D β) := by
  unfold pairTrees
  by_cases hl : ∃ ℓ : GLeaf (D.garden hS).tree, ℓ.1 = (chainContextNode D hS β a).1
  · rw [dite_eq_left hl]
    have ha : a.1.2 ≠ (D.tree β).lonePath := by
      intro h
      have hc := (pc_chain_core_iff D hS layer hLayer β a).mpr h
      obtain ⟨β', hβ'⟩ := hc
      have hb := (D.coreBranch hS β').2
      have hl2 := hl.choose.2
      rw [hl.choose_spec, hβ'] at hl2
      exact Comb.TreePath.not_mem_branching_of_mem_leaves _ hl2 hb
    exact Prod.ext rfl (pc_chain_partner_tree D hS layer hLayer β a ha hl.choose hl.choose_spec)
  · rw [dite_eq_right hl]
    rfl

/-- **The anchored profile at a native chain node** is the type profile of the chain's tree. -/
theorem pc_anch_ch (hcap : ∀ j ∈ J, (D.garden hS).tree j = TTree.leaf) {d' : ℕ}
    (h : ℕ → Fin w → Fin w → Mom d' → ℝ) (L : ℝ) (roots : Fin w → (Fin d' → ℤ))
    (a : GNode (nativeChainLayered D hS layer hLayer β).garden.tree) :
    anchProfiles J (layeredReconstruction D hS layer hLayer) h L roots (chainContextNode D hS β a).1 =
      h ((nativeChainLayered D hS layer hLayer β).layer a) (pcRI D β) (pcRI D β) := by
  have hnc : ¬ InCapNative D hS J (chainContextNode D hS β a) :=
    IntGeo.not_inCapNative_of_slot D hS J (.inr β) (fun q h => by cases h) a
  rw [IntGeo.anchProfiles_eq D hS layer hLayer J hcap h L roots _ hnc]
  have e := pc_pairTrees_chain D hS layer hLayer β a
  change pairTrees (layeredReconstruction D hS layer hLayer).garden (chainContextNode D hS β a).1 = _ at e
  unfold typeProfiles
  split_ifs with hn
  · rw [e]
    rfl
  · exact absurd (chainContextNode D hS β a).2 hn

/-! ### The pins at a chain branch -/

variable (hcap : ∀ j ∈ J, (D.garden hS).tree j = TTree.leaf)
include hcap

/-- No branch at a non-lone chain node is a capped flower parent. -/
theorem pc_not_cfp_chain (x : GNode (nativeChainLayered D hS layer hLayer β).garden.tree)
    (hx : x.1.2 ≠ (D.tree β).lonePath) (B : GBranch (D.forest hS)) (hB : B.toNode = chainContextNode D hS β x) :
    ¬ IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J B := by
  intro hcfp
  have hnc : ∀ b, B ≠ D.coreBranch hS b := fun b he =>
    hx ((pc_chain_core_iff D hS layer hLayer β x).mp ⟨b, hB.symm.trans (by rw [he])⟩)
  have hin := (IntGeo.capParent_inCapNative D hS layer hLayer J hcap B hcfp hnc).1
  rw [hB] at hin
  exact IntGeo.not_inCapNative_of_slot D hS J (.inr β) (fun q h => by cases h) x hin

omit hcap in
theorem pc_nativeBr_inr_node (b : GBranch (nativeChainLayered D hS layer hLayer β).garden.tree) :
    (MkSlotsB.nativeBr D hS (.inr β) b).toNode = chainContextNode D hS β b.toNode := Subtype.ext rfl

omit hcap in
theorem pc_lone_not_branch (b : GBranch (nativeChainLayered D hS layer hLayer β).garden.tree) :
    b.1.2 ≠ (D.tree β).lonePath := by
  intro h
  have hb := b.2
  rw [h] at hb
  exact Comb.TreePath.not_mem_branching_of_mem_leaves _
    (chain_lone_mem_leaves (D.tree β) (nodeSign S.sig β.1)) hb

omit hcap in
theorem pc_cfp_nativeBr_ch' (b : GBranch (nativeChainLayered D hS layer hLayer β).garden.tree) :
    (MkSlotsB.nativeBr D hS (.inr β) b).1 =
      ((inflatedPosition S D.tree β.toNode).1, (inflatedPosition S D.tree β.toNode).2 ++ b.1.2) := rfl

/-- A chain branch is never a capped flower parent. -/
theorem pc_cfp_nativeBr_ch (b : GBranch (nativeChainLayered D hS layer hLayer β).garden.tree) :
    ¬ IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (MkSlotsB.nativeBr D hS (.inr β) b) :=
  pc_not_cfp_chain D hS layer hLayer J β hcap b.toNode (pc_lone_not_branch D hS layer hLayer β b) _
    (pc_nativeBr_inr_node D hS layer hLayer β b)

omit hcap in
/-- Root predicate at a chain branch. -/
theorem pc_root_nativeBr_ch (b : GBranch (nativeChainLayered D hS layer hLayer β).garden.tree) :
    (MkSlotsB.nativeBr D hS (.inr β) b).1.2 = [] ↔ b.1.2 = [] ∧ pcRR D β := by
  show (inflatedPosition S D.tree β.toNode).2 ++ b.1.2 = [] ↔ _
  rw [List.append_eq_nil_iff]
  exact And.comm

/-- `dParent` predicate at a chain branch: the parent of the lone leaf, below a capped flower parent core. -/
theorem pc_par_nativeBr_ch (b : GBranch (nativeChainLayered D hS layer hLayer β).garden.tree) :
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
      have hcore := (pc_chain_core_iff D hS layer hLayer β (b.child i)).mpr hl
      obtain ⟨β', hβ'⟩ := hcore
      have hβ : β' = β := by
        have h3 := (pc_chain_core_iff D hS layer hLayer β (b.child i)).mpr hl
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
    · exact (pc_not_cfp_chain D hS layer hLayer J β hcap (b.child i) hl C hCn hC).elim
  · rintro ⟨⟨i, hi⟩, hcb⟩
    refine ⟨D.coreBranch hS β, hcb, rfl, i, ?_⟩
    show (inflatedPosition S D.tree β.toNode).2 ++ (D.tree β).lonePath =
      ((inflatedPosition S D.tree β.toNode).2 ++ b.1.2) ++ [i]
    rw [← hi, List.append_assoc]

/-! ### The stem at a chain node -/

/-- **A non-lone chain node is on the capped stem iff it lies on the lone path and the core is on the stem.** -/
theorem pc_onCapStem_ch (a : GNode (nativeChainLayered D hS layer hLayer β).garden.tree)
    (ha : a.1.2 ≠ (D.tree β).lonePath) :
    OnCapStem (layeredReconstruction D hS layer hLayer) J (chainContextNode D hS β a) ↔
      a.1.2 <+: (D.tree β).lonePath ∧
        OnCapStem (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS β).toNode := by
  constructor
  · rintro ⟨ℓ, hℓ, h1, r, h2⟩
    have h2' : ((inflatedPosition S D.tree β.toNode).2 ++ a.1.2) ++ r = ℓ.1.2 := h2
    have h1' : ℓ.1.1 = (inflatedPosition S D.tree β.toNode).1 := h1.symm
    have hmem : a.1.2 ++ r ∈ ((D.tree β).plug (nodeSign S.sig β.1) (node3 fun i => D.inflateNode hS (β.child i))).leaves := by
      rw [Comb.subtree_leaves_iff (pc_chain_subtree D hS β)]
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
      have hp := pc_chain_partner_tree D hS layer hLayer β x hn ℓ hx
      have hJ := hℓ.2
      change ((D.garden hS).pair ℓ).1.1 ∈ J at hJ
      rw [hp] at hJ
      have e : pcRI D β = β.1.1 := inflatedPosition_index S D.tree β.toNode
      rw [e] at hJ
      exact IntGeo.no_branch_of_leafTree (hcap _ hJ) β rfl
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

end Chain

end WaveTurbulence.Flower.MkSlotsO
