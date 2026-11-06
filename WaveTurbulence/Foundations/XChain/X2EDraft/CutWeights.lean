/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.X2EDraft.FlowerSumTops
public import WaveTurbulence.Foundations.XChain.X2EDraft.FlowerConds
public import WaveTurbulence.Foundations.XChain.LayerCutParents
public import WaveTurbulence.Foundations.XChain.LayerCutAttachments
public import WaveTurbulence.Foundations.XChain.CplDraft.DtKernel

/-!
# X2E-5, step 4: the cutoff weights of a flower graft

**Statements.**
- `isTopLeaf_iff` (any layered garden with layers `≤ p`): the top leaves of the gate are the non-root leaves of the
  layer-`p` cut;
- on the flower graft of `x : FlowerAt`: the `M₁` set of tree `j` is the image of the non-flower leaves of `tops j`
  (`prodCut1_topLeaves_eq`), the `M₂` set is the image of the stem branches `≠ 𝔣^pr` of `tops j` (`prodCut2_stem_eq`);
- **`cutWeightsOK`**: `CutWeightsOK` for all cutoffs.
-/

@[expose] public section

namespace WaveTurbulence.X2E

open Finset Induct SysAPI
open scoped Classical

/-- **The top leaves are the non-root leaves of the layer-`p` cut.** -/
theorem isTopLeaf_iff {w : ℕ} (LG : LayeredGarden w) (p : ℕ) (hbound : ∀ a, LG.layer a ≤ p)
    (a : GNode LG.garden.tree) :
    LG.IsTopLeaf p a ↔ a.1.2 ∈ (layerCutForest LG p a.1.1).leaves ∧ a.1.2 ≠ [] := by
  constructor
  · rintro ⟨h1, hne, hpar⟩
    refine ⟨?_, hne⟩
    have hm := mem_cutTree_nodes_of_no_strict_stop (LG.garden.tree a.1.1) (layerCutStop LG p a.1.1) a.1.2 a.2
      (no_strict_layerCutStop_of_parentLayer_eq LG p a hpar)
    rcases (TTree.mem_nodes_iff _ _).mp hm with hl | hb
    · exact hl
    · exfalso
      have hge := (layerCutStop_false_iff LG p a).mp (stop_false_of_mem_cutTree_branching _ _ hb)
      rcases h1 with hlt | hleaf
      · omega
      · exact TTree.not_mem_branching_of_mem_leaves _ hleaf (cutTree_branching_subset _ _ hb)
  · rintro ⟨hl, hne⟩
    let c : GLeaf (layerCutForest LG p) := ⟨a.1, hl⟩
    have hc : layerCutNodeEmbedding LG p c.toNode = a := Subtype.ext rfl
    refine ⟨?_, hne, ?_⟩
    · rcases layerCut_leaf_attach_or_terminal LG p hbound c with hat | ⟨hleaf, -⟩
      · rw [hc] at hat
        exact Or.inl (mem_filter.mp hat).2.1
      · exact Or.inr hleaf
    · have h := layerCut_leaf_parentLayer LG p hbound c
      rwa [hc] at h

section Graft

variable {d Pm p : ℕ} {ζ : ℤˣ} {tops : Fin (2 * Pm) → FTree} (hF : ∀ j, tops j ≠ FTree.flower)
  (x : FlowerAt Pm p tops) (hsign : ∀ j, (tops j).sign = ζ)

/-- A top node of the flower graft. -/
noncomputable def topNd (j : Fin (2 * Pm)) (a : GNode (single (tops j).toTree)) :
    GNode (x.toData hsign).flowerGraft.garden.tree :=
  topNodeEmbedding (ftop tops) x.partition (fun B => ((x.toData hsign).lowFl B).garden)
    (singleNodeToForest (ftop tops) j a)

theorem topNd_val (j : Fin (2 * Pm)) (a : GNode (single (tops j).toTree)) : (topNd x hsign j a).1 = (j, a.1.2) := rfl

/-- A top branch of the flower graft. -/
noncomputable def topBr (j : Fin (2 * Pm)) (b : GBranch (single (tops j).toTree)) :
    GBranch (x.toData hsign).flowerGraft.garden.tree :=
  gardenBranchEquiv (ftop tops) x.partition (fun B => ((x.toData hsign).lowFl B).garden)
    (.inl (singleBranchToForest (ftop tops) j b))

theorem topBr_val (j : Fin (2 * Pm)) (b : GBranch (single (tops j).toTree)) : (topBr x hsign j b).1 = (j, b.1.2) :=
  gardenBranchEquiv_top_val _ _ _ _

theorem leaf_ne_flowerLeaf_iff (j : Fin (2 * Pm)) (ℓ : GLeaf (single (tops j).toTree)) :
    ℓ ≠ (tops j).flowerLeaf ↔ ℓ.1.2 ≠ (tops j).flowerPath := by
  constructor
  · intro h he
    exact h (Subtype.ext (Prod.ext (Subsingleton.elim _ _) he))
  · intro h he
    exact h (congrArg (fun l : GLeaf (single (tops j).toTree) => l.1.2) he)

theorem topNd_injective (j : Fin (2 * Pm)) :
    Function.Injective fun ℓ : GLeaf (single (tops j).toTree) => topNd x hsign j ℓ.toNode := by
  intro ℓ ℓ' h
  have h1 := congrArg (fun a => a.1.2) h
  simp only [topNd_val] at h1
  exact Subtype.ext (Prod.ext (Subsingleton.elim _ _) h1)

include hF in
/-- **The `M₁` weight of tree `j` of the graft** is the tree weight `Ψ_{j₁}` of the non-flower leaves of `tops j`,
read through the top embedding (a reindexing of the leaf set). -/
theorem prodCut1_topLeaves_eq (L : ℝ) (j₁ : ℕ) (j : Fin (2 * Pm))
    (k : GNode (x.toData hsign).flowerGraft.garden.tree → Mom d) :
    prodDyadicCut L j₁ (univ.filter fun a : GNode (x.toData hsign).flowerGraft.garden.tree =>
        a.1.1 = j ∧ (x.toData hsign).flowerGraft.IsTopLeaf p a ∧ ¬ (x.toData hsign).flowerGraft.IsFlowerNode a)
      (fun a => ‖k a‖) =
    prodDyadicCut L j₁ (univ.erase (tops j).flowerLeaf) (fun ℓ => ‖k (topNd x hsign j ℓ.toNode)‖) := by
  have hb := (x.toData hsign).layer_le
  have hcut := layerCut_toData x hsign
  refine XChain.ProductCut.prodDyadicCut_congr_nbij _ L j₁ (fun ℓ : GLeaf (single (tops j).toTree) => topNd x hsign j ℓ.toNode)
    ?_ (fun ℓ _ ℓ' _ h => topNd_injective x hsign j h) ?_ (fun _ _ => rfl)
  · intro ℓ hℓ
    have hne : ℓ.1.2 ≠ [] := Cpl.ne_nil_of_mem_leaves ((ne_flower_iff _).mp (hF j)) ℓ.2
    have hnfl := (leaf_ne_flowerLeaf_iff j ℓ).mp (mem_erase.mp hℓ).1
    refine mem_filter.mpr ⟨mem_univ _, rfl, (isTopLeaf_iff _ p hb _).mpr ⟨?_, hne⟩, ?_⟩
    · rw [congrFun hcut]
      exact ℓ.2
    · rw [(x.toData hsign).isFlowerNode_iff]
      exact hnfl
  · intro a ha
    obtain ⟨-, hj, htl, hnf⟩ := mem_filter.mp (Finset.mem_coe.mp ha)
    obtain ⟨hl, -⟩ := (isTopLeaf_iff _ p hb a).mp htl
    rw [congrFun hcut a.1.1, hj] at hl
    obtain ⟨ℓ, hℓv⟩ : ∃ ℓ : GLeaf (single (tops j).toTree), ℓ.1 = (0, a.1.2) := ⟨⟨(0, a.1.2), hl⟩, rfl⟩
    have hℓ2 : ℓ.1.2 = a.1.2 := congrArg Prod.snd hℓv
    have hℓ : ℓ ∈ univ.erase (tops j).flowerLeaf := by
      refine mem_erase.mpr ⟨(leaf_ne_flowerLeaf_iff j ℓ).mpr fun he => hnf ?_, mem_univ _⟩
      rw [(x.toData hsign).isFlowerNode_iff]
      change a.1.2 = (tops a.1.1).flowerPath
      rw [hj, ← hℓ2]
      exact he
    exact ⟨ℓ, Finset.mem_coe.mpr hℓ, Subtype.ext ((topNd_val x hsign j ℓ.toNode).trans (Prod.ext hj.symm hℓ2))⟩

theorem fp_eq_of (j c : Fin (2 * Pm)) (hc : c = j) (q : TTree.Path)
    (h : q = ((tops c).flowerParent (hF c)).1.2) : q = ((tops j).flowerParent (hF j)).1.2 := by
  subst hc
  exact h

theorem omegaNode_topBr (j : Fin (2 * Pm)) (b : GBranch (single (tops j).toTree))
    (k : GNode (x.toData hsign).flowerGraft.garden.tree → Mom d) :
    omegaNode (x.toData hsign).flowerGraft.garden k (topBr x hsign j b) =
      resFactor (k (topNd x hsign j (b.child 0))) (k (topNd x hsign j (b.child 1)))
        (k (topNd x hsign j (b.child 2))) (k (topNd x hsign j b.toNode)) := by
  unfold omegaNode
  congr 1

theorem topBr_injective (j : Fin (2 * Pm)) :
    Function.Injective fun b : GBranch (single (tops j).toTree) => topBr x hsign j b := by
  intro b b' h
  have h1 := congrArg (fun a => a.1.2) h
  simp only [topBr_val] at h1
  exact Subtype.ext (Prod.ext (Subsingleton.elim _ _) h1)

include hF in
/-- **The `M₂` weight of tree `j` of the graft** is the tree weight `Ψ_{j₂}` of the `|Ω|` at the stem branches
`≠ 𝔣^pr` of `tops j`, read through the top embedding (a reindexing of the branch set). -/
theorem prodCut2_stem_eq (L : ℝ) (j₂ : ℕ) (j : Fin (2 * Pm))
    (k : GNode (x.toData hsign).flowerGraft.garden.tree → Mom d) :
    prodDyadicCut L j₂ (univ.filter fun b : GBranch (x.toData hsign).flowerGraft.garden.tree => b.1.1 = j ∧
        (x.toData hsign).flowerGraft.OnStem b.toNode ∧ ¬ (x.toData hsign).flowerGraft.garden.IsFlowerParent b)
      (fun b => |omegaNode (x.toData hsign).flowerGraft.garden k b|) =
    prodDyadicCut L j₂ (univ.filter fun b : GBranch (single (tops j).toTree) => OnStemT (tops j) b ∧
        b ≠ (tops j).flowerParent (hF j))
      (fun b => |resFactor (k (topNd x hsign j (b.child 0))) (k (topNd x hsign j (b.child 1)))
        (k (topNd x hsign j (b.child 2))) (k (topNd x hsign j b.toNode))|) := by
  refine XChain.ProductCut.prodDyadicCut_congr_nbij _ L j₂ (fun b' : GBranch (single (tops j).toTree) => topBr x hsign j b')
    ?_ (fun b _ b' _ h => topBr_injective x hsign j h) ?_ (fun b' _ => ?_)
  · intro b' hb'
    obtain ⟨-, hst, hne⟩ := mem_filter.mp hb'
    have hv := topBr_val x hsign j b'
    refine mem_filter.mpr ⟨mem_univ _, congrArg Prod.fst hv, ?_, fun hfp => hne ?_⟩
    · refine ⟨(x.toData hsign).flLeaf j, ((x.toData hsign).isFlower_iff _).mpr
        (by rw [(x.toData hsign).flLeaf_val]), ?_, ?_⟩
      · change (topBr x hsign j b').1.1 = ((x.toData hsign).flLeaf j).1.1
        rw [hv, (x.toData hsign).flLeaf_val]
      · change (topBr x hsign j b').1.2 <+: ((x.toData hsign).flLeaf j).1.2
        rw [hv, (x.toData hsign).flLeaf_val]
        exact hst
    · have h := (isFlowerParent_toData_iff x hsign hF _).mp hfp
      have h' := fp_eq_of hF j _ (congrArg Prod.fst hv) _ h
      rw [congrArg Prod.snd hv] at h'
      exact Subtype.ext (Prod.ext (Subsingleton.elim _ _) h')
  · intro b hb
    obtain ⟨-, hj, hst, hnfp⟩ := mem_filter.mp (Finset.mem_coe.mp hb)
    obtain ⟨ℓ, hfl, hdesc⟩ := hst
    have hℓ := ((x.toData hsign).isFlower_iff ℓ).mp hfl
    have hpre : b.1.2 <+: (tops j).flowerPath := by
      have h2 : b.1.2 <+: ℓ.1.2 := hdesc.2
      have h1 : b.1.1 = ℓ.1.1 := hdesc.1
      rw [hℓ, ← h1, hj] at h2
      exact h2
    have hneq : b.1.2 ≠ (tops j).flowerPath := by
      intro he
      have hbr : b.1.2 ∈ ((x.toData hsign).flowerGraft.garden.tree b.1.1).branching := b.2
      have hlf : ((x.toData hsign).flLeaf j).1.2 ∈
          ((x.toData hsign).flowerGraft.garden.tree ((x.toData hsign).flLeaf j).1.1).leaves :=
        ((x.toData hsign).flLeaf j).2
      rw [(x.toData hsign).flLeaf_val] at hlf
      rw [hj, he] at hbr
      exact TTree.not_mem_branching_of_mem_leaves _ hlf hbr
    obtain ⟨r, hr⟩ := hpre
    have hr0 : r ≠ [] := fun h0 => hneq (by rw [← hr, h0, List.append_nil])
    have hbr : b.1.2 ∈ (tops j).toTree.branching := by
      obtain ⟨i, r', rfl⟩ := List.exists_cons_of_ne_nil hr0
      refine TTree.branching_of_append_mem _ (i := i) (TTree.mem_nodes_of_prefix _
        (TTree.leaves_subset_nodes _ (tops j).flowerPath_mem_leaves) ⟨r', ?_⟩)
      rw [← hr]
      simp
    obtain ⟨b', hb'v⟩ : ∃ b' : GBranch (single (tops j).toTree), b'.1 = (0, b.1.2) := ⟨⟨(0, b.1.2), hbr⟩, rfl⟩
    have hb'2 : b'.1.2 = b.1.2 := congrArg Prod.snd hb'v
    have hb' : b' ∈ univ.filter fun b : GBranch (single (tops j).toTree) => OnStemT (tops j) b ∧
        b ≠ (tops j).flowerParent (hF j) := by
      refine mem_filter.mpr ⟨mem_univ _, ⟨r, by rw [hb'2]; exact hr⟩, fun he => hnfp ?_⟩
      rw [isFlowerParent_toData_iff x hsign hF b, hj, ← hb'2]
      exact congrArg (fun c : GBranch (single (tops j).toTree) => c.1.2) he
    exact ⟨b', Finset.mem_coe.mpr hb', Subtype.ext ((topBr_val x hsign j b').trans (Prod.ext hj.symm hb'2))⟩
  · show |omegaNode (x.toData hsign).flowerGraft.garden k (topBr x hsign j b')| = _
    rw [omegaNode_topBr x hsign j b' k]

include hF in
/-- **The cutoff weights of a flower graft are the products of the tree cutoff weights.** -/
theorem cutWeightsOK (L : ℝ) (cut1 cut2 : Option ℕ) : CutWeightsOK L (d := d) hF x hsign cut1 cut2 := by
  refine ⟨fun j₁ _ k => ?_, fun j₂ _ k => ?_⟩
  · unfold LayeredGarden.cutWeight1P
    refine prod_congr rfl fun j _ => ?_
    unfold treeCut1K
    exact prodCut1_topLeaves_eq hF x hsign L j₁ j k
  · unfold LayeredGarden.cutWeight2P
    refine prod_congr rfl fun j _ => ?_
    unfold treeCut2K
    exact prodCut2_stem_eq hF x hsign L j₂ j k

end Graft

end WaveTurbulence.X2E
