/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.DescendantReplacement

/-! # Collapsing an actual embedded paired-tree interval

Replace the upper subtree by the lower subtree and pull back the source
matching on exactly its surviving leaves. The removed interval is completely
paired, and its upper/lower root signs agree, both by the source premises.
-/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem collapseData_frame {w : ℕ} {tree : Fin w → TTree} {a b : GNode tree} (h : a.IsDesc b) :
    b.1 = addrExt a.1 (Comb.collapseDataOfDesc h).path :=
  Prod.ext h.1.symm (Comb.collapseDataOfDesc h).path_eq.symm

/-- The surviving source leaves are exactly the complement of the removed interval. -/
theorem outside_interval_iff {w : ℕ} {tree : Fin w → TTree} (a b : GNode tree) (ℓ : GLeaf tree) :
    ℓ ∉ a.leavesBelow \ b.leavesBelow ↔ ¬ Below a.1 ℓ.1 ∨ Below b.1 ℓ.1 := by
  classical
  simp only [Finset.mem_sdiff,leafBelow_iff_below,not_and_or,not_not]

/-- Exact unchanged/prefix-relocated leaf embedding for a source paired-tree collapse. -/
noncomputable def pairedTreeLeafEmbedding {w : ℕ} {G : Garden w} {a b : GNode G.tree}
    (h : Comb.IsSubPairedTree G a b) :
    GLeaf (Comb.replaceNodeForest G.tree a (Comb.nodeSubtree b)) ↪ GLeaf G.tree :=
  replacementLeafEmbedding G.tree a b (Comb.collapseDataOfDesc h.1).path (collapseData_frame h.1)

/-- No leaf outside the removed upper-minus-lower family is lost. -/
theorem pairedTreeLeafEmbedding_range {w : ℕ} {G : Garden w} {a b : GNode G.tree}
    (h : Comb.IsSubPairedTree G a b) (y : GLeaf G.tree) :
    y ∈ Set.range (pairedTreeLeafEmbedding h) ↔ y ∉ a.leavesBelow \ b.leavesBelow := by
  constructor
  · rintro ⟨x,hx⟩
    have hv := congrArg (fun z : GLeaf G.tree => z.1) hx
    have he := (replacement_leaf_image G.tree a b (Comb.collapseDataOfDesc h.1).path
      (collapseData_frame h.1) y).mpr ⟨x,hv⟩
    exact (outside_interval_iff a b y).mpr he
  · intro hy
    obtain ⟨x,hx⟩ := (replacement_leaf_image G.tree a b (Comb.collapseDataOfDesc h.1).path
      (collapseData_frame h.1) y).mp ((outside_interval_iff a b y).mp hy)
    exact ⟨x,Subtype.ext hx⟩

/-- The actual ambient partner of a surviving leaf is another surviving leaf. -/
theorem pairedTreeLeafEmbedding_closed {w : ℕ} {G : Garden w} {a b : GNode G.tree}
    (h : Comb.IsSubPairedTree G a b) :
    ∀ x, ∃ y, pairedTreeLeafEmbedding h y = G.pair (pairedTreeLeafEmbedding h x) := by
  intro x
  have hx := (pairedTreeLeafEmbedding_range h (pairedTreeLeafEmbedding h x)).mp ⟨x,rfl⟩
  have hp := paired_complement_closed G _ h.2 (pairedTreeLeafEmbedding h x) hx
  exact (pairedTreeLeafEmbedding_range h (G.pair (pairedTreeLeafEmbedding h x))).mpr hp

/-- Root-sign equality of the paired interval preserves all transported leaf signs. -/
theorem pairedTreeLeafEmbedding_sign {w : ℕ} {G : Garden w} {a b : GNode G.tree}
    (h : Comb.IsSubPairedTree G a b) (x : GLeaf (Comb.replaceNodeForest G.tree a (Comb.nodeSubtree b))) :
    nodeSign G.sig x.1 = nodeSign G.sig (pairedTreeLeafEmbedding h x).1 := by
  change nodeSign G.sig x.1 = nodeSign G.sig (stretch a.1 (Comb.collapseDataOfDesc h.1).path x.1)
  symm
  apply stretch_sign G.sig a.1 (Comb.collapseDataOfDesc h.1).path ?_ x.1
  rw [← nodeSign_addrExt,← collapseData_frame h.1]
  exact (Comb.subPairedTree_sign h).symm

/-- Collapse the embedded paired tree to its lone root, retaining the entire lower subtree. -/
noncomputable def collapsePairedTreeGarden {w : ℕ} {G : Garden w} {a b : GNode G.tree}
    (h : Comb.IsSubPairedTree G a b) : Garden w :=
  Comb.gardenOnLeafEmbedding G.sig (pairedTreeLeafEmbedding h)
    (pairedTreeLeafEmbedding_closed h) (pairedTreeLeafEmbedding_sign h)

theorem collapsePairedTreeGarden_sig {w : ℕ} {G : Garden w} {a b : GNode G.tree}
    (h : Comb.IsSubPairedTree G a b) : (collapsePairedTreeGarden h).sig = G.sig := rfl

theorem collapsePairedTreeGarden_tree {w : ℕ} {G : Garden w} {a b : GNode G.tree}
    (h : Comb.IsSubPairedTree G a b) :
    (collapsePairedTreeGarden h).tree = Comb.replaceNodeForest G.tree a (Comb.nodeSubtree b) := rfl

/-- Exact source partner transport in the collapsed garden. -/
theorem collapsePairedTreeGarden_pair {w : ℕ} {G : Garden w} {a b : GNode G.tree}
    (h : Comb.IsSubPairedTree G a b) (x : GLeaf (collapsePairedTreeGarden h).tree) :
    pairedTreeLeafEmbedding h ((collapsePairedTreeGarden h).pair x) = G.pair (pairedTreeLeafEmbedding h x) :=
  Comb.leafPairPullback_spec (pairedTreeLeafEmbedding h) (pairedTreeLeafEmbedding_closed h) x

/-- Ordinary source gardens stay ordinary under paired-tree collapse. -/
theorem collapsePairedTreeGarden_plain {w : ℕ} {G : Garden w} {a b : GNode G.tree}
    (h : Comb.IsSubPairedTree G a b) (hG : G.IsPlain) : (collapsePairedTreeGarden h).IsPlain :=
  Comb.gardenOnLeafEmbedding_plain G.sig _ (pairedTreeLeafEmbedding_closed h) (pairedTreeLeafEmbedding_sign h) hG

/-- The collapse removes exactly the source embedded paired-tree order. -/
theorem collapsePairedTreeGarden_order {w : ℕ} {G : Garden w} {a b : GNode G.tree}
    (h : Comb.IsSubPairedTree G a b) :
    (collapsePairedTreeGarden h).order + (Comb.embeddedPairedTree h).order = G.order := by
  have ho := Comb.replaceNodeForest_order G.tree a (Comb.nodeSubtree b)
  have ht := Comb.embeddedPairedTree_order h
  change (collapsePairedTreeGarden h).order + (Comb.nodeSubtree a).order = G.order + (Comb.nodeSubtree b).order at ho
  omega

end WaveTurbulence.Reg.Skeleton
