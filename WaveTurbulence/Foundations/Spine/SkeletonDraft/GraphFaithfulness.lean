/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.GraphNodeRecovery

/-! # The labelled graph retains the full ordinary source garden carrier

Ordered roots and slots determine every tree address; matched incoming leaf
slots determine every partner. The signature is retained as source typing data.
For ordinary gardens all marks are none, so no mark information is lost.
-/

public section
namespace WaveTurbulence.Reg.Skeleton.LabelledGarden
open TTree

/-- Leaf membership is reconstructed from the graph's node and branch predicates. -/
theorem leaf_mem_transfer {w : ℕ} {B : Type*} (G H : LabelledGarden w B) (hg : G.graph = H.graph)
    (j : Fin w) (p : Path) (hp : p ∈ (G.garden.tree j).leaves) : p ∈ (H.garden.tree j).leaves := by
  let ℓ : GLeaf G.garden.tree := ⟨(j,p),hp⟩
  have hn := G.node_mem_transfer H hg j p ℓ.toNode.2
  rcases (Comb.TreePath.mem_nodes_iff _ _).mp hn with hl | hb
  · exact hl
  · have hbG := H.branch_mem_transfer G hg.symm j p hb
    exact (Comb.TreePath.not_mem_branching_of_mem_leaves _ hp hbG).elim

/-- The actual ordered forest is fixed by the labelled port matching. -/
theorem forest_eq_of_graph_eq {w : ℕ} {B : Type*} (G H : LabelledGarden w B) (hg : G.graph = H.graph) :
    G.garden.tree = H.garden.tree := by
  funext j
  apply tree_eq_of_leaves_eq
  apply Finset.ext
  intro p
  exact ⟨G.leaf_mem_transfer H hg j p,H.leaf_mem_transfer G hg.symm j p⟩

/-- Actual leaf partners have the same addresses in equal labelled graphs. -/
theorem pair_address_transfer {w : ℕ} {B : Type*} (G H : LabelledGarden w B) (hg : G.graph = H.graph)
    (ℓ : GLeaf G.garden.tree) (q : GLeaf H.garden.tree) (hq : ℓ.1 = q.1) :
    (G.garden.pair ℓ).1 = (H.garden.pair q).1 := by
  have hin := G.incoming_eq_of_address H hg ℓ.toNode q.toNode hq
  have hm : G.graph.mate (G.incoming ℓ.toNode) = H.graph.mate (H.incoming q.toNode) := by rw [hg,hin]
  have hp := (G.graph_mate_incoming_leaf ℓ).symm.trans (hm.trans (H.graph_mate_incoming_leaf q))
  obtain ⟨c,hc,hcin⟩ := G.node_transfer H hg (G.garden.pair ℓ).toNode
  have he := H.incoming_injective (hcin.symm.trans hp)
  exact hc.symm.trans (congrArg (fun a : GNode H.garden.tree => a.1) he)

/-- Faithfulness on ordinary gardens with the inherited root signature.
This is equality of the complete source carrier, not graph isomorphism. -/
theorem garden_eq_of_graph_eq {w : ℕ} {B : Type*} (G H : LabelledGarden w B)
    (hG : G.garden.IsPlain) (hH : H.garden.IsPlain) (hsig : G.garden.sig = H.garden.sig)
    (hg : G.graph = H.graph) : G.garden = H.garden := by
  have htree := G.forest_eq_of_graph_eq H hg
  have hp : ∀ (ℓ : GLeaf G.garden.tree) (q : GLeaf H.garden.tree), ℓ.1 = q.1 →
      (G.garden.pair ℓ).1 = (H.garden.pair q).1 := G.pair_address_transfer H hg
  obtain ⟨⟨gs,gt,gp,gm,gpp,geq,gsgn⟩,glab⟩ := G
  obtain ⟨⟨hs,ht,hp',hm,hpp,heq,hsgn⟩,hlab⟩ := H
  change gt = ht at htree
  change gs = hs at hsig
  subst ht
  subst hs
  have hpair : gp = hp' := by
    funext ℓ
    exact Subtype.ext (hp ℓ ℓ rfl)
  have hmark : gm = hm := funext fun ℓ => (hG ℓ).trans (hH ℓ).symm
  cases hpair
  cases hmark
  rfl

end WaveTurbulence.Reg.Skeleton.LabelledGarden
