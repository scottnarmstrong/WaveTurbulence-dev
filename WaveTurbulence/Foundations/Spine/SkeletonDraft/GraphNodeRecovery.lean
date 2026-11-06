/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.IncomingPorts

/-! # Exact recovery of source nodes and branch labels from the port graph -/

public section
namespace WaveTurbulence.Reg.Skeleton.LabelledGarden
open TTree

/-- Equal incoming slots in equal graphs identify the same source branch label. -/
theorem branch_transfer {w : ℕ} {B : Type*} (G H : LabelledGarden w B) (hg : G.graph = H.graph)
    (a : GNode G.garden.tree) (b : GNode H.garden.tree) (he : G.incoming a = H.incoming b)
    (c : GBranch G.garden.tree) (hc : c.toNode = a) :
    ∃ d : GBranch H.garden.tree, d.toNode = b ∧ H.label d = G.label c := by
  apply H.branch_of_mate_incoming b (G.label c)
  have hm := G.graph_mate_incoming_branch c
  rw [hc,hg,he] at hm
  exact hm

/-- Walk from each original root along the ordered child slots. Equal labelled
graphs give actual nodes at exactly the same tree address, retaining incoming slots. -/
theorem node_transfer {w : ℕ} {B : Type*} (G H : LabelledGarden w B) (hg : G.graph = H.graph)
    (a : GNode G.garden.tree) :
    ∃ b : GNode H.garden.tree, b.1 = a.1 ∧ G.incoming a = H.incoming b := by
  have h : ∀ (p : Path) (j : Fin w) (hp : p ∈ (G.garden.tree j).nodes),
      ∃ b : GNode H.garden.tree, b.1 = (j,p) ∧ G.incoming ⟨(j,p),hp⟩ = H.incoming b := by
    intro p
    induction p using List.reverseRecOn with
    | nil =>
      intro j hp
      refine ⟨GNode.root H.garden.tree j,rfl,?_⟩
      change G.incoming (GNode.root G.garden.tree j) = H.incoming (GNode.root H.garden.tree j)
      rw [incoming_root,incoming_root]
    | append_singleton p i ih =>
      intro j hp
      have hb : p ∈ (G.garden.tree j).branching := Comb.TreePath.branching_of_append_mem _ hp
      let c : GBranch G.garden.tree := ⟨(j,p),hb⟩
      obtain ⟨b,hbval,hin⟩ := ih j c.toNode.2
      change G.incoming c.toNode = H.incoming b at hin
      obtain ⟨d,hdnode,hdlabel⟩ := G.branch_transfer H hg c.toNode b hin c rfl
      have hdval : d.1 = (j,p) := (congrArg (fun q : GNode H.garden.tree => q.1) hdnode).trans hbval
      refine ⟨d.child i,?_,?_⟩
      · change (d.1.1,d.1.2 ++ [i]) = (j,p ++ [i])
        have hj := congrArg (fun z : Fin w × Path => z.1) hdval
        have hp := congrArg (fun z : Fin w × Path => z.2) hdval
        exact Prod.ext hj (congrArg (fun q => q ++ [i]) hp)
      · change G.incoming (c.child i) = H.incoming (d.child i)
        rw [incoming_child,incoming_child,hdlabel]
  exact h a.1.2 a.1.1 a.2

/-- In equal graphs, any two actual nodes at the same address have the same incoming slot. -/
theorem incoming_eq_of_address {w : ℕ} {B : Type*} (G H : LabelledGarden w B) (hg : G.graph = H.graph)
    (a : GNode G.garden.tree) (b : GNode H.garden.tree) (he : a.1 = b.1) : G.incoming a = H.incoming b := by
  obtain ⟨c,hc,hin⟩ := G.node_transfer H hg a
  have hcb : c = b := Subtype.ext (hc.trans he)
  rw [hcb] at hin
  exact hin

/-- Persistent branch identifiers are recovered at every actual branching address. -/
theorem label_eq_of_address {w : ℕ} {B : Type*} (G H : LabelledGarden w B) (hg : G.graph = H.graph)
    (a : GBranch G.garden.tree) (b : GBranch H.garden.tree) (he : a.1 = b.1) : G.label a = H.label b := by
  have hin := G.incoming_eq_of_address H hg a.toNode b.toNode he
  have hm := G.graph_mate_incoming_branch a
  rw [hg,hin,H.graph_mate_incoming_branch] at hm
  exact (Sum.inr.inj (congrArg Prod.fst hm)).symm

/-- Node membership at every literal path is determined by the labelled graph. -/
theorem node_mem_transfer {w : ℕ} {B : Type*} (G H : LabelledGarden w B) (hg : G.graph = H.graph)
    (j : Fin w) (p : Path) (hp : p ∈ (G.garden.tree j).nodes) : p ∈ (H.garden.tree j).nodes := by
  obtain ⟨b,hb,_⟩ := G.node_transfer H hg ⟨(j,p),hp⟩
  have hm := b.2
  rw [hb] at hm
  exact hm

/-- Branch membership at every literal path is determined by the labelled graph. -/
theorem branch_mem_transfer {w : ℕ} {B : Type*} (G H : LabelledGarden w B) (hg : G.graph = H.graph)
    (j : Fin w) (p : Path) (hp : p ∈ (G.garden.tree j).branching) : p ∈ (H.garden.tree j).branching := by
  let c : GBranch G.garden.tree := ⟨(j,p),hp⟩
  obtain ⟨b,hb,hin⟩ := G.node_transfer H hg c.toNode
  obtain ⟨d,hd,_⟩ := G.branch_transfer H hg c.toNode b hin c rfl
  have hv : d.1 = (j,p) := (congrArg (fun q : GNode H.garden.tree => q.1) hd).trans hb
  have hm := d.2
  rw [hv] at hm
  exact hm

end WaveTurbulence.Reg.Skeleton.LabelledGarden
