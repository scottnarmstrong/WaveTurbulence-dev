/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkMark.StemZero
public import WaveTurbulence.Foundations.Flower.MkMark.Transport
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflateNodeEquations
public import WaveTurbulence.Foundations.RegStruct.ChainNodeBounds

/-! # B2b MK-MARK: skeleton coordinates of a decoded garden

A node of a garden decoded from `(S, D)` is `IP(o) ++ q` for its owner `o` and a *local path* `q` in the local tree
of `o` (`localTree`): the regular tree of a branch with its hole (the branch itself) plugged by a leaf, or the couple
tree inflated at a leaf (`node_coord_iff`, (N1) of the B2b plan). Children stay in the owner's region, except at the
hole of a branch, where the `i`-th child is the top of the region of the `i`-th skeleton child (`owner_child`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton

namespace WaveTurbulence.Flower.MkMark

variable {w : ℕ}

section Owners
variable (S : Garden w) (X : GBranch S.tree → RegChain)

/-- The inflated position of a node is owned by that node. -/
theorem owner_inflatedPosition (c : GNode S.tree) : owner S X (inflatedPosition S X c) = c := by
  rw [← mem_ownRegion_iff]
  refine ⟨addrBelow_refl _, fun c' hc hne hb => ?_⟩
  have hd := isDesc_of_addrBelow S X hb
  have h1 : c.1.2.length ≤ c'.1.2.length := hc.2.length_le
  have h2 : c'.1.2.length ≤ c.1.2.length := hd.2.length_le
  exact hne (gnode_eq_of_val hc.1.symm (hc.2.eq_of_length (le_antisymm h1 h2)).symm)

/-- Ownership by a branch: below its inflated position and below none of its children's. -/
theorem owner_eq_branch' {b : GBranch S.tree} {y : Address w}
    (hy : AddrBelow (inflatedPosition S X b.toNode) y)
    (hn : ∀ i, ¬ AddrBelow (inflatedPosition S X (b.child i)) y) : owner S X y = b.toNode := by
  rw [← mem_ownRegion_iff]
  refine ⟨hy, fun c hc hne hcy => ?_⟩
  obtain ⟨h1, r, hr⟩ := hc
  cases r with
  | nil => exact hne (gnode_eq_of_val h1.symm (by simpa using hr.symm))
  | cons i r =>
    have hci : (b.child i).IsDesc c := ⟨h1, r, by
      show b.1.2 ++ [i] ++ r = c.1.2
      rw [← hr]
      simp only [List.append_assoc, List.singleton_append]
      rfl⟩
    exact hn i (addrBelow_trans (addrBelow_inflatedPosition S X hci) hcy)

/-- A child address `z ++ [i]` is owned by the owner of `z`, unless `z` is the hole of a branch, in which case it
is the inflated position of (and owned by) the `i`-th skeleton child. -/
theorem owner_child (z : Address w) (i : Fin 3) :
    owner S X (addrExt z [i]) = owner S X z ∨
      ∃ b : GBranch S.tree, owner S X z = b.toNode ∧ z = addrExt (inflatedPosition S X b.toNode) (X b).lonePath ∧
        addrExt z [i] = inflatedPosition S X (b.child i) ∧ owner S X (addrExt z [i]) = b.child i := by
  set o := owner S X z
  set c := owner S X (addrExt z [i])
  have hz := mem_ownRegion_owner S X z
  have hc := mem_ownRegion_owner S X (addrExt z [i])
  have hoc : o.IsDesc c := owner_isDesc_of_addrBelow S X (addrBelow_addrExt z [i])
  by_cases he : c = o
  · exact Or.inl he
  right
  -- `IP(c)` is a prefix of `z ++ [i]` but not of `z`
  have hnz : ¬ AddrBelow (inflatedPosition S X c) z := hz.2 c hoc he
  have key : ∀ y : Address w, AddrBelow y (addrExt z [i]) → ¬ AddrBelow y z → y = addrExt z [i] := by
    intro y hy hyz
    obtain ⟨h1, s, hs⟩ := hy
    rcases List.prefix_concat_iff.mp ⟨s, hs⟩ with h | h
    · exact Prod.ext h1 h
    · exact absurd ⟨h1, h⟩ hyz
  have hIPc := key _ hc.1 hnz
  -- `c` is a proper descendant of `o`, below some child of `o`
  obtain ⟨h1, r, hr⟩ := hoc
  cases r with
  | nil => exact absurd (gnode_eq_of_val h1.symm (by simpa using hr.symm)) he
  | cons j r =>
    have hm : o.1.2 ++ [j] ++ r ∈ (S.tree o.1.1).nodes := by
      have h0 := c.2
      rw [← hr, ← h1] at h0
      simpa using h0
    have hb : o.1.2 ∈ (S.tree o.1.1).branching := TTree.branching_of_append_mem _ (prefix_mem_nodes _ hm)
    let b : GBranch S.tree := ⟨o.1, hb⟩
    have hbo : b.toNode = o := rfl
    have hbj : (b.child j).IsDesc c := ⟨h1, r, by
      show o.1.2 ++ [j] ++ r = c.1.2
      rw [← hr]
      simp⟩
    have hj := addrBelow_inflatedPosition S X hbj
    rw [hIPc] at hj
    have hnj : ¬ AddrBelow (inflatedPosition S X (b.child j)) z :=
      hz.2 (b.child j) (GBranch.isDesc_child b j) (by
        intro h
        have h2 : b.child j = b.toNode := h.trans hbo.symm
        have := congrArg (fun x : GNode S.tree => x.1.2.length) h2
        simp [GBranch.child, GBranch.toNode] at this)
    have hjz := key _ hj hnj
    rw [inflatedPosition_child] at hjz
    obtain ⟨hzb, hij⟩ := addrExt_inj (show addrExt (addrExt (inflatedPosition S X b.toNode) (X b).lonePath) [j] =
        addrExt z [i] by rw [← hjz]; simp [addrExt])
    subst hij
    have hcb : c = b.child j := by
      have h2 : AddrBelow (inflatedPosition S X c) (inflatedPosition S X (b.child j)) := by
        rw [hIPc, inflatedPosition_child, ← hzb]
        exact ⟨rfl, by simp [addrExt]⟩
      have hd := isDesc_of_addrBelow S X h2
      exact gnode_eq_of_val hbj.1.symm (hbj.2.eq_of_length (le_antisymm hbj.2.length_le hd.2.length_le)).symm
    refine ⟨b, hbo, hzb.symm, ?_, hcb⟩
    exact hIPc.symm.trans (congrArg (inflatedPosition S X) hcb)

end Owners

/-! ## Local trees -/

section Local
variable {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)

theorem leaf_of_not_branch (o : GNode S.tree) (h : o.1.2 ∉ (S.tree o.1.1).branching) :
    o.1.2 ∈ (S.tree o.1.1).leaves :=
  ((TTree.mem_nodes_iff _ _).mp o.2).resolve_right h

/-- The local tree of a skeleton node: the regular tree of a branch with its hole plugged by a leaf, or the couple
tree inflated at a leaf. -/
def localTree (o : GNode S.tree) : TTree :=
  if h : o.1.2 ∈ (S.tree o.1.1).branching then (D.tree ⟨o.1, h⟩).plug (nodeSign S.sig o.1) .leaf
  else D.leafTree hS ⟨o.1, leaf_of_not_branch o h⟩

theorem localTree_branch (b : GBranch S.tree) :
    localTree D hS b.toNode = (D.tree b).plug (nodeSign S.sig b.1) .leaf := by
  unfold localTree
  exact dif_pos b.2

theorem localTree_leaf (l : GLeaf S.tree) : localTree D hS l.toNode = D.leafTree hS l := by
  unfold localTree
  exact dif_neg (TTree.not_mem_branching_of_mem_leaves _ l.2)

theorem mem_nodeAddresses_iff {t : TTree} {a : Address w} {q : TTree.Path} :
    addrExt a q ∈ nodeAddresses t a ↔ q ∈ t.nodes := by
  constructor
  · intro h
    obtain ⟨p, hp, he⟩ := Finset.mem_image.mp h
    have : p = q := by simpa [addrExt] using he
    rwa [← this]
  · intro h
    exact Finset.mem_image.mpr ⟨q, h, rfl⟩

/-- **(N1)** Nodes of the decoded garden in skeleton coordinates. -/
theorem node_coord_iff {G : Garden w} (hd : D.Decodes hS G) (o : GNode S.tree) (q : TTree.Path) :
    (addrExt (inflatedPosition S D.tree o) q).2 ∈ (G.tree (addrExt (inflatedPosition S D.tree o) q).1).nodes ∧
      owner S D.tree (addrExt (inflatedPosition S D.tree o) q) = o ↔ q ∈ (localTree D hS o).nodes := by
  have hsub := D.forest_subtree_position hS o
  rw [decodes_tree hd] at hsub
  have hnode : (addrExt (inflatedPosition S D.tree o) q).2 ∈ (G.tree (addrExt (inflatedPosition S D.tree o) q).1).nodes ↔
      q ∈ (D.inflateNode hS o).nodes := (Comb.subtree_nodes_iff hsub q).symm
  rw [hnode]
  by_cases hb : o.1.2 ∈ (S.tree o.1.1).branching
  · let b : GBranch S.tree := ⟨o.1, hb⟩
    have hbo : b.toNode = o := rfl
    rw [← hbo, localTree_branch, D.inflateNode_branch hS b]
    have e1 := chain_nodeAddresses (D.tree b) (nodeSign S.sig b.1)
      (node3 fun i => D.inflateNode hS (b.child i)) (inflatedPosition S D.tree b.toNode)
    have e2 := chain_nodeAddresses (D.tree b) (nodeSign S.sig b.1) .leaf (inflatedPosition S D.tree b.toNode)
    rw [← mem_nodeAddresses_iff (a := inflatedPosition S D.tree b.toNode), e1,
      ← mem_nodeAddresses_iff (a := inflatedPosition S D.tree b.toNode), e2]
    rw [nodeAddresses_leaf]
    set z := addrExt (inflatedPosition S D.tree b.toNode) q
    set hole := addrExt (inflatedPosition S D.tree b.toNode) (D.tree b).lonePath
    have hchild : ∀ i, inflatedPosition S D.tree (b.child i) = addrExt hole [i] := by
      intro i
      rw [inflatedPosition_child]
      simp [hole, addrExt]
    constructor
    · rintro ⟨hz, ho⟩
      rcases Finset.mem_union.mp hz with h | h
      · exact Finset.mem_union_left _ h
      · obtain ⟨r, hr, he⟩ := Finset.mem_image.mp h
        cases r with
        | nil => exact Finset.mem_union_right _ (by simp [← he, addrExt, hole])
        | cons j r =>
          exfalso
          have hbel : AddrBelow (inflatedPosition S D.tree (b.child j)) z := by
            rw [hchild, ← he]
            exact ⟨rfl, by simp [addrExt]⟩
          have hd := owner_isDesc_of_addrBelow S D.tree hbel
          rw [owner_inflatedPosition, ho] at hd
          have := hd.2.length_le
          simp [GBranch.child, GBranch.toNode] at this
    · intro h
      have hnb : ∀ i, ¬ AddrBelow (inflatedPosition S D.tree (b.child i)) z := by
        intro i hi
        rw [hchild] at hi
        rcases Finset.mem_union.mp h with h | h
        · exact chainNodes_not_below_lone _ _ _ _ h ((addrBelow_iff_below).mp
            (addrBelow_trans (addrBelow_addrExt hole [i]) hi))
        · rw [Finset.mem_singleton] at h
          rw [h] at hi
          have := hi.2.length_le
          simp [addrExt, hole] at this
      refine ⟨?_, owner_eq_branch' S D.tree (addrBelow_addrExt _ _) hnb⟩
      rcases Finset.mem_union.mp h with h | h
      · exact Finset.mem_union_left _ h
      · rw [Finset.mem_singleton] at h
        rw [h]
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨[], TTree.nil_mem_nodes _, by simp [addrExt, hole]⟩)
  · let l : GLeaf S.tree := ⟨o.1, leaf_of_not_branch o hb⟩
    have hlo : l.toNode = o := rfl
    rw [← hlo, localTree_leaf, D.inflateNode_leaf hS l]
    exact ⟨fun h => h.1, fun h => ⟨h, owner_eq_leaf S D.tree (addrBelow_addrExt _ _)⟩⟩

end Local

end WaveTurbulence.Flower.MkMark
