/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.Geom
public import WaveTurbulence.Foundations.Molecule.SpliceInsideNodes
public import WaveTurbulence.Foundations.Molecule.SpliceSignedLeaves
public import WaveTurbulence.Foundations.Molecule.CLLeafNames
public import WaveTurbulence.Foundations.Molecule.CLBranchNames
import Mathlib.Tactic

/-!
# VINE-B Part I (1): the node map of one CL splice

`spNode B : GNode (spliceForest G a B.node) → GNode G.tree` sends the new node at address `a ++ k :: q` to the old
node `(B.node k) ++ q`, the crown (address `a`) to `a`, and is the identity elsewhere.  It is injective with range
the nodes that are not strictly below `a` outside the three boundary subtrees, preserves roots, signs, and the child
structure away from the crown.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.Mole WaveTurbulence.RedSplice

variable {w : ℕ} {G : Garden w} {a : GBranch G.tree} (B : SpliceBoundaryRoots G a)

/-- The address map of the splice. -/
def spAddr (y : Fin w × Path) : Fin w × Path :=
  if y.1 = a.1.1 ∧ a.1.2 <+: y.2 then
    (match y.2.drop a.1.2.length with
      | [] => a.1
      | k :: q => ((B.node k).1.1, (B.node k).1.2 ++ q))
  else y

theorem spAddr_out {y : Fin w × Path} (h : ¬ (y.1 = a.1.1 ∧ a.1.2 <+: y.2)) : spAddr B y = y := by
  simp [spAddr, h]

theorem spAddr_inside (k : Fin 3) (q : Path) :
    spAddr B (a.1.1, a.1.2 ++ k :: q) = ((B.node k).1.1, (B.node k).1.2 ++ q) := by
  have h : (a.1.1, a.1.2 ++ k :: q).1 = a.1.1 ∧ a.1.2 <+: (a.1.1, a.1.2 ++ k :: q).2 :=
    ⟨rfl, List.prefix_append _ _⟩
  simp only [spAddr, h, and_self, ite_true]
  rw [List.drop_left]

theorem spAddr_crown : spAddr B a.1 = a.1 := by
  have h : (a.1).1 = a.1.1 ∧ a.1.2 <+: (a.1).2 := ⟨rfl, List.prefix_refl _⟩
  simp only [spAddr, h, and_self, ite_true]
  simp

theorem crown_node_iff (k : Fin 3) (q : Path) :
    k :: q ∈ (spliceCrown G B.node).nodes ↔ q ∈ (spliceNodeSubtree G (B.node k)).nodes := by
  fin_cases k <;> simp [spliceCrown, TTree.nodes, TTree.cons_mem_pre]

theorem new_mem_iff (r : Path) :
    a.1.2 ++ r ∈ (spliceForest G a B.node a.1.1).nodes ↔ r ∈ (spliceCrown G B.node).nodes := by
  rw [spliceForest_at]
  exact (Comb.subtree_nodes_iff (Comb.subtree_replaceAt (spliceNodeSubtree_spec G a.toNode) _) r).symm

theorem out_mem_iff {p : Path} (hp : ¬ a.1.2 <+: p) :
    p ∈ (spliceForest G a B.node a.1.1).nodes ↔ p ∈ (G.tree a.1.1).nodes := by
  rw [TTree.mem_nodes_iff, TTree.mem_nodes_iff, spliceForest_leaves, spliceForest_branching]
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ((⟨h, _⟩ | ⟨q, _, rfl⟩) | (⟨h, _⟩ | ⟨q, _, rfl⟩))
    · exact Or.inl h
    · exact (hp (List.prefix_append _ _)).elim
    · exact Or.inr h
    · exact (hp (List.prefix_append _ _)).elim
  · rintro (h | h)
    · exact Or.inl (Or.inl ⟨h, hp⟩)
    · exact Or.inr (Or.inl ⟨h, hp⟩)

theorem spAddr_mem (y : GNode (spliceForest G a B.node)) :
    (spAddr B y.1).2 ∈ (G.tree (spAddr B y.1).1).nodes := by
  by_cases hc : y.1.1 = a.1.1 ∧ a.1.2 <+: y.1.2
  · obtain ⟨r, hr⟩ := hc.2
    have hy : a.1.2 ++ r ∈ (spliceForest G a B.node a.1.1).nodes := by
      rw [hr, ← hc.1]
      exact y.2
    have hy' : y.1 = (a.1.1, a.1.2 ++ r) := Prod.ext hc.1 hr.symm
    rw [hy']
    rcases r with _ | ⟨k, q⟩
    · have : (a.1.1, a.1.2 ++ ([] : Path)) = a.1 := by simp
      rw [this, spAddr_crown]
      exact a.toNode.2
    · rw [spAddr_inside]
      have h1 := (crown_node_iff B k q).mp ((new_mem_iff B _).mp hy)
      exact (Comb.subtree_nodes_iff (spliceNodeSubtree_spec G (B.node k)) q).mp h1
  · rw [spAddr_out B hc]
    by_cases hi : y.1.1 = a.1.1
    · have hp : ¬ a.1.2 <+: y.1.2 := fun h => hc ⟨hi, h⟩
      have := y.2
      rw [hi] at this ⊢
      exact (out_mem_iff B hp).mp this
    · have := y.2
      rw [spliceForest_other G a B.node _ hi] at this
      exact this

/-- The node map of the splice. -/
def spNode (y : GNode (spliceForest G a B.node)) : GNode G.tree := ⟨spAddr B y.1, spAddr_mem B y⟩


theorem spNode_val (y : GNode (spliceForest G a B.node)) : (spNode B y).1 = spAddr B y.1 := rfl

theorem spNode_inside (k : Fin 3) (q : Path) (y : GNode (spliceForest G a B.node))
    (hy : y.1 = (a.1.1, a.1.2 ++ k :: q)) :
    (spNode B y).1 = ((B.node k).1.1, (B.node k).1.2 ++ q) := by
  rw [spNode_val, hy, spAddr_inside]

theorem spNode_out (y : GNode (spliceForest G a B.node)) (hy : ¬ (y.1.1 = a.1.1 ∧ a.1.2 <+: y.1.2)) :
    (spNode B y).1 = y.1 := by
  rw [spNode_val, spAddr_out B hy]

theorem spNode_crown (y : GNode (spliceForest G a B.node)) (hy : y.1 = a.1) : (spNode B y).1 = a.1 := by
  rw [spNode_val, hy, spAddr_crown]

/-- The three kinds of new nodes. -/
theorem sp_class (y : GNode (spliceForest G a B.node)) :
    (¬ (y.1.1 = a.1.1 ∧ a.1.2 <+: y.1.2)) ∨ y.1 = a.1 ∨ ∃ k q, y.1 = (a.1.1, a.1.2 ++ k :: q) := by
  by_cases hc : y.1.1 = a.1.1 ∧ a.1.2 <+: y.1.2
  · right
    obtain ⟨r, hr⟩ := hc.2
    have hy : y.1 = (a.1.1, a.1.2 ++ r) := Prod.ext hc.1 hr.symm
    rcases r with _ | ⟨k, q⟩
    · left; rw [hy]; simp
    · right; exact ⟨k, q, hy⟩
  · left; exact hc

theorem spNode_idx (y : GNode (spliceForest G a B.node)) : (spNode B y).1.1 = y.1.1 := by
  rcases sp_class B y with hc | hc | ⟨k, q, hy⟩
  · rw [spNode_out B y hc]
  · rw [spNode_crown B y hc, hc]
  · rw [spNode_inside B k q y hy, hy]
    exact ((B.below k).1).symm

theorem bnode_ne_a (i : Fin 3) : B.node i ≠ a.toNode := by
  intro h
  obtain ⟨j, hj⟩ := exists_ne i
  have h1 := B.below j
  rw [← h] at h1
  exact (B.incomparable i j hj.symm).1 h1

theorem spNode_inj : Function.Injective (spNode B) := by
  intro y y' h
  have hv : (spNode B y).1 = (spNode B y').1 := congrArg Subtype.val h
  apply Subtype.ext
  have bd : ∀ (k : Fin 3) (q : Path), ¬ (((B.node k).1.1, (B.node k).1.2 ++ q).1 = a.1.1 ∧
      a.1.2 <+: ((B.node k).1.1, (B.node k).1.2 ++ q).2) → False := by
    intro k q hn
    exact hn ⟨((B.below k).1).symm, (B.below k).2.trans (List.prefix_append _ _)⟩
  have inA : ∀ (k : Fin 3) (q : Path), ((B.node k).1.1, (B.node k).1.2 ++ q) = a.1 → False := by
    intro k q h2
    have h3 : (B.node k).1.2 ++ q = a.1.2 := congrArg Prod.snd h2
    have hp : (B.node k).1.2 <+: a.1.2 := by rw [← h3]; exact List.prefix_append _ _
    have h4 : (B.node k).1.2 = a.1.2 :=
      hp.eq_of_length (le_antisymm hp.length_le (B.below k).2.length_le)
    apply bnode_ne_a B k
    exact Subtype.ext (Prod.ext ((B.below k).1).symm h4)
  rcases sp_class B y with hc | hc | ⟨k, q, hy⟩ <;> rcases sp_class B y' with hc' | hc' | ⟨k', q', hy'⟩
  · rw [spNode_out B y hc, spNode_out B y' hc'] at hv; exact hv
  · rw [spNode_out B y hc, spNode_crown B y' hc'] at hv; exact (hc (by rw [hv]; exact ⟨rfl, List.prefix_refl _⟩)).elim
  · rw [spNode_out B y hc, spNode_inside B k' q' y' hy'] at hv
    exact (bd k' q' (hv ▸ hc)).elim
  · rw [spNode_crown B y hc, spNode_out B y' hc'] at hv; exact (hc' (by rw [← hv]; exact ⟨rfl, List.prefix_refl _⟩)).elim
  · rw [hc, hc']
  · rw [spNode_crown B y hc, spNode_inside B k' q' y' hy'] at hv
    exact (inA k' q' hv.symm).elim
  · rw [spNode_inside B k q y hy, spNode_out B y' hc'] at hv
    exact (bd k q (hv ▸ hc')).elim
  · rw [spNode_inside B k q y hy, spNode_crown B y' hc'] at hv
    exact (inA k q hv).elim
  · rw [spNode_inside B k q y hy, spNode_inside B k' q' y' hy'] at hv
    obtain ⟨hv1, hv2⟩ := Prod.mk.inj hv
    have hkk : k = k' := by
      by_contra hn
      rcases List.prefix_or_prefix_of_prefix (List.prefix_append (B.node k).1.2 q) (hv2 ▸ List.prefix_append (B.node k').1.2 q') with hp | hp
      · exact (B.incomparable k k' hn).1 ⟨hv1, hp⟩
      · exact (B.incomparable k k' hn).2 ⟨hv1.symm, hp⟩
    subst hkk
    have : q = q' := List.append_cancel_left hv2
    subst this
    rw [hy, hy']


theorem spNode_range (x : GNode G.tree) :
    (∃ y, spNode B y = x) ↔ (¬ a.toNode.IsDesc x ∨ x = a.toNode ∨ ∃ i, (B.node i).IsDesc x) := by
  constructor
  · rintro ⟨y, rfl⟩
    rcases sp_class B y with hc | hc | ⟨k, q, hy⟩
    · left
      intro hd
      apply hc
      have e := spNode_out B y hc
      refine ⟨?_, ?_⟩
      · have h1 := hd.1; rw [e] at h1; exact h1.symm
      · have h2 := hd.2; rw [e] at h2; exact h2
    · right; left
      exact Subtype.ext (spNode_crown B y hc)
    · right; right
      refine ⟨k, ?_, ?_⟩
      · rw [spNode_inside B k q y hy]
      · rw [spNode_inside B k q y hy]
        exact ⟨q, rfl⟩
  · rintro (h | h | ⟨i, hi1, ⟨q, hq⟩⟩)
    · have hmem : x.1.2 ∈ (spliceForest G a B.node x.1.1).nodes := by
        by_cases hi : x.1.1 = a.1.1
        · rw [hi]
          exact (out_mem_iff B (fun hp => h ⟨hi.symm, hp⟩)).mpr (hi ▸ x.2)
        · rw [spliceForest_other G a B.node _ hi]
          exact x.2
      refine ⟨⟨x.1, hmem⟩, ?_⟩
      apply Subtype.ext
      rw [spNode_out B ⟨x.1, hmem⟩]
      intro hc
      exact h ⟨hc.1.symm, hc.2⟩
    · subst h
      refine ⟨(spliceCrownBranch B).toNode, ?_⟩
      exact Subtype.ext (spNode_crown B _ rfl)
    · have hx : x.1 = ((B.node i).1.1, (B.node i).1.2 ++ q) := Prod.ext hi1.symm hq.symm
      have h1 : (B.node i).1.2 ++ q ∈ (G.tree (B.node i).1.1).nodes := by
        have := x.2
        rw [hx] at this
        exact this
      have h2 := (crown_node_iff B i q).mpr ((Comb.subtree_nodes_iff (spliceNodeSubtree_spec G (B.node i)) q).mpr h1)
      have h3 := (new_mem_iff B _).mpr h2
      let y' : GNode (spliceForest G a B.node) := ⟨(a.1.1, a.1.2 ++ i :: q), by simpa using h3⟩
      refine ⟨y', ?_⟩
      apply Subtype.ext
      rw [spNode_inside B i q y' rfl, hx]

theorem spNode_root_iff (hnr : ∀ i, (B.node i).1.2 ≠ []) (y : GNode (spliceForest G a B.node)) :
    (spNode B y).1.2 = [] ↔ y.1.2 = [] := by
  rcases sp_class B y with hc | hc | ⟨k, q, hy⟩
  · rw [spNode_out B y hc]
  · rw [spNode_crown B y hc, hc]
  · rw [spNode_inside B k q y hy, hy]
    simp only [List.append_eq_nil_iff]
    constructor
    · rintro ⟨h, _⟩; exact (hnr k h).elim
    · intro h; simp at h

theorem spNode_sign (hs : ∀ i, G.sign (B.node i) = G.sign (a.child i)) (y : GNode (spliceForest G a B.node)) :
    G.sign (spNode B y) = nodeSign G.sig y.1 := by
  rcases sp_class B y with hc | hc | ⟨k, q, hy⟩
  · have := spNode_out B y hc
    simp only [Garden.sign, this]
  · have := spNode_crown B y hc
    simp only [Garden.sign, this, hc]
  · have h1 := spNode_inside B k q y hy
    have h := hs k
    have hnew : nodeSign G.sig (a.1.1, a.1.2 ++ k :: q) = pathSign (G.sign (a.child k)) q := by
      change pathSign (G.sig a.1.1) (a.1.2 ++ k :: q) = pathSign (pathSign (G.sig a.1.1) (a.1.2 ++ [k])) q
      simpa only [List.append_assoc, List.singleton_append] using
        Comb.pathSign_append (G.sig a.1.1) (a.1.2 ++ [k]) q
    have hold : nodeSign G.sig ((B.node k).1.1, (B.node k).1.2 ++ q) = pathSign (G.sign (B.node k)) q := by
      simp only [nodeSign, pathSign, Garden.sign, List.count_append, pow_add, mul_assoc]
    simp only [Garden.sign, h1]
    rw [hy, hnew, hold, h]

theorem spNode_child (c : GBranch (spliceForest G a B.node)) (c0 : GBranch G.tree)
    (hc0 : c0.1 = (spNode B c.toNode).1) (hcr : c ≠ spliceCrownBranch B) (i : Fin 3) :
    spNode B (c.child i) = c0.child i := by
  apply Subtype.ext
  have hcv : (c.child i).1 = (c.1.1, c.1.2 ++ [i]) := rfl
  have hc0v : (c0.child i).1 = (c0.1.1, c0.1.2 ++ [i]) := rfl
  rcases sp_class B c.toNode with hc | hc | ⟨k, q, hy⟩
  · have e0 : c0.1 = c.1 := by rw [hc0]; exact spNode_out B _ hc
    by_cases hd : (c.child i).1.1 = a.1.1 ∧ a.1.2 <+: (c.child i).1.2
    · have hd2 : a.1.2 <+: c.1.2 ++ [i] := by rw [hcv] at hd; exact hd.2
      rcases List.prefix_concat_iff.mp hd2 with h | h
      · have hca : (c.child i).1 = a.1 := by
          rw [hcv]
          exact Prod.ext (by rw [hcv] at hd; exact hd.1) h.symm
        rw [spNode_crown B _ hca, hc0v, e0, ← hcv, hca]
      · exact (hc ⟨hd.1, h⟩).elim
    · rw [spNode_out B _ hd, hc0v, e0, hcv]
  · exact (hcr (Subtype.ext hc)).elim
  · have hy' : (c.child i).1 = (a.1.1, a.1.2 ++ k :: (q ++ [i])) := by
      rw [hcv]
      have : c.1 = (a.1.1, a.1.2 ++ k :: q) := hy
      rw [this]; simp
    rw [spNode_inside B k (q ++ [i]) _ hy', hc0v]
    have e0 : c0.1 = ((B.node k).1.1, (B.node k).1.2 ++ q) := by
      rw [hc0, spNode_inside B k q _ hy]
    rw [e0]
    simp

theorem spNode_crown_child (i : Fin 3) : spNode B ((spliceCrownBranch B).child i) = B.node i := by
  apply Subtype.ext
  have : ((spliceCrownBranch B).child i).1 = (a.1.1, a.1.2 ++ i :: []) := rfl
  rw [spNode_inside B i [] _ this]
  simp

end WaveTurbulence.VineB
