/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.WaveB.Lemmas
/-! FLOWER-P7: the two-root cap of a width-six forest.  For six trees `T c` (`c : Fin (2 * 3)`) the capped
forest has two trees, the `j`-th being the node whose three children are `T (idx j 0)`, `T (idx j 1)`,
`T (idx j 2)`.  This file gives the address-level description of the nodes, leaves and branching nodes of the
capped forest, and the three reindexing equivalences (roots and lifted nodes). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset

/-- The index of the `i`-th child of the `j`-th root among the six trees. -/
def idx (j : Fin 2) (i : Fin 3) : Fin (2 * 3) := finProdFinEquiv (j, i)

/-- The root of the child tree `c`. -/
def jOf (c : Fin (2 * 3)) : Fin 2 := (finProdFinEquiv.symm c).1

/-- The slot of the child tree `c` under its root. -/
def iOf (c : Fin (2 * 3)) : Fin 3 := (finProdFinEquiv.symm c).2

@[simp] theorem jOf_idx (j : Fin 2) (i : Fin 3) : jOf (idx j i) = j := by
  simp [jOf, idx]

@[simp] theorem iOf_idx (j : Fin 2) (i : Fin 3) : iOf (idx j i) = i := by
  simp [iOf, idx]

@[simp] theorem idx_jOf_iOf (c : Fin (2 * 3)) : idx (jOf c) (iOf c) = c := by
  simp [jOf, iOf, idx]

theorem idx_injective {j j' : Fin 2} {i i' : Fin 3} (h : idx j i = idx j' i') : j = j' ∧ i = i' := by
  have h1 := congrArg jOf h
  have h2 := congrArg iOf h
  simp at h1 h2
  exact ⟨h1, h2⟩

/-- The capped forest. -/
def capTree (T : Fin (2 * 3) → TTree) (j : Fin 2) : TTree :=
  .node (T (idx j 0)) (T (idx j 1)) (T (idx j 2))

theorem mem_leaves_cap {T : Fin (2 * 3) → TTree} {j : Fin 2} {p : Path} :
    p ∈ (capTree T j).leaves ↔ ∃ i : Fin 3, ∃ q, p = i :: q ∧ q ∈ (T (idx j i)).leaves := by
  simp only [capTree, TTree.leaves, Finset.mem_union, TTree.mem_pre]
  constructor
  · rintro ((⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩) | ⟨q, hq, rfl⟩)
    · exact ⟨0, q, rfl, hq⟩
    · exact ⟨1, q, rfl, hq⟩
    · exact ⟨2, q, rfl, hq⟩
  · rintro ⟨i, q, rfl, hq⟩
    fin_cases i
    · exact Or.inl (Or.inl ⟨q, hq, rfl⟩)
    · exact Or.inl (Or.inr ⟨q, hq, rfl⟩)
    · exact Or.inr ⟨q, hq, rfl⟩

theorem mem_nodes_cap {T : Fin (2 * 3) → TTree} {j : Fin 2} {p : Path} :
    p ∈ (capTree T j).nodes ↔ p = [] ∨ ∃ i : Fin 3, ∃ q, p = i :: q ∧ q ∈ (T (idx j i)).nodes := by
  simp only [capTree, TTree.nodes, Finset.mem_insert, Finset.mem_union, TTree.mem_pre]
  constructor
  · rintro (rfl | ((⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩) | ⟨q, hq, rfl⟩))
    · exact Or.inl rfl
    · exact Or.inr ⟨0, q, rfl, hq⟩
    · exact Or.inr ⟨1, q, rfl, hq⟩
    · exact Or.inr ⟨2, q, rfl, hq⟩
  · rintro (rfl | ⟨i, q, rfl, hq⟩)
    · exact Or.inl rfl
    · fin_cases i
      · exact Or.inr (Or.inl (Or.inl ⟨q, hq, rfl⟩))
      · exact Or.inr (Or.inl (Or.inr ⟨q, hq, rfl⟩))
      · exact Or.inr (Or.inr ⟨q, hq, rfl⟩)

theorem mem_branching_cap {T : Fin (2 * 3) → TTree} {j : Fin 2} {p : Path} :
    p ∈ (capTree T j).branching ↔
      p = [] ∨ ∃ i : Fin 3, ∃ q, p = i :: q ∧ q ∈ (T (idx j i)).branching := by
  simp only [capTree, TTree.branching, Finset.mem_insert, Finset.mem_union, TTree.mem_pre]
  constructor
  · rintro (rfl | ((⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩) | ⟨q, hq, rfl⟩))
    · exact Or.inl rfl
    · exact Or.inr ⟨0, q, rfl, hq⟩
    · exact Or.inr ⟨1, q, rfl, hq⟩
    · exact Or.inr ⟨2, q, rfl, hq⟩
  · rintro (rfl | ⟨i, q, rfl, hq⟩)
    · exact Or.inl rfl
    · fin_cases i
      · exact Or.inr (Or.inl (Or.inl ⟨q, hq, rfl⟩))
      · exact Or.inr (Or.inl (Or.inr ⟨q, hq, rfl⟩))
      · exact Or.inr (Or.inr ⟨q, hq, rfl⟩)

theorem cap_order (T : Fin (2 * 3) → TTree) (j : Fin 2) :
    (capTree T j).order = (T (idx j 0)).order + (T (idx j 1)).order + (T (idx j 2)).order + 1 := rfl

/-! ### Lifting of addresses -/

/-- Lift an address of the six trees to an address of the capped forest. -/
def liftAddr (a : Fin (2 * 3) × Path) : Fin 2 × Path := (jOf a.1, iOf a.1 :: a.2)

theorem liftAddr_injective : Function.Injective liftAddr := by
  intro a b h
  simp only [liftAddr, Prod.mk.injEq, List.cons.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have : a.1 = b.1 := by
    rw [← idx_jOf_iOf a.1, ← idx_jOf_iOf b.1, h1, h2]
  exact Prod.ext this h3

def liftNode {T : Fin (2 * 3) → TTree} (a : GNode T) : GNode (capTree T) :=
  ⟨liftAddr a.1, by
    show (iOf a.1.1 :: a.1.2) ∈ (capTree T (jOf a.1.1)).nodes
    rw [mem_nodes_cap]
    exact Or.inr ⟨iOf a.1.1, a.1.2, rfl, by simpa using a.2⟩⟩

def liftLeaf {T : Fin (2 * 3) → TTree} (a : GLeaf T) : GLeaf (capTree T) :=
  ⟨liftAddr a.1, by
    show (iOf a.1.1 :: a.1.2) ∈ (capTree T (jOf a.1.1)).leaves
    rw [mem_leaves_cap]
    exact ⟨iOf a.1.1, a.1.2, rfl, by simpa using a.2⟩⟩

def liftBranch {T : Fin (2 * 3) → TTree} (a : GBranch T) : GBranch (capTree T) :=
  ⟨liftAddr a.1, by
    show (iOf a.1.1 :: a.1.2) ∈ (capTree T (jOf a.1.1)).branching
    rw [mem_branching_cap]
    exact Or.inr ⟨iOf a.1.1, a.1.2, rfl, by simpa using a.2⟩⟩

/-- The root `j` of the capped forest as a branching node. -/
def rootBranch (T : Fin (2 * 3) → TTree) (j : Fin 2) : GBranch (capTree T) :=
  ⟨(j, []), by
    show ([] : Path) ∈ (capTree T j).branching
    rw [mem_branching_cap]
    exact Or.inl rfl⟩

theorem liftBranch_injective {T : Fin (2 * 3) → TTree} : Function.Injective (liftBranch (T := T)) := by
  intro a b h
  exact Subtype.ext (liftAddr_injective (congrArg Subtype.val h))

theorem liftNode_injective {T : Fin (2 * 3) → TTree} : Function.Injective (liftNode (T := T)) := by
  intro a b h
  exact Subtype.ext (liftAddr_injective (congrArg Subtype.val h))

theorem liftLeaf_injective {T : Fin (2 * 3) → TTree} : Function.Injective (liftLeaf (T := T)) := by
  intro a b h
  exact Subtype.ext (liftAddr_injective (congrArg Subtype.val h))

/-- Every non-root node of the capped forest is a lifted node. -/
theorem exists_liftNode {T : Fin (2 * 3) → TTree} (a : GNode (capTree T)) (h : a.1.2 ≠ []) :
    ∃ b : GNode T, liftNode b = a := by
  obtain ⟨⟨j, p⟩, hp⟩ := a
  have hp' : p ∈ (capTree T j).nodes := hp
  rw [mem_nodes_cap] at hp'
  rcases hp' with rfl | ⟨i, q, rfl, hq⟩
  · exact absurd rfl h
  · refine ⟨⟨(idx j i, q), hq⟩, ?_⟩
    apply Subtype.ext
    simp [liftNode, liftAddr]

theorem exists_liftLeaf {T : Fin (2 * 3) → TTree} (a : GLeaf (capTree T)) :
    ∃ b : GLeaf T, liftLeaf b = a := by
  obtain ⟨⟨j, p⟩, hp⟩ := a
  have hp' : p ∈ (capTree T j).leaves := hp
  rw [mem_leaves_cap] at hp'
  obtain ⟨i, q, rfl, hq⟩ := hp'
  refine ⟨⟨(idx j i, q), hq⟩, ?_⟩
  apply Subtype.ext
  simp [liftLeaf, liftAddr]

theorem exists_liftBranch {T : Fin (2 * 3) → TTree} (a : GBranch (capTree T)) (h : a.1.2 ≠ []) :
    ∃ b : GBranch T, liftBranch b = a := by
  obtain ⟨⟨j, p⟩, hp⟩ := a
  have hp' : p ∈ (capTree T j).branching := hp
  rw [mem_branching_cap] at hp'
  rcases hp' with rfl | ⟨i, q, rfl, hq⟩
  · exact absurd rfl h
  · refine ⟨⟨(idx j i, q), hq⟩, ?_⟩
    apply Subtype.ext
    simp [liftBranch, liftAddr]

theorem lift_ne_root {T : Fin (2 * 3) → TTree} (b : GBranch T) (j : Fin 2) :
    liftBranch b ≠ rootBranch T j := by
  intro h
  have := congrArg (fun x : GBranch (capTree T) => x.1.2) h
  simp [liftBranch, liftAddr, rootBranch] at this

/-- The map of `capBranchEquiv`. -/
def capBranchMap (T : Fin (2 * 3) → TTree) : Fin 2 ⊕ GBranch T → GBranch (capTree T)
  | .inl j => rootBranch T j
  | .inr a => liftBranch a

/-- The map of `capNodeEquiv`. -/
def capNodeMap (T : Fin (2 * 3) → TTree) : Fin 2 ⊕ GNode T → GNode (capTree T)
  | .inl j => (rootBranch T j).toNode
  | .inr a => liftNode a

theorem capBranchMap_bijective (T : Fin (2 * 3) → TTree) : Function.Bijective (capBranchMap T) := by
  constructor
  · rintro (j | a) (j' | a') h
    · have := congrArg (fun x : GBranch (capTree T) => x.1.1) h
      simp only [capBranchMap, rootBranch] at this
      rw [this]
    · exact absurd h.symm (lift_ne_root a' j)
    · exact absurd h (lift_ne_root a j')
    · exact congrArg Sum.inr (liftBranch_injective h)
  · rintro ⟨⟨j, p⟩, hp⟩
    by_cases h : p = []
    · subst h
      exact ⟨Sum.inl j, rfl⟩
    · obtain ⟨b, hb⟩ := exists_liftBranch ⟨(j, p), hp⟩ h
      exact ⟨Sum.inr b, hb⟩

theorem capNodeMap_bijective (T : Fin (2 * 3) → TTree) : Function.Bijective (capNodeMap T) := by
  constructor
  · rintro (j | a) (j' | a') h
    · have := congrArg (fun x : GNode (capTree T) => x.1.1) h
      simp only [capNodeMap, rootBranch, GBranch.toNode] at this
      rw [this]
    · have := congrArg (fun x : GNode (capTree T) => x.1.2) h
      simp [capNodeMap, liftNode, liftAddr, rootBranch, GBranch.toNode] at this
    · have := congrArg (fun x : GNode (capTree T) => x.1.2) h
      simp [capNodeMap, liftNode, liftAddr, rootBranch, GBranch.toNode] at this
    · exact congrArg Sum.inr (liftNode_injective h)
  · rintro ⟨⟨j, p⟩, hp⟩
    by_cases h : p = []
    · subst h
      exact ⟨Sum.inl j, rfl⟩
    · obtain ⟨b, hb⟩ := exists_liftNode ⟨(j, p), hp⟩ h
      exact ⟨Sum.inr b, hb⟩

/-- The branching nodes of the capped forest: the two roots and the lifted branching nodes. -/
noncomputable def capBranchEquiv (T : Fin (2 * 3) → TTree) : Fin 2 ⊕ GBranch T ≃ GBranch (capTree T) :=
  Equiv.ofBijective (capBranchMap T) (capBranchMap_bijective T)

/-- The nodes of the capped forest: the two roots and the lifted nodes. -/
noncomputable def capNodeEquiv (T : Fin (2 * 3) → TTree) : Fin 2 ⊕ GNode T ≃ GNode (capTree T) :=
  Equiv.ofBijective (capNodeMap T) (capNodeMap_bijective T)

/-- The leaves of the capped forest are the lifted leaves. -/
noncomputable def capLeafEquiv (T : Fin (2 * 3) → TTree) : GLeaf T ≃ GLeaf (capTree T) :=
  Equiv.ofBijective liftLeaf ⟨liftLeaf_injective, exists_liftLeaf⟩

end WaveTurbulence.FlowerP7
