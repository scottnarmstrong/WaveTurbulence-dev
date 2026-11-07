/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.PL234Draft.P4Decode
public import WaveTurbulence.Foundations.RegStruct.DecodedCouple
public import WaveTurbulence.Foundations.RegStruct.PairFunctionality

/-!
# A frame couple around any couple code

Every couple code `Q` sits inside the **frame couple** with trees `•(•(𝒯⁺, •, •), •, •)` and
`•(•(𝒯⁻, •, •), •, •)`: the code at `a = (0, [0,0])`, `b = (1, [0,0])`, and four outer leaf pairs

`(1,[1]) – (0,[0,1])`, `(0,[0,2]) – (1,[0,2])`, `(1,[0,1]) – (0,[1])`, `(0,[2]) – (1,[2])`,

none of which closes up a sub-couple around the code. It is built by REG-STRUCT's `gardenOfPairs` from its literal
pair list (`frameGarden`, `frameGarden_pair`), embeds the code (`frame_embeds`), and has the code's signs at `a`, `b`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct

open Finset

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

/-- The frame around one tree. -/
def frameTree (T : TTree) : TTree := .node (.node T .leaf .leaf) .leaf .leaf

/-- The frame forest of a couple code. -/
def frameForest (Q : RegCpl) : Fin 2 → TTree := ![frameTree Q.trees.1, frameTree Q.trees.2]

/-- The position of the `+` tree of the code. -/
def fA : Fin 2 × Path := ((0 : Fin 2), [0, 0])

/-- The position of the `-` tree of the code. -/
def fB : Fin 2 × Path := ((1 : Fin 2), [0, 0])

/-- The outer leaf pairs, as `(+ leaf, - leaf)`. -/
def outerPairs : List ((Fin 2 × Path) × (Fin 2 × Path)) :=
  [(((1 : Fin 2), [1]), ((0 : Fin 2), [0, 1])), (((0 : Fin 2), [0, 2]), ((1 : Fin 2), [0, 2])),
    (((1 : Fin 2), [0, 1]), ((0 : Fin 2), [1])), (((0 : Fin 2), [2]), ((1 : Fin 2), [2]))]

/-- The pair list of the frame. -/
def framePairs (Q : RegCpl) : List ((Fin 2 × Path) × (Fin 2 × Path)) := Q.pairsAt fA fB ++ outerPairs

theorem frameTree_leaves (T : TTree) (p : Path) :
    p ∈ (frameTree T).leaves ↔ (∃ u ∈ T.leaves, p = 0 :: 0 :: u) ∨ p = [0, 1] ∨ p = [0, 2] ∨ p = [1] ∨ p = [2] := by
  simp only [frameTree, TTree.leaves, TTree.pre, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro (((⟨x, ((⟨u, hu, rfl⟩ | ⟨y, rfl, rfl⟩) | ⟨y, rfl, rfl⟩), rfl⟩) | ⟨y, rfl, rfl⟩) | ⟨y, rfl, rfl⟩)
    · exact Or.inl ⟨u, hu, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  · rintro (⟨u, hu, rfl⟩ | rfl | rfl | rfl | rfl)
    · exact Or.inl (Or.inl ⟨0 :: u, Or.inl (Or.inl ⟨u, hu, rfl⟩), rfl⟩)
    · exact Or.inl (Or.inl ⟨[1], Or.inl (Or.inr ⟨[], rfl, rfl⟩), rfl⟩)
    · exact Or.inl (Or.inl ⟨[2], Or.inr ⟨[], rfl, rfl⟩, rfl⟩)
    · exact Or.inl (Or.inr ⟨[], rfl, rfl⟩)
    · exact Or.inr ⟨[], rfl, rfl⟩

theorem frameTree_nodes (T : TTree) (p : Path) :
    p ∈ (frameTree T).nodes ↔ p = [] ∨ p = [0] ∨ (∃ u ∈ T.nodes, p = 0 :: 0 :: u) ∨ p = [0, 1] ∨ p = [0, 2] ∨
      p = [1] ∨ p = [2] := by
  simp only [frameTree, TTree.nodes, TTree.pre, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
    Finset.mem_singleton]
  constructor
  · rintro (rfl | ((⟨x, (rfl | ((⟨u, hu, rfl⟩ | ⟨y, rfl, rfl⟩) | ⟨y, rfl, rfl⟩)), rfl⟩) | ⟨y, rfl, rfl⟩) |
      ⟨y, rfl, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl ⟨u, hu, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  · rintro (rfl | rfl | ⟨u, hu, rfl⟩ | rfl | rfl | rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (Or.inl ⟨[], Or.inl rfl, rfl⟩))
    · exact Or.inr (Or.inl (Or.inl ⟨0 :: u, Or.inr (Or.inl (Or.inl ⟨u, hu, rfl⟩)), rfl⟩))
    · exact Or.inr (Or.inl (Or.inl ⟨[1], Or.inr (Or.inl (Or.inr ⟨[], rfl, rfl⟩)), rfl⟩))
    · exact Or.inr (Or.inl (Or.inl ⟨[2], Or.inr (Or.inr ⟨[], rfl, rfl⟩), rfl⟩))
    · exact Or.inr (Or.inl (Or.inr ⟨[], rfl, rfl⟩))
    · exact Or.inr (Or.inr ⟨[], rfl, rfl⟩)

theorem mem_outer_endpoints (z : Fin 2 × Path) :
    z ∈ pairEndpoints outerPairs ↔ z = ((1 : Fin 2), [1]) ∨ z = ((0 : Fin 2), [0, 1]) ∨
      z = ((0 : Fin 2), [0, 2]) ∨ z = ((1 : Fin 2), [0, 2]) ∨ z = ((1 : Fin 2), [0, 1]) ∨ z = ((0 : Fin 2), [1]) ∨
      z = ((0 : Fin 2), [2]) ∨ z = ((1 : Fin 2), [2]) := by
  simp only [pairEndpoints, outerPairs, List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
    Finset.mem_union, Finset.mem_insert, Finset.notMem_empty, or_false]
  tauto

/-- **The leaves of the frame are the endpoints of its pair list.** -/
theorem frame_leaf_iff (Q : RegCpl) (z : Fin 2 × Path) :
    z.2 ∈ (frameForest Q z.1).leaves ↔ z ∈ pairEndpoints (framePairs Q) := by
  rw [framePairs, pairEndpoints_append, Finset.mem_union, ← couple_leafAddresses, Finset.mem_union,
    mem_outer_endpoints]
  obtain ⟨j, p⟩ := z
  simp only [leafAddresses, Finset.mem_image, fA, fB, addrExt]
  fin_cases j
  · simp only [frameForest, Matrix.cons_val_zero, frameTree_leaves, Fin.zero_eta, Prod.mk.injEq, Fin.isValue]
    constructor
    · rintro (⟨u, hu, rfl⟩ | rfl | rfl | rfl | rfl)
      · exact Or.inl (Or.inl ⟨u, hu, trivial, rfl⟩)
      · tauto
      · tauto
      · tauto
      · tauto
    · rintro ((⟨u, hu, -, rfl⟩ | ⟨u, -, h, -⟩) | h)
      · exact Or.inl ⟨u, hu, rfl⟩
      · exact absurd h (by decide)
      · simp at h
        tauto
  · simp only [frameForest, Matrix.cons_val_one, Matrix.cons_val_fin_one, frameTree_leaves, Fin.mk_one,
      Prod.mk.injEq, Fin.isValue]
    constructor
    · rintro (⟨u, hu, rfl⟩ | rfl | rfl | rfl | rfl)
      · exact Or.inl (Or.inr ⟨u, hu, trivial, rfl⟩)
      · tauto
      · tauto
      · tauto
      · tauto
    · rintro ((⟨u, -, h, -⟩ | ⟨u, hu, -, rfl⟩) | h)
      · exact absurd h (by decide)
      · exact Or.inl ⟨u, hu, rfl⟩
      · simp at h
        tauto

theorem frame_pairs_valid (Q : RegCpl) :
    ∀ p ∈ framePairs Q, p.1.2 ∈ (frameForest Q p.1.1).leaves ∧ p.2.2 ∈ (frameForest Q p.2.1).leaves :=
  fun p hp => ⟨(frame_leaf_iff Q p.1).mpr ((mem_pairEndpoints_iff _ _).mpr ⟨p, hp, Or.inl rfl⟩),
    (frame_leaf_iff Q p.2).mpr ((mem_pairEndpoints_iff _ _).mpr ⟨p, hp, Or.inr rfl⟩)⟩

theorem frame_pairs_cover (Q : RegCpl) (ℓ : GLeaf (frameForest Q)) : ℓ.1 ∈ pairEndpoints (framePairs Q) :=
  (frame_leaf_iff Q ℓ.1).mp ℓ.2

theorem frameTree_order (T : TTree) : (frameTree T).order = T.order + 2 := by
  simp [frameTree, TTree.order]

theorem frame_pair_card (Q : RegCpl) : (framePairs Q).length * 2 = Fintype.card (GLeaf (frameForest Q)) := by
  have hf : (∑ j, (frameForest Q j).order) = Q.size + 4 := by
    simp only [frameForest, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, frameTree_order]
    have := code_trees_order Q
    omega
  rw [framePairs, List.length_append, couple_pairsAt_length, Comb.card_gleaf, hf]
  simp [outerPairs]
  ring

theorem nodeSign_fA : nodeSign ![(1 : ℤˣ), -1] fA = 1 := by simp [nodeSign, pathSign, fA]

theorem nodeSign_fB : nodeSign ![(1 : ℤˣ), -1] fB = -1 := by simp [nodeSign, pathSign, fB]

theorem frame_pair_signs (Q : RegCpl) :
    ∀ p ∈ framePairs Q, nodeSign ![(1 : ℤˣ), -1] p.1 = 1 ∧ nodeSign ![(1 : ℤˣ), -1] p.2 = -1 := by
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact couple_pairsAt_signs Q ![1, -1] fA fB nodeSign_fA nodeSign_fB p h
  · simp only [outerPairs, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> simp [nodeSign, pathSign]

/-- **The frame couple** of a code. -/
noncomputable def frameGarden (Q : RegCpl) : Garden 2 :=
  gardenOfPairs (frameForest Q) ![1, -1] (framePairs Q) (frame_pairs_valid Q) (frame_pairs_cover Q)
    (frame_pair_card Q) (frame_pair_signs Q)

theorem frameGarden_plain (Q : RegCpl) : (frameGarden Q).IsPlain := gardenOfPairs_plain _ _ _ _ _ _ _

theorem frameGarden_sig (Q : RegCpl) : (frameGarden Q).sig = ![1, -1] := rfl

theorem frameGarden_tree (Q : RegCpl) : (frameGarden Q).tree = frameForest Q := rfl

/-- **The partner of a frame leaf is its listed partner.** -/
theorem frameGarden_pair (Q : RegCpl) (ℓ : GLeaf (frameGarden Q).tree) {y : Fin 2 × Path}
    (hy : (ℓ.1, y) ∈ symmPairs (framePairs Q)) : ((frameGarden Q).pair ℓ).1 = y :=
  pair_relation_functional (frameForest Q) (framePairs Q) (frame_pairs_valid Q) (frame_pairs_cover Q)
    (frame_pair_card Q) (gardenOfPairs_pair_mem _ _ _ _ _ _ _ ℓ) hy

/-- **The frame embeds the code at `a`, `b`.** -/
theorem frame_embeds (Q : RegCpl) : Embeds (frameGarden Q) Q fA fB where
  indep := ⟨fun h => by simp [Under, fA, fB] at h, fun h => by simp [Under, fA, fB] at h⟩
  nodeA := by
    show [0, 0] ∈ (frameTree Q.trees.1).nodes
    rw [frameTree_nodes]
    exact Or.inr (Or.inr (Or.inl ⟨[], TTree.nil_mem_nodes _, rfl⟩))
  nodeB := by
    show [0, 0] ∈ (frameTree Q.trees.2).nodes
    rw [frameTree_nodes]
    exact Or.inr (Or.inr (Or.inl ⟨[], TTree.nil_mem_nodes _, rfl⟩))
  treeA := by simp [frameGarden_tree, frameForest, frameTree, fA, TTree.subtreeAt]
  treeB := by simp [frameGarden_tree, frameForest, frameTree, fB, TTree.subtreeAt]
  pairs := fun p hp ℓ hℓ => frameGarden_pair Q ℓ (by
    rw [hℓ]
    exact List.mem_append_left _ (List.mem_append_left _ hp))

end WaveTurbulence.PL234
