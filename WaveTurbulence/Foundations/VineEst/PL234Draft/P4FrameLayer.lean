/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.PL234Draft.P4Frame

/-!
# The layered frame

For a layered carrier `LQ` of a couple code `Q` and layers `q' ≤ q ≤ p`, the **layered frame** carries the layers of
`LQ` on the code (shifted by `ι z = (z.1, 0 :: 0 :: z.2)`) and the outer layers

roots `p`, `(0,[0])` `q`, `(1,[0])` `q'`, `(0,[0,1])` `q`, `(0,[0,2])` `q'`, `(1,[0,1])` `q'`, `(1,[0,2])` `q'`,
`(0,[1])` `q'`, `(1,[1])` `q`, `(0,[2])` `p`, `(1,[2])` `p`,

so that the code's parents are in layers `q` and `q'`. This is a layering when the roots of `LQ` are in layers
`≤ q` and `≤ q'` (`frameLayer_isLayering`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct

open Finset

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

/-- The shift of the code into the frame. -/
def frameIota (z : Fin 2 × Path) : Fin 2 × Path := (z.1, 0 :: 0 :: z.2)

theorem frameIota_hom (z : Fin 2 × Path) (p : Path) : frameIota (addrExt z p) = addrExt (frameIota z) p := by
  simp [frameIota, addrExt]

theorem frameIota_zero : frameIota ((0 : Fin 2), []) = fA := rfl

theorem frameIota_one : frameIota ((1 : Fin 2), []) = fB := rfl

/-- The outer layers of the frame. -/
def outerLayer (p q q' : ℕ) (z : Fin 2 × Path) : ℕ :=
  if z.2 = [] ∨ z.2 = [2] then p
  else if z.2 = [0] ∨ z.2 = [0, 1] then (if z.1 = 0 then q else q')
  else if z.2 = [0, 2] then q'
  else if z.2 = [1] then (if z.1 = 0 then q' else q) else 0

/-- The layers of the frame at every address. -/
noncomputable def frameAddrLayer (LQ : LayeredGarden 2) (p q q' : ℕ) (z : Fin 2 × Path) : ℕ :=
  if [0, 0] <+: z.2 then layerAt LQ (z.1, z.2.drop 2) else outerLayer p q q' z

theorem frameAddrLayer_iota (LQ : LayeredGarden 2) (p q q' : ℕ) (z : Fin 2 × Path) :
    frameAddrLayer LQ p q q' (frameIota z) = layerAt LQ z := by
  unfold frameAddrLayer frameIota
  rw [ite_eq_left (by simp)]
  rfl

theorem mem_symmPairs_append_left {α : Type*} {L M : List (α × α)} {x : α × α} (h : x ∈ symmPairs L) :
    x ∈ symmPairs (L ++ M) := by
  unfold symmPairs at h ⊢
  rcases List.mem_append.mp h with h | h
  · exact List.mem_append_left _ (List.mem_append_left _ h)
  · rw [List.map_append]
    exact List.mem_append_right _ (List.mem_append_left _ h)

theorem frameTree_branching (T : TTree) (p : Path) :
    p ∈ (frameTree T).branching ↔ p = [] ∨ p = [0] ∨ ∃ u ∈ T.branching, p = 0 :: 0 :: u := by
  simp only [frameTree, TTree.branching, TTree.pre, Finset.mem_insert, Finset.mem_image,
    Finset.image_empty, Finset.union_empty]
  constructor
  · rintro (rfl | ⟨x, (rfl | ⟨u, hu, rfl⟩), rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨u, hu, rfl⟩)
  · rintro (rfl | rfl | ⟨u, hu, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨[], Or.inl rfl, rfl⟩
    · exact Or.inr ⟨0 :: u, Or.inr ⟨u, hu, rfl⟩, rfl⟩

theorem frameForest_eq {Q : RegCpl} {LQ : LayeredGarden 2} (hQ : Q.Decodes LQ.garden) (j : Fin 2) :
    frameForest Q j = frameTree (LQ.garden.tree j) := by
  fin_cases j
  · show frameTree Q.trees.1 = frameTree (LQ.garden.tree 0)
    rw [hQ.2.1]
  · show frameTree Q.trees.2 = frameTree (LQ.garden.tree 1)
    rw [hQ.2.2.1]

section Layering

variable {Q : RegCpl} {LQ : LayeredGarden 2} (hQ : Q.Decodes LQ.garden) {p q q' : ℕ} (hqq : q' ≤ q)
  (hqp : q ≤ p) (ha : layerAt LQ ((0 : Fin 2), []) ≤ q) (hb : layerAt LQ ((1 : Fin 2), []) ≤ q')
include hQ hqq hqp ha hb

theorem frameLayer_child (z : Fin 2 × Path) (hz : z.2 ∈ (frameForest Q z.1).branching) (i : Fin 3) :
    frameAddrLayer LQ p q q' (z.1, z.2 ++ [i]) ≤ frameAddrLayer LQ p q q' z := by
  obtain ⟨j, path⟩ := z
  rw [frameForest_eq hQ, frameTree_branching] at hz
  rcases hz with rfl | rfl | ⟨u, hu, rfl⟩
  · have hi : ¬ [0, 0] <+: ([] ++ [i] : Path) := by
      intro h
      have := h.length_le
      simp at this
    unfold frameAddrLayer outerLayer
    rw [ite_eq_right hi]
    fin_cases i <;> fin_cases j <;> simp <;> omega
  · fin_cases i
    · unfold frameAddrLayer outerLayer
      rw [ite_eq_left (by simp), ite_eq_right (by simp)]
      simp only [List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero, Fin.zero_eta,
        Fin.isValue]
      fin_cases j
      · simpa using ha
      · simpa using hb
    · unfold frameAddrLayer outerLayer
      rw [ite_eq_right (by simp), ite_eq_right (by simp)]
      fin_cases j <;> simp
    · unfold frameAddrLayer outerLayer
      rw [ite_eq_right (by simp), ite_eq_right (by simp)]
      fin_cases j <;> simp [hqq]
  · unfold frameAddrLayer
    rw [ite_eq_left (by simp), ite_eq_left (by simp)]
    simp only [List.cons_append, List.drop_succ_cons, List.drop_zero]
    have hb' : u ∈ (LQ.garden.tree j).branching := hu
    have h := LQ.isLayering.1 ⟨(j, u), hb'⟩ i
    rw [← layerAt_node, ← layerAt_node] at h
    exact h

omit hqq hqp ha hb in
theorem frameLayer_pair (ℓ : GLeaf (frameGarden Q).tree) :
    frameAddrLayer LQ p q q' ℓ.1 = frameAddrLayer LQ p q q' ((frameGarden Q).pair ℓ).1 := by
  have hm := frame_pairs_cover Q ℓ
  rw [framePairs, pairEndpoints_append, Finset.mem_union, ← couple_leafAddresses] at hm
  rcases hm with hm | hm
  · -- an inner leaf
    have hm' : ∃ w : Fin 2 × Path, w.2 ∈ (LQ.garden.tree w.1).leaves ∧ ℓ.1 = frameIota w := by
      rcases Finset.mem_union.mp hm with h | h
      · obtain ⟨u, hu, he⟩ := Finset.mem_image.mp h
        refine ⟨((0 : Fin 2), u), ?_, he.symm⟩
        show u ∈ (LQ.garden.tree 0).leaves
        rw [hQ.2.1]
        exact hu
      · obtain ⟨u, hu, he⟩ := Finset.mem_image.mp h
        refine ⟨((1 : Fin 2), u), ?_, he.symm⟩
        show u ∈ (LQ.garden.tree 1).leaves
        rw [hQ.2.2.1]
        exact hu
    obtain ⟨w, hw, he⟩ := hm'
    set ℓ' : GLeaf LQ.garden.tree := ⟨w, hw⟩
    have hpair : (ℓ'.1, (LQ.garden.pair ℓ').1) ∈ symmPairs Q.raw.2 := hQ.2.2.2 ℓ'
    have hmap : (frameIota w, frameIota (LQ.garden.pair ℓ').1) ∈ symmPairs (framePairs Q) := by
      apply mem_symmPairs_append_left
      have e := couple_pairsAt_map Q frameIota frameIota_hom ((0 : Fin 2), []) ((1 : Fin 2), [])
      rw [frameIota_zero, frameIota_one] at e
      unfold symmPairs at hpair ⊢
      rw [List.mem_append] at hpair ⊢
      rcases hpair with h | h
      · left
        rw [e]
        exact List.mem_map.mpr ⟨_, h, rfl⟩
      · right
        rw [e, List.map_map]
        obtain ⟨x, hx, hxe⟩ := List.mem_map.mp h
        refine List.mem_map.mpr ⟨x, hx, ?_⟩
        simp only [Function.comp_apply, Prod.swap] at hxe ⊢
        rw [Prod.mk.injEq] at hxe
        exact Prod.ext (congrArg frameIota hxe.1) (congrArg frameIota hxe.2)
    rw [← he] at hmap
    rw [frameGarden_pair Q ℓ hmap, he, frameAddrLayer_iota, frameAddrLayer_iota]
    have h := LQ.isLayering.2 ℓ'
    rw [← layerAt_node, ← layerAt_node] at h
    exact h
  · -- an outer leaf
    rw [mem_outer_endpoints] at hm
    have hP : ∀ x y : Fin 2 × Path, (x, y) ∈ outerPairs → ℓ.1 = x ∨ ℓ.1 = y →
        frameAddrLayer LQ p q q' x = frameAddrLayer LQ p q q' y →
        frameAddrLayer LQ p q q' ℓ.1 = frameAddrLayer LQ p q q' ((frameGarden Q).pair ℓ).1 := by
      intro x y hxy hl hxyl
      rcases hl with hl | hl
      · rw [frameGarden_pair Q ℓ (y := y) (by
          rw [hl]
          exact List.mem_append_left _ (List.mem_append_right _ hxy)), hl, hxyl]
      · rw [frameGarden_pair Q ℓ (y := x) (by
          rw [hl]
          refine List.mem_append_right _ (List.mem_map.mpr ⟨(x, y), List.mem_append_right _ hxy, rfl⟩)), hl,
          hxyl]
    have hv : ∀ x y : Fin 2 × Path, (x, y) ∈ outerPairs → frameAddrLayer LQ p q q' x = frameAddrLayer LQ p q q' y := by
      intro x y hxy
      simp only [outerPairs, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hxy
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [frameAddrLayer, outerLayer]
    rcases hm with h | h | h | h | h | h | h | h
    · exact hP (((1 : Fin 2), [1])) (((0 : Fin 2), [0, 1])) (by simp [outerPairs]) (Or.inl h) (hv _ _ (by simp [outerPairs]))
    · exact hP (((1 : Fin 2), [1])) (((0 : Fin 2), [0, 1])) (by simp [outerPairs]) (Or.inr h) (hv _ _ (by simp [outerPairs]))
    · exact hP (((0 : Fin 2), [0, 2])) (((1 : Fin 2), [0, 2])) (by simp [outerPairs]) (Or.inl h) (hv _ _ (by simp [outerPairs]))
    · exact hP (((0 : Fin 2), [0, 2])) (((1 : Fin 2), [0, 2])) (by simp [outerPairs]) (Or.inr h) (hv _ _ (by simp [outerPairs]))
    · exact hP (((1 : Fin 2), [0, 1])) (((0 : Fin 2), [1])) (by simp [outerPairs]) (Or.inl h) (hv _ _ (by simp [outerPairs]))
    · exact hP (((1 : Fin 2), [0, 1])) (((0 : Fin 2), [1])) (by simp [outerPairs]) (Or.inr h) (hv _ _ (by simp [outerPairs]))
    · exact hP (((0 : Fin 2), [2])) (((1 : Fin 2), [2])) (by simp [outerPairs]) (Or.inl h) (hv _ _ (by simp [outerPairs]))
    · exact hP (((0 : Fin 2), [2])) (((1 : Fin 2), [2])) (by simp [outerPairs]) (Or.inr h) (hv _ _ (by simp [outerPairs]))

theorem frameLayer_isLayering :
    IsLayering (frameGarden Q) (fun z => frameAddrLayer LQ p q q' z.1) :=
  ⟨fun b i => frameLayer_child hQ hqq hqp ha hb b.1 b.2 i, fun ℓ => frameLayer_pair hQ ℓ⟩

/-- **The layered frame.** -/
noncomputable def frameLayered : LayeredGarden 2 :=
  ⟨frameGarden Q, fun z => frameAddrLayer LQ p q q' z.1, frameLayer_isLayering hQ hqq hqp ha hb⟩

omit hqq hqp ha hb in
theorem frameNode_iota (z : Fin 2 × Path) :
    (frameIota z).2 ∈ ((frameGarden Q).tree (frameIota z).1).nodes ↔ z.2 ∈ (LQ.garden.tree z.1).nodes := by
  show 0 :: 0 :: z.2 ∈ (frameForest Q z.1).nodes ↔ _
  rw [frameForest_eq hQ, frameTree_nodes]
  constructor
  · rintro (h | h | ⟨u, hu, h⟩ | h | h | h | h) <;> simp_all
  · intro h
    exact Or.inr (Or.inr (Or.inl ⟨z.2, h, rfl⟩))

theorem layerAt_frameLayered (z : Fin 2 × Path) :
    layerAt (frameLayered hQ hqq hqp ha hb) z =
      if z.2 ∈ ((frameGarden Q).tree z.1).nodes then frameAddrLayer LQ p q q' z else 0 := by
  show (if h : z.2 ∈ ((frameGarden Q).tree z.1).nodes then frameAddrLayer LQ p q q' z else 0) = _
  split_ifs <;> rfl

theorem layerAt_frame_iota (z : Fin 2 × Path) :
    layerAt (frameLayered hQ hqq hqp ha hb) (frameIota z) = layerAt LQ z := by
  rw [layerAt_frameLayered]
  split_ifs with h
  · exact frameAddrLayer_iota LQ p q q' z
  · have h' := (frameNode_iota hQ z).not.mp h
    unfold layerAt
    rw [dite_eq_right_of_eq_false (eq_false h')]

end Layering

end WaveTurbulence.PL234
