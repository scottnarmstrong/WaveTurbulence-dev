/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.PL234Draft.P4FrameLayer
public import WaveTurbulence.Foundations.Molecule.LayerRegDraft.Part2

/-!
# The layered frame is canonical

By LAYERREG's characterization `layerreg1_part2` (TARGET `layerreg1` (2), ported verbatim), a garden containing an
embedded couple with the layering pattern of `layerreg1` (1) is canonical iff its layers are `≤ p` and the
criterion holds away from the couple (`CritOut`) and at the collapsed couple (`CritAttach`). For the frame these
are finitely many checks:

* the only outer nodes below their parent's layer are `(0,[0])`, `(1,[0])`, `(0,[1])`, `(1,[1])`, `(0,[0,2])`;
* each incomparable pair of them (and of `(0,[0,0])` with them) misses the partner of one of its leaves
  (`frame_not_cp_*`), so it is not completely paired.

**`frame_canon`**: the layered frame is in `𝒞_{p+1}` whenever the code carries the `layerreg1` pattern.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct

open Finset

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

/-- A set of leaves below two nodes is not completely paired if one of its leaves has its partner outside. -/
theorem not_cp_of {w : ℕ} {G : Garden w} {x y : GNode G.tree} (ℓ : GLeaf G.tree)
    (h1 : Under x.1 ℓ.1 ∨ Under y.1 ℓ.1) (h2 : ¬ Under x.1 (G.pair ℓ).1) (h3 : ¬ Under y.1 (G.pair ℓ).1) :
    ¬ G.CompletelyPaired (x.leavesBelow ∪ y.leavesBelow) := by
  intro hcp
  have hm : ℓ ∈ x.leavesBelow ∪ y.leavesBelow := by
    simp only [GNode.leavesBelow, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h1
  obtain ⟨-, hp⟩ := hcp ℓ hm
  simp only [GNode.leavesBelow, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  rcases hp with hp | hp
  · exact h2 hp
  · exact h3 hp

/-- The outer leaves of the frame. -/
theorem frame_outer_leaf (Q : RegCpl) {u v : Fin 2 × Path} (huv : (u, v) ∈ outerPairs) :
    u.2 ∈ ((frameGarden Q).tree u.1).leaves ∧ v.2 ∈ ((frameGarden Q).tree v.1).leaves :=
  frame_pairs_valid Q (u, v) (List.mem_append_right _ huv)

theorem frame_outer_pair (Q : RegCpl) {u v : Fin 2 × Path} (huv : (u, v) ∈ outerPairs) :
    ((frameGarden Q).pair ⟨u, (frame_outer_leaf Q huv).1⟩).1 = v :=
  frameGarden_pair Q _ (List.mem_append_left _ (List.mem_append_right _ huv))

theorem frame_outer_pair' (Q : RegCpl) {u v : Fin 2 × Path} (huv : (u, v) ∈ outerPairs) :
    ((frameGarden Q).pair ⟨v, (frame_outer_leaf Q huv).2⟩).1 = u :=
  frameGarden_pair Q _ (List.mem_append_right _
    (List.mem_map.mpr ⟨(u, v), List.mem_append_right _ huv, rfl⟩))

/-- **A frame witness**: an outer leaf below one of the two nodes whose partner is below neither. -/
theorem frame_ncp (Q : RegCpl) {x y : GNode (frameGarden Q).tree} {u v : Fin 2 × Path}
    (huv : (u, v) ∈ outerPairs ∨ (v, u) ∈ outerPairs) (h1 : Under x.1 u ∨ Under y.1 u) (h2 : ¬ Under x.1 v)
    (h3 : ¬ Under y.1 v) : ¬ (frameGarden Q).CompletelyPaired (x.leavesBelow ∪ y.leavesBelow) := by
  rcases huv with huv | huv
  · exact not_cp_of ⟨u, (frame_outer_leaf Q huv).1⟩ h1 (by rw [frame_outer_pair Q huv]; exact h2)
      (by rw [frame_outer_pair Q huv]; exact h3)
  · exact not_cp_of ⟨u, (frame_outer_leaf Q huv).2⟩ h1 (by rw [frame_outer_pair' Q huv]; exact h2)
      (by rw [frame_outer_pair' Q huv]; exact h3)

theorem frameAddrLayer_outer (LQ : LayeredGarden 2) (p q q' : ℕ) {z : Fin 2 × Path} (hz : ¬ [0, 0] <+: z.2) :
    frameAddrLayer LQ p q q' z = outerLayer p q q' z := by
  unfold frameAddrLayer
  rw [ite_eq_right hz]

section Canon

variable {Q : RegCpl} {LQ : LayeredGarden 2} (hQ : Q.Decodes LQ.garden) {p q q' : ℕ} (hqq : q' ≤ q)
  (hqp : q ≤ p) (ha : layerAt LQ ((0 : Fin 2), []) ≤ q) (hb : layerAt LQ ((1 : Fin 2), []) ≤ q')

theorem frame_layer (x : GNode (frameLayered hQ hqq hqp ha hb).garden.tree) :
    (frameLayered hQ hqq hqp ha hb).layer x = frameAddrLayer LQ p q q' x.1 := rfl

theorem frame_parentLayer (x : GNode (frameLayered hQ hqq hqp ha hb).garden.tree) :
    (frameLayered hQ hqq hqp ha hb).parentLayer p x =
      if x.1.2 = [] then p else frameAddrLayer LQ p q q' (x.1.1, x.1.2.dropLast) := by
  unfold LayeredGarden.parentLayer
  split_ifs <;> rfl

include hQ in
omit hqq hqp ha hb in
theorem frame_outer (x : Fin 2 × Path) (hn : x.2 ∈ ((frameGarden Q).tree x.1).nodes) (hx : ¬ InRegion fA fB x) :
    x.2 = [] ∨ x.2 = [0] ∨ x.2 = [0, 1] ∨ x.2 = [0, 2] ∨ x.2 = [1] ∨ x.2 = [2] := by
  have hn' : x.2 ∈ (frameForest Q x.1).nodes := hn
  rw [frameForest_eq hQ, frameTree_nodes] at hn'
  rcases hn' with h | h | ⟨u, -, h⟩ | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exfalso
    apply hx
    obtain ⟨j, path⟩ := x
    simp only at h
    subst h
    fin_cases j
    · exact Or.inl ⟨rfl, by simp [fA]⟩
    · exact Or.inr ⟨rfl, by simp [fB]⟩
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

include hQ in
/-- **The criterion away from the code.** -/
theorem frame_critOut : CritOut (frameLayered hQ hqq hqp ha hb) p fA fB := by
  intro x y hx hy hxy hcp
  rw [frame_parentLayer hQ hqq hqp ha hb x, frame_parentLayer hQ hqq hqp ha hb y, frame_layer hQ hqq hqp ha hb x,
    frame_layer hQ hqq hqp ha hb y]
  have hxo := frame_outer hQ x.1 x.2 hx
  have hyo := frame_outer hQ y.1 y.2 hy
  obtain ⟨⟨i, s⟩, hxm⟩ := x
  obtain ⟨⟨j, t⟩, hym⟩ := y
  simp only at hxo hyo ⊢
  rcases hxo with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hyo with rfl | rfl | rfl | rfl | rfl | rfl <;>
    fin_cases i <;> fin_cases j <;>
    simp only [List.dropLast, frameAddrLayer, outerLayer] <;>
    simp (config := { decide := true }) <;>
    first
    | omega
    | (revert hxy; simp (config := { decide := true }) [GNode.Incomparable, GNode.IsDesc]; done)
    | (refine absurd hcp (frame_ncp Q (u := ((0 : Fin 2), [0, 1])) (v := ((1 : Fin 2), [1])) ?_ ?_ ?_ ?_) <;> (simp (config := { decide := true }) [Under]; done))
    | (refine absurd hcp (frame_ncp Q (u := ((1 : Fin 2), [1])) (v := ((0 : Fin 2), [0, 1])) ?_ ?_ ?_ ?_) <;> (simp (config := { decide := true }) [Under]; done))
    | (refine absurd hcp (frame_ncp Q (u := ((0 : Fin 2), [0, 2])) (v := ((1 : Fin 2), [0, 2])) ?_ ?_ ?_ ?_) <;> (simp (config := { decide := true }) [Under]; done))
    | (refine absurd hcp (frame_ncp Q (u := ((1 : Fin 2), [0, 2])) (v := ((0 : Fin 2), [0, 2])) ?_ ?_ ?_ ?_) <;> (simp (config := { decide := true }) [Under]; done))
    | (refine absurd hcp (frame_ncp Q (u := ((1 : Fin 2), [0, 1])) (v := ((0 : Fin 2), [1])) ?_ ?_ ?_ ?_) <;> (simp (config := { decide := true }) [Under]; done))

theorem not_under_of_tree {a z : Fin 2 × Path} (h : a.1 ≠ z.1) : ¬ Under a z := fun hu => h hu.1

include hQ in
/-- **The criterion at the collapsed code.** -/
theorem frame_critAttach : CritAttach (frameLayered hQ hqq hqp ha hb) p fA fB (min q q') := by
  obtain ⟨ℓ₀, h₀a, h₀b⟩ := (frame_embeds Q).cross_leaf (exists_cross_pair Q fA fB)
  have hb1 : ((frameGarden Q).pair ℓ₀).1.1 = 1 := h₀b.1.symm
  intro x y hx hy hxy hcp
  rw [frame_parentLayer hQ hqq hqp ha hb x, frame_parentLayer hQ hqq hqp ha hb y, frame_layer hQ hqq hqp ha hb y]
  have hyo := frame_outer hQ y.1 y.2 hy
  obtain ⟨⟨i, s⟩, hxm⟩ := x
  obtain ⟨⟨j, t⟩, hym⟩ := y
  simp only at hx hyo ⊢
  rcases hx with hx | hx <;> simp only [fA, fB, Prod.mk.injEq] at hx <;> obtain ⟨rfl, rfl⟩ := hx <;>
    rcases hyo with rfl | rfl | rfl | rfl | rfl | rfl <;> fin_cases j <;>
    simp only [List.dropLast, frameAddrLayer, outerLayer] <;>
    simp (config := { decide := true }) <;>
    first
    | omega
    | (revert hxy; simp (config := { decide := true }) [GNode.Incomparable, GNode.IsDesc]; done)
    | (refine absurd hcp (frame_ncp Q (u := ((1 : Fin 2), [0, 1])) (v := ((0 : Fin 2), [1])) ?_ ?_ ?_ ?_) <;>
        (simp (config := { decide := true }) [Under]; done))
    | exact absurd hcp (not_cp_of ℓ₀ (Or.inl h₀a) (not_under_of_tree fun h => absurd (h.trans hb1) (by simp))
        (not_under_of_tree fun h => absurd (h.trans hb1) (by simp)))

theorem frame_parAt_fA : parAt (frameLayered hQ hqq hqp ha hb) p fA = q := by
  have hn : fA.2 ∈ ((frameLayered hQ hqq hqp ha hb).garden.tree fA.1).nodes := (frame_embeds Q).nodeA
  rw [parAt_of_mem _ p hn]
  unfold LayeredGarden.parentLayer
  simp [fA, frameLayered, frameAddrLayer, outerLayer]

theorem frame_parAt_fB : parAt (frameLayered hQ hqq hqp ha hb) p fB = q' := by
  have hn : fB.2 ∈ ((frameLayered hQ hqq hqp ha hb).garden.tree fB.1).nodes := (frame_embeds Q).nodeB
  rw [parAt_of_mem _ p hn]
  unfold LayeredGarden.parentLayer
  simp [fB, frameLayered, frameAddrLayer, outerLayer]

include hQ in
theorem frame_layer_le (x : GNode (frameLayered hQ hqq hqp ha hb).garden.tree) :
    (frameLayered hQ hqq hqp ha hb).layer x ≤ p := by
  rw [frame_layer]
  unfold frameAddrLayer
  split_ifs with h
  · -- a node of the code, below its root
    obtain ⟨⟨j, path⟩, hm⟩ := x
    obtain ⟨u, rfl⟩ := h
    have hm' : [0, 0] ++ u ∈ (frameForest Q j).nodes := hm
    rw [frameForest_eq hQ, frameTree_nodes] at hm'
    have hu : u ∈ (LQ.garden.tree j).nodes := by
      rcases hm' with h | h | ⟨v, hv, h⟩ | h | h | h | h <;> simp_all
    have hle := layerAt_le_of_under LQ (x := (j, [])) (z := (j, u)) (TTree.nil_mem_nodes _) hu
      ⟨rfl, List.nil_prefix⟩
    fin_cases j
    · exact hle.trans (ha.trans hqp)
    · exact hle.trans (hb.trans (hqq.trans hqp))
  · unfold outerLayer
    split_ifs <;> omega

/-- **The layered frame is canonical** whenever the code carries the `layerreg1` pattern. -/
theorem frame_canon (hP : LayerPattern (frameLayered hQ hqq hqp ha hb) p Q fA fB) :
    IsCanonGC (p + 1) (frameLayered hQ hqq hqp ha hb) := by
  refine ⟨frameGarden_plain Q, Or.inr ⟨rfl, fun j => by fin_cases j <;> rfl⟩, ?_⟩
  rw [layerreg1_part2 (frameGarden_plain Q) (frame_embeds Q) hP, frame_parAt_fA, frame_parAt_fB]
  exact ⟨frame_layer_le hQ hqq hqp ha hb, frame_critOut hQ hqq hqp ha hb, frame_critAttach hQ hqq hqp ha hb⟩

end Canon

end WaveTurbulence.PL234
