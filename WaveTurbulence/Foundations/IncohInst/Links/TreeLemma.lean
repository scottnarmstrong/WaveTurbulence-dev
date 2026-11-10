/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.IncohInst.Links.Auxlem
public import WaveTurbulence.Foundations.IncohInst.Links.Bridge
public import WaveTurbulence.Foundations.Links.Cover

/-!
# Localization of tree decorations: DH23 Lemma A.4 (`explem`), TARGET Lemma `treelemma` (2)

For a ternary tree `𝒯` of order `n` and decorations `(k_𝔫)` (`k_𝔫 = k_{𝔫₁} - k_{𝔫₂} + k_{𝔫₃}` at
every branching node) with `|k_ℓ - k_ℓ⁰| ≤ 1` at every leaf:

* `explem_one` (DH23 Lemma A.4 (1), TARGET `treelemma` (2)): the decorations split into at most
  `C^n` sub-collections (`C` depending only on `d`) on each of which every `k_𝔫` lies in a fixed unit
  ball: there is a set `S` of at most `C^n` center maps `c` such that every such decoration is within
  `1` of some `c ∈ S` at every node;
* `explem_two` (DH23 Lemma A.4 (2)): the same for the projections `r · k_𝔫`, `|r| ≤ 1`, with at most
  `3^n ∏_ℓ (2|k_ℓ⁰| + 5)` center maps, the same family for every `r`.

The proof localizes bottom-up: the root value is within `3` of the alternating sum of the children's
centers, and a ball of radius `3` is covered by a fixed number of unit balls
(`Foundations/Links/Cover.lean`).
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree

/-- A decoration of a single ternary tree `t` (TARGET Def `defdec`): the node relation at every
branching node; the leaves are free. -/
def TreeDec {V : Type*} [AddCommGroup V] (t : TTree) (k : Path → V) : Prop :=
  ∀ p ∈ t.branching, k p = k (p ++ [0]) - k (p ++ [1]) + k (p ++ [2])

theorem mem_pre {i j : Fin 3} {S : Finset Path} {q : Path} : j :: q ∈ pre i S ↔ i = j ∧ q ∈ S := by
  simp only [pre, Finset.mem_image, List.cons.injEq]
  constructor
  · rintro ⟨q', hq', rfl, rfl⟩; exact ⟨rfl, hq'⟩
  · rintro ⟨rfl, hq⟩; exact ⟨q, hq, rfl, rfl⟩

theorem treeDec_child {V : Type*} [AddCommGroup V] {l m r : TTree} {k : Path → V}
    (h : TreeDec (.node l m r) k) :
    k [] = k [0] - k [1] + k [2] ∧ TreeDec l (fun p => k (0 :: p)) ∧
      TreeDec m (fun p => k (1 :: p)) ∧ TreeDec r (fun p => k (2 :: p)) := by
  refine ⟨h [] (by simp [TTree.branching]), fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩ <;>
    exact h _ (by simp [TTree.branching, mem_pre, hp])

/-- A decoration of a garden restricts to a decoration of each of its trees. -/
theorem treeDec_of_isDecoration {V : Type*} [AddCommGroup V] {w : ℕ} {G : Garden w}
    {κ : GNode G.tree → V} (hκ : IsDecoration G κ) (j : Fin w) :
    TreeDec (G.tree j) (fun p => extend κ (j, p)) := fun p hp =>
  nodeRel_extend hκ ⟨(j, p), hp⟩

end WaveTurbulence.Links
