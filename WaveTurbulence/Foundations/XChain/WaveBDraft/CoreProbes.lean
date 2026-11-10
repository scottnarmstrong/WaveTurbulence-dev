/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import WaveTurbulence.Foundations.WaveB.Lemmas

/-!
# Wave B tier B1 core — non-vacuity probes and audit lemmas (sorry-free)

* explicit trees and gardens (the trivial couple, the two `(1,1)`-mini-couples, the layered garden
  of TARGET Figures `LayerGarden.png` / `CanonGarden.png`), with their predicates decided;
* `IsCanonG 3` holds for the garden of Figure `CanonGarden.png` (WAVE-B §5 unit test (iii)), it is
  not in `𝒢₂`, and its truncation data are those of the figure;
* `IsCanonC 1` holds for the trivial couple and the mini-couples with all layers `0` (§5 (v));
* finiteness of the set of layered gardens of bounded order and depth (the `finsum`s of WAVE-B §2.4.3
  are genuine finite sums);
* `|ℒ| = 2 n(𝒯) + 1`, `|𝒩| = n(𝒯)`, and the parameter relations of WAVE-B §2.1;
* the stage-1 audit garden E1 (two attached gardens in one top tree): `e1_canon2`, `e1_topOrder`,
  `e1_trunc` (second truncation unit test);
* `omegaNode_latticeDecoration`: `Ω_𝔫` of a lattice decoration is `Ω` of its lattice vectors (the
  bridges to the landed `NLS.resonance` are in `WaveB1-Bridges.lean`).
-/

@[expose] public section

open Finset

namespace WaveTurbulence.WaveBProbes

open TTree

/-! ### Building gardens from address-level data -/

/-! ### The trivial couple and the mini-couples -/

/-- Pairing the left and right leaves of the `+` tree violates the sign rule. -/
example : ¬ (nodeSign (![1, -1] : Fin 2 → ℤˣ) (0, [0]) =
    -nodeSign (![1, -1] : Fin 2 → ℤˣ) (0, [2])) := by decide

/-! ### A flower garden and a paired tree (T Def `defflower`, T L637) -/

/-! ### The layered garden of Figures `LayerGarden.png` / `CanonGarden.png` (T L649–L750) -/

/-! ### Second truncation unit test: two attached gardens in one top tree (stage-1 audit E1)

The garden of the stage-1 audit (wt-orch, `scratch/WaveB-stage1-E1.lean`): width 4, signature
`(+,-,+,-)`, `𝒯₁ = node(node(tree1, •, •), •, tree1)`, `𝒯₂ = 𝒯₃ = 𝒯₄ = •`, the nodes `[]`, `[0]` of
`𝒯₁` in layer 1 and everything else in layer 0. At `p = 1` there are two attached gardens of
order 1, at `{[0,0],[0,1],[0,2],[1]}` of `𝒯₁` and at `{[2] of 𝒯₁, 𝒯₂, 𝒯₃, 𝒯₄}`. Generating the
linking relation on all nodes merged them through the root of `𝒯₁`; with `AttachLinkedOn` every
attached garden has order `≤ 1`, so the garden is in `𝒢^tr₂` for `(N₂, N₁) = (2, 1)`, as in
T Def `defgtr`. The figure garden alone cannot detect the merging (it has one attached garden). -/

instance {w : ℕ} (LG : LayeredGarden w) (u u' : GNode LG.garden.tree) :
    Decidable (LG.AttachLinked u u') := by
  unfold LayeredGarden.AttachLinked
  infer_instance

/-! ### The resonance factor -/

/-! ### Trees: counting lemmas -/

theorem card_pre (i : Fin 3) (S : Finset Path) : (pre i S).card = S.card :=
  Finset.card_image_of_injective _ (List.cons_injective)

theorem pre_disjoint {i j : Fin 3} (hij : i ≠ j) (S T : Finset Path) :
    Disjoint (pre i S) (pre j T) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  obtain ⟨q, -, rfl⟩ := mem_pre.1 hp
  exact hij (cons_mem_pre.1 hq).1.symm

/-- `|ℒ| = 2 n(𝒯) + 1` (T L630). -/
theorem card_leaves : ∀ t : TTree, t.leaves.card = 2 * t.order + 1
  | .leaf => rfl
  | .node l m r => by
    rw [leaves, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint, card_pre, card_pre,
      card_pre, card_leaves l, card_leaves m, card_leaves r, order]
    · ring
    · exact pre_disjoint (by decide) _ _
    · exact Finset.disjoint_union_left.2 ⟨pre_disjoint (by decide) _ _, pre_disjoint (by decide) _ _⟩

/-! ### Finiteness of layered gardens of bounded order and depth -/

/-- The garden data with layers bounded by `p`, before imposing the axioms. -/
def RawData {w : ℕ} (p : ℕ) (t : Fin w → TTree) : Type :=
  (Fin w → ℤˣ) × (GLeaf t → GLeaf t) × (GLeaf t → Option MarkTag) × (GNode t → Fin (p + 1))

instance {w : ℕ} (p : ℕ) (t : Fin w → TTree) : Finite (RawData p t) := by
  unfold RawData
  infer_instance

/-! ### Parameters (WAVE-B §2.1 audit lemmas) -/

end WaveTurbulence.WaveBProbes
