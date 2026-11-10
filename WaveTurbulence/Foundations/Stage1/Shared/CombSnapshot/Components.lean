/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.Gardens
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-! # Components of a garden (TARGET L636)

The graph has one vertex per tree and an edge for a leaf pair between distinct
trees. Its finite connected components give a decidable partition of the trees.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.Comb
open Finset

variable {w : ℕ}

/-- Two distinct trees are adjacent when one of their leaves is paired across. -/
@[expose] def treeGraph (G : Garden w) : SimpleGraph (Fin w) where
  Adj i j := i ≠ j ∧ ∃ ℓ : GLeaf G.tree, ℓ.1.1 = i ∧ (G.pair ℓ).1.1 = j
  symm := ⟨by
    rintro i j ⟨hne, ℓ, hi, hj⟩
    refine ⟨hne.symm, G.pair ℓ, hj, ?_⟩
    rw [G.pair_pair]
    exact hi⟩
  loopless := ⟨fun i h => h.1 rfl⟩

instance (G : Garden w) : DecidableRel (treeGraph G).Adj := by
  intro i j
  change Decidable (i ≠ j ∧ ∃ ℓ : GLeaf G.tree, ℓ.1.1 = i ∧ (G.pair ℓ).1.1 = j)
  infer_instance

/-- The tree indices in the component containing tree `i`. -/
@[expose] def component (G : Garden w) (i : Fin w) : Finset (Fin w) :=
  Finset.univ.filter ((treeGraph G).Reachable i)

/-- Every tree belongs to its component. -/
theorem mem_component_self (G : Garden w) (i : Fin w) : i ∈ component G i := by
  simp [component]

/-- Paired leaves belong to the same component, even when they lie in one tree. -/
theorem reachable_pair (G : Garden w) (ℓ : GLeaf G.tree) :
    (treeGraph G).Reachable ℓ.1.1 (G.pair ℓ).1.1 := by
  by_cases h : ℓ.1.1 = (G.pair ℓ).1.1
  · simpa only [h] using (SimpleGraph.Reachable.refl (G := treeGraph G) (G.pair ℓ).1.1)
  · exact SimpleGraph.Adj.reachable ⟨h, ℓ, rfl, rfl⟩

/-- Components are closed under the leaf pairing. -/
theorem component_completelyPaired (G : Garden w) (hG : G.IsPlain) (i : Fin w) :
    G.CompletelyPaired (G.leavesOf (component G i)) := by
  intro ℓ hℓ
  refine ⟨pair_ne_of_plain hG ℓ, ?_⟩
  simp only [Garden.leavesOf, Finset.mem_filter, Finset.mem_univ, true_and,
    component] at hℓ ⊢
  exact hℓ.trans (reachable_pair G ℓ)


/-- A pairing-closed set of trees contains every tree reachable from one of its members. -/
theorem reachable_preserves_closed (G : Garden w) {A : Finset (Fin w)}
    (hA : ∀ ℓ : GLeaf G.tree, ℓ.1.1 ∈ A → (G.pair ℓ).1.1 ∈ A)
    {i j : Fin w} (hij : (treeGraph G).Reachable i j) (hi : i ∈ A) : j ∈ A := by
  have h := (SimpleGraph.reachable_iff_reflTransGen i j).mp hij
  clear hij
  induction h with
  | refl => exact hi
  | tail h ha ih =>
    obtain ⟨hne, ℓ, hℓi, hℓj⟩ := ha
    rw [← hℓj]
    apply hA ℓ
    rw [hℓi]
    exact ih

/-- Irreducibility is exactly connectedness of the tree-pairing graph (TARGET L636). -/
theorem irreducible_iff_preconnected (G : Garden w) (hG : G.IsPlain) :
    G.Irreducible ↔ (treeGraph G).Preconnected := by
  constructor
  · intro h i j
    by_contra hij
    have hproper : component G i ≠ Finset.univ := by
      intro he
      have hj : j ∈ component G i := he ▸ Finset.mem_univ j
      exact hij (Finset.mem_filter.mp hj).2
    exact h (component G i) ⟨i, mem_component_self G i⟩ hproper
      (component_completelyPaired G hG i)
  · intro h A hA hproper hclosed
    obtain ⟨i, hi⟩ := hA
    apply hproper
    apply Finset.eq_univ_of_forall
    intro j
    refine reachable_preserves_closed G (i := i) ?_ (h i j) hi
    intro ℓ hℓ
    exact (Finset.mem_filter.mp ((hclosed ℓ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hℓ⟩)).2)).2

/-- A multi-couple has components of width two (TARGET L636). -/
@[expose] def IsMultiCouple (G : Garden w) : Prop :=
  G.IsPlain ∧ ∀ i : Fin w, (component G i).card = 2

instance (G : Garden w) : Decidable (IsMultiCouple G) := by
  unfold IsMultiCouple
  infer_instance

end WaveTurbulence.Comb
