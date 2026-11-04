/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Foundations.Links.Cover
import Mathlib.Tactic

/-!
# An auxiliary ternary shape for finite momentum localization

This local analytic shape contains only addresses, parent/child momentum
relations and leaf balls. C2 instantiates it by forgetting signs and links
of its source tree. No analytic bound is a field.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh

/-- Auxiliary shape of the tree localization argument. -/
inductive LocalizationTree where
  | leaf
  | node (left middle right : LocalizationTree)

namespace LocalizationTree

abbrev Path := List (Fin 3)

/-- Actual number of branching vertices of the auxiliary shape. -/
@[expose] def order : LocalizationTree → ℕ
  | .leaf => 0
  | .node l m r => l.order + m.order + r.order + 1

/-- Prefix an address set by its child index. -/
@[expose] def pre (i : Fin 3) (S : Finset Path) : Finset Path := S.image (List.cons i)

/-- Every vertex address, including the root. -/
@[expose] def nodes : LocalizationTree → Finset Path
  | .leaf => {[]}
  | .node l m r => insert [] (pre 0 l.nodes ∪ pre 1 m.nodes ∪ pre 2 r.nodes)

/-- The actual leaf addresses. -/
@[expose] def leaves : LocalizationTree → Finset Path
  | .leaf => {[]}
  | .node l m r => pre 0 l.leaves ∪ pre 1 m.leaves ∪ pre 2 r.leaves

/-- The actual branching addresses. -/
@[expose] def branching : LocalizationTree → Finset Path
  | .leaf => ∅
  | .node l m r => insert [] (pre 0 l.branching ∪ pre 1 m.branching ∪ pre 2 r.branching)

/-- A decoration of a single ternary tree `t` (TARGET Def `defdec`): the node relation at every
branching node; the leaves are free. -/
@[expose] def IsDecoration {V : Type*} [AddCommGroup V] (t : LocalizationTree) (k : Path → V) : Prop :=
  ∀ p ∈ t.branching, k p = k (p ++ [0]) - k (p ++ [1]) + k (p ++ [2])

theorem mem_pre {i j : Fin 3} {S : Finset Path} {q : Path} : j :: q ∈ pre i S ↔ i = j ∧ q ∈ S := by
  simp only [pre, Finset.mem_image, List.cons.injEq]
  constructor
  · rintro ⟨q', hq', rfl, rfl⟩; exact ⟨rfl, hq'⟩
  · rintro ⟨rfl, hq⟩; exact ⟨q, hq, rfl, rfl⟩

theorem treeDec_child {V : Type*} [AddCommGroup V] {l m r : LocalizationTree} {k : Path → V}
    (h : IsDecoration (.node l m r) k) :
    k [] = k [0] - k [1] + k [2] ∧ IsDecoration l (fun p => k (0 :: p)) ∧
      IsDecoration m (fun p => k (1 :: p)) ∧ IsDecoration r (fun p => k (2 :: p)) := by
  refine ⟨h [] (by simp [LocalizationTree.branching]), fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩ <;>
    exact h _ (by simp [LocalizationTree.branching, mem_pre, hp])

theorem mem_nodes_node {l m r : LocalizationTree} {p : Path} (hp : p ∈ (LocalizationTree.node l m r).nodes) :
    p = [] ∨ ∃ i : Fin 3, ∃ q, p = i :: q ∧ q ∈ (![l, m, r] i).nodes := by
  rcases p with _ | ⟨j, q⟩
  · exact Or.inl rfl
  · simp only [LocalizationTree.nodes, Finset.mem_insert, Finset.mem_union, mem_pre, reduceCtorEq,
      false_or] at hp
    right
    rcases hp with (⟨rfl, h⟩ | ⟨rfl, h⟩) | ⟨rfl, h⟩
    · exact ⟨0, q, rfl, h⟩
    · exact ⟨1, q, rfl, h⟩
    · exact ⟨2, q, rfl, h⟩

theorem leaves_child {α : Type*} {l m r : LocalizationTree} {k k0 : Path → α} [Norm α] [Sub α]
    (h : ∀ p ∈ (LocalizationTree.node l m r).leaves, ‖k p - k0 p‖ ≤ 1) (i : Fin 3) :
    ∀ p ∈ (![l, m, r] i).leaves, ‖k (i :: p) - k0 (i :: p)‖ ≤ 1 := fun p hp =>
  h _ (by fin_cases i <;> simp [LocalizationTree.leaves, mem_pre] at hp ⊢ <;> exact hp)

/-- A map on paths with value `v` at the root and `c i` below the `i`-th child. -/
@[expose] def combine {α : Type*} (v : α) (c : Fin 3 → Path → α) : Path → α
  | [] => v
  | i :: p => c i p


end LocalizationTree
end WaveTurbulence.Incoh
