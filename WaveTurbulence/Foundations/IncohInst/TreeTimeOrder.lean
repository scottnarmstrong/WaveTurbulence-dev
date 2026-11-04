/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WaveB.FrozenB1

/-! # Ancestor bounds from the literal source parent-child time inequalities -/

public section
namespace WaveTurbulence.IncohInst
open TTree

/-- The local source strict ordering of branching parent and branching child clocks. -/
@[expose] def TimeOrdered (t : TTree) (τ : Path → ℝ) : Prop :=
  ∀ p ∈ t.branching, ∀ j : Fin 3, p ++ [j] ∈ t.branching → τ (p ++ [j]) < τ p

/-- A tree with any branching node has a branching root. -/
theorem root_mem_branching_of_mem {t : TTree} {p : Path} (hp : p ∈ t.branching) : [] ∈ t.branching := by
  cases t with
  | leaf => simp only [TTree.branching, Finset.notMem_empty] at hp
  | node l m r => simp [TTree.branching]

/-- Child-prefix membership in the actual source branching set. -/
theorem mem_branching_cons (l m r : TTree) (j : Fin 3) (p : Path) :
    j :: p ∈ (TTree.node l m r).branching ↔ p ∈ (![l, m, r] j).branching := by
  fin_cases j <;> simp [TTree.branching, TTree.pre]

/-- The parent-child ordering restricts exactly to each source subtree. -/
theorem TimeOrdered.child {l m r : TTree} {τ : Path → ℝ} (h : TimeOrdered (.node l m r) τ)
    (j : Fin 3) : TimeOrdered (![l, m, r] j) (fun p => τ (j :: p)) := by
  intro p hp i hi
  have hparent := (mem_branching_cons l m r j p).2 hp
  have hchild := (mem_branching_cons l m r j (p ++ [i])).2 hi
  exact h (j :: p) hparent i hchild

/-- Every branching clock is at most its root clock, using only the source's local inequalities. -/
theorem time_le_root_of_ordered (t : TTree) (τ : Path → ℝ) (h : TimeOrdered t τ)
    (p : Path) (hp : p ∈ t.branching) : τ p ≤ τ [] := by
  induction t generalizing τ p with
  | leaf => simp only [TTree.branching, Finset.notMem_empty] at hp
  | node l m r hl hm hr =>
    have hroot : [] ∈ (TTree.node l m r).branching := by simp [TTree.branching]
    simp only [TTree.branching, TTree.pre, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
    rcases hp with rfl | ((⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩) | ⟨q, hq, rfl⟩)
    · exact le_refl _
    · have hc : [0] ∈ (TTree.node l m r).branching :=
        (mem_branching_cons l m r 0 []).2 (root_mem_branching_of_mem hq)
      exact (hl (fun p => τ (0 :: p)) (h.child 0) q hq).trans (h [] hroot 0 hc).le
    · have hc : [1] ∈ (TTree.node l m r).branching :=
        (mem_branching_cons l m r 1 []).2 (root_mem_branching_of_mem hq)
      exact (hm (fun p => τ (1 :: p)) (h.child 1) q hq).trans (h [] hroot 1 hc).le
    · have hc : [2] ∈ (TTree.node l m r).branching :=
        (mem_branching_cons l m r 2 []).2 (root_mem_branching_of_mem hq)
      exact (hr (fun p => τ (2 :: p)) (h.child 2) q hq).trans (h [] hroot 2 hc).le

end WaveTurbulence.IncohInst
