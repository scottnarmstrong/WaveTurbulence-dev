/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.RepAnalytic.NodeCentreCount

/-! # W5, node centres: `treelemma` (2) in Lean

`nodeCentre_count`: for fixed leaf centres `cl`, the compatible node-centre assignments form a finite set
of at most `C_0^m` elements (`C_0 = nodeBallCard d`, `m = ∑_j n(𝒯_j) = |𝒩|`).
`nodeCentre_cover`: every branching-consistent labelling `k` with `‖k_ℓ - a cl_ℓ‖ ≤ 1` at the leaves and
every assignment `cn` with `‖k_n - a cn_n‖ ≤ 1` at all nodes has `cn` in this set.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RepAnalytic
open WaveTurbulence Finset TTree

variable {w d : ℕ} {tree : Fin w → TTree}

theorem nodeExt_eq_of_adm {cl : GLeaf tree → (Fin d → ℤ)} {cn : GNode tree → (Fin d → ℤ)}
    (h : ∀ ℓ : GLeaf tree, cn ℓ.toNode = cl ℓ) :
    nodeExt cl (fun b => cn b.toNode) = cn := by
  classical
  funext a
  by_cases hb : a.1.2 ∈ (tree a.1.1).branching
  · have := nodeExt_branch cl (fun b => cn b.toNode) ⟨a.1, hb⟩
    exact this
  · have hl : a.1.2 ∈ (tree a.1.1).leaves := by
      rcases (TTree.mem_nodes_iff _ _).1 a.2 with h1 | h1
      · exact h1
      · exact absurd h1 hb
    have := nodeExt_leaf cl (fun b => cn b.toNode) ⟨a.1, hl⟩
    exact this.trans (h ⟨a.1, hl⟩).symm

/-- **`treelemma` (2), the count.** -/
theorem nodeCentre_count (cl : GLeaf tree → (Fin d → ℤ)) :
    {cn : GNode tree → (Fin d → ℤ) | NodeCentreAdm cl cn}.Finite ∧
      {cn : GNode tree → (Fin d → ℤ) | NodeCentreAdm cl cn}.ncard ≤
        nodeBallCard d ^ ∑ j, (tree j).order := by
  classical
  set M0 := Finset.univ.sup (fun a : GNode tree => a.1.2.length) with hM0
  have hle : ∀ a : GNode tree, a.1.2.length ≤ M0 := fun a =>
    Finset.le_sup (f := fun a : GNode tree => a.1.2.length) (Finset.mem_univ a)
  let rank : GBranch tree → ℕ := fun b => M0 - b.1.2.length
  have hdep : ∀ (b : GBranch tree) (x y : GBranch tree → (Fin d → ℤ)),
      (∀ b', rank b' < rank b → x b' = y b') → candidates cl x b = candidates cl y b := by
    intro b x y hxy
    have hi : ∀ i : Fin 3, nodeExt cl x (b.child i) = nodeExt cl y (b.child i) := by
      intro i
      have hlen : (b.child i).1.2.length = b.1.2.length + 1 := by simp [GBranch.child]
      have hl2 := hle (b.child i)
      unfold nodeExt
      by_cases h : (b.child i).1.2 ∈ (tree (b.child i).1.1).branching
      · simp only [h, dite_true]
        apply hxy
        show M0 - (b.child i).1.2.length < M0 - b.1.2.length
        omega
      · simp only [h, dite_false]
    have hc : childCombo cl x b = childCombo cl y b := by
      unfold childCombo; rw [hi 0, hi 1, hi 2]
    unfold candidates
    rw [hc]
  obtain ⟨hF, hC⟩ := ncard_solutions_le rank (nodeBallCard d) (nodeBallCard_pos d) (fun b x => candidates cl x b)
    (fun b x => card_candidates_le cl x b) hdep
  set A := {cn : GNode tree → (Fin d → ℤ) | NodeCentreAdm cl cn} with hA
  set S := {x : GBranch tree → (Fin d → ℤ) | ∀ b, x b ∈ candidates cl x b} with hS
  have hmaps : Set.MapsTo (fun cn b => cn b.toNode) A S := by
    intro cn hcn b
    have hext := nodeExt_eq_of_adm hcn.1
    rw [mem_candidates]
    have := hcn.2 b
    unfold childCombo
    rw [hext]
    simpa using this
  have hinj : Set.InjOn (fun cn : GNode tree → (Fin d → ℤ) => fun b : GBranch tree => cn b.toNode) A := by
    intro cn hcn cn' hcn' h
    rw [← nodeExt_eq_of_adm hcn.1, ← nodeExt_eq_of_adm hcn'.1]
    simp only [h]
  refine ⟨Set.Finite.of_injOn hmaps hinj hF, ?_⟩
  refine (Set.ncard_le_ncard_of_injOn _ hmaps hinj hF).trans ?_
  rw [← card_gbranch tree]
  exact hC

end WaveTurbulence.RepAnalytic
