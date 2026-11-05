/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Canon.Basic
/-! Root subtree identities and the automatic irreducibility of two-root gardens. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem root_leavesBelow {w : ℕ} (G : Garden w) (j : Fin w) :
    (GNode.root G.tree j).leavesBelow = G.leavesOf {j} := by
  ext ℓ
  simp only [GNode.leavesBelow, Garden.leavesOf, mem_filter, mem_univ, true_and,
    GNode.IsDesc, GNode.root, GLeaf.toNode, mem_singleton, List.nil_prefix, and_true]
  exact eq_comm

theorem garden_two_irreducible (G : Garden 2) : G.Irreducible := by
  classical
  intro A hAn hAu hcp
  obtain ⟨j, hj⟩ := hAn
  have hsingle : A = {j} := by
    apply subset_antisymm
    · intro k hk
      simp only [mem_singleton]
      by_contra hkj
      have hu : A = univ := by
        ext i
        simp only [mem_univ, iff_true]
        have hi : i = j ∨ i = k := by
          fin_cases j <;> fin_cases k <;> fin_cases i <;> simp_all
        rcases hi with rfl | rfl
        · exact hj
        · exact hk
      exact hAu hu
    · exact singleton_subset_iff.mpr hj
  have hp : G.CompletelyPaired (GNode.root G.tree j).leavesBelow := by
    rw [root_leavesBelow, ← hsingle]
    exact hcp
  exact (Nat.not_even_iff_odd.mpr (Canon.odd_card_leavesBelow (GNode.root G.tree j)))
    (Canon.even_card_of_completelyPaired G _ _ rfl hp)

theorem root_pair_leavesBelow {w : ℕ} (G : Garden w) (i j : Fin w) :
    (GNode.root G.tree i).leavesBelow ∪ (GNode.root G.tree j).leavesBelow =
      G.leavesOf {i, j} := by
  rw [root_leavesBelow, root_leavesBelow]
  ext ℓ
  simp only [Garden.leavesOf, mem_union, mem_filter, mem_univ, true_and,
    mem_singleton, mem_insert]

theorem not_paired_root_pair {w : ℕ} (G : Garden w) (hw : 4 ≤ w)
    (hirr : G.Irreducible) (i j : Fin w) :
    ¬ G.CompletelyPaired ((GNode.root G.tree i).leavesBelow ∪
      (GNode.root G.tree j).leavesBelow) := by
  rw [root_pair_leavesBelow]
  apply hirr {i, j} (by simp)
  intro he
  have hc : ({i, j} : Finset (Fin w)).card ≤ 2 := by
    by_cases hij : i = j
    · simp [hij]
    · simp [Finset.card_pair hij]
  rw [he, Finset.card_univ, Fintype.card_fin] at hc
  omega

end WaveTurbulence.Induct
