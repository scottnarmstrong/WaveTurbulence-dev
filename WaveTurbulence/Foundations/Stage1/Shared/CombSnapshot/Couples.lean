/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.CombSnapshot.Components
public import WaveTurbulence.Foundations.Stage1.Shared.CombSnapshot.SignCounts

/-! # Irreducible couples and the lone leaf (TARGET L634–L643) -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.Comb
open TTree Finset

/-- A single tree cannot have all its leaves paired with opposite signs (TARGET L636). -/
theorem not_completelyPaired_one_tree {w : ℕ} (G : Garden w) (j : Fin w) :
    ¬ G.CompletelyPaired (G.leavesOf {j}) := by
  intro hp
  let κ : GNode G.tree → ℤ := fun _ => 1
  have hc : ∀ b : GBranch G.tree, κ b.toNode = κ (b.child 0) - κ (b.child 1) + κ (b.child 2) :=
    fun _ => by norm_num [κ]
  have hs := sum_rule G.sig κ hc (GNode.root G.tree j)
  have he : (GNode.root G.tree j).leavesBelow = G.leavesOf {j} := by
    ext ℓ
    simp [GNode.leavesBelow, Garden.leavesOf, GNode.IsDesc, GNode.root, GLeaf.toNode, eq_comm]
  rw [he, sum_signed_completelyPaired hp κ (fun _ => rfl)] at hs
  simp [κ, nodeSign, GNode.root, pathSign] at hs

/-- Every couple is irreducible (TARGET L636); in fact width two alone suffices. -/
theorem couple_irreducible (G : Garden 2) : G.Irreducible := by
  intro A hA hproper
  have hh : ∀ A : Finset (Fin 2), A.Nonempty → A ≠ Finset.univ → A = {0} ∨ A = {1} := by decide
  rcases hh A hA hproper with rfl | rfl <;> exact not_completelyPaired_one_tree G _

/-- A paired tree has an actual lone leaf (TARGET L637). -/
theorem pairedTree_exists_lone {G : Garden 1} (hG : IsPairedTree G) :
    ∃ ℓ : GLeaf G.tree, G.IsLone ℓ := by
  obtain ⟨ℓ, hℓ⟩ := Finset.card_pos.mp (by rw [hG.1]; decide)
  exact ⟨ℓ, hG.2 ℓ (Finset.mem_filter.mp hℓ).2⟩

/-- The lone leaf is unique and has the root sign (TARGET L637–L643). -/
theorem pairedTree_existsUnique_lone {G : Garden 1} (hG : IsPairedTree G) :
    ∃! ℓ : GLeaf G.tree, G.IsLone ℓ := by
  obtain ⟨ℓ, hℓ⟩ := pairedTree_exists_lone hG
  exact ⟨ℓ, hℓ, fun ℓ' hℓ' => IsPairedTree.eq_of_isLone hG hℓ' hℓ⟩

/-- The root and lone leaf values agree for every paired-tree decoration (TARGET L643). -/
theorem pairedTree_root_eq_lone {G : Garden 1} (hG : IsPairedTree G)
    {V : Type*} [AddCommGroup V] {κ : GNode G.tree → V} (hκ : IsDecoration G κ)
    {ℓ : GLeaf G.tree} (hℓ : G.IsLone ℓ) : κ (GNode.root G.tree 0) = κ ℓ.toNode := by
  have hv := IsPairedTree.lone_value hG hκ hℓ
  have hs := IsPairedTree.sign_lone hG hℓ
  have hr : G.sign (GNode.root G.tree 0) = G.sig 0 := by
    simp [Garden.sign, nodeSign, GNode.root, pathSign]
  rw [hs, hr] at hv
  rcases Int.units_eq_one_or (G.sig 0) with h | h <;> rw [h] at hv <;> simpa using hv.symm

/-- A couple decoration has the same momentum at its two roots (TARGET L643). -/
theorem couple_root_values_eq {G : Garden 2} (hG : IsCouple G)
    {V : Type*} [AddCommGroup V] {κ : GNode G.tree → V} (hκ : IsDecoration G κ) :
    κ (GNode.root G.tree 0) = κ (GNode.root G.tree 1) := by
  have hs := sum_signed_roots_eq_zero hG.1 hκ
  have he : κ (GNode.root G.tree 0) - κ (GNode.root G.tree 1) = 0 := by
    simpa [Fin.sum_univ_two, hG.2, sub_eq_add_neg] using hs
  exact sub_eq_zero.mp he

end WaveTurbulence.Comb
