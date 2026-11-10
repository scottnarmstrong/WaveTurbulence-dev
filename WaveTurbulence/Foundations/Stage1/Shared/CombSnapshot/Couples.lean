/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.CombSnapshot.Components

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

end WaveTurbulence.Comb
