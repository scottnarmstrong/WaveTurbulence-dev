/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.RepAnalytic.NodeCentreMain

/-! # W5, node centres: the partition of unity restricted to admissible centres

For a branching-consistent labelling `δ` with leaves in the unit balls around `a cl_ℓ`, the node factors
`χ_{x_b}(δ_b)`, `x : 𝒩 → ℤ^d`, sum to `1` over `x`, and every `x` with a nonzero term has `nodeExt cl x`
compatible (so lies in the finite set of at most `C_0^m` assignments of `nodeCentre_count`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RepAnalytic
open WaveTurbulence Finset TTree

variable {w d : ℕ} {tree : Fin w → TTree}

/-- `∑_x ∏_b χ_{x_b}(δ_b) = 1`. -/
theorem hasSum_node_chi (δ : GNode tree → Mom d) :
    HasSum (fun x : GBranch tree → (Fin d → ℤ) => ∏ b, chi d (x b) (δ b.toNode)) 1 := by
  classical
  have hs : ∀ b : GBranch tree, Summable fun m : Fin d → ℤ => ‖chi d m (δ b.toNode)‖ := fun b => by
    have := (hasSum_chi d (δ b.toNode)).summable
    simpa [Real.norm_of_nonneg (chi_nonneg d _ _)] using this
  have := (VineEstS3.Eng.hasSum_pi_prod (M := Fin d → ℤ) (𝕜 := ℝ)
    (fun b : GBranch tree => fun m => chi d m (δ b.toNode)) hs).2
  simpa [(hasSum_chi d _).tsum_eq] using this

/-- A nonzero term of the node partition has compatible centres. -/
theorem nodeCentreAdm_of_prod_ne_zero {cl : GLeaf tree → (Fin d → ℤ)} (δ : GNode tree → Mom d)
    (hδ : ∀ b : GBranch tree, δ b.toNode = δ (b.child 0) - δ (b.child 1) + δ (b.child 2))
    (hleaf : ∀ ℓ : GLeaf tree, ‖δ ℓ.toNode - latPt d (cl ℓ)‖ ≤ 1)
    {x : GBranch tree → (Fin d → ℤ)} (hx : ∏ b, chi d (x b) (δ b.toNode) ≠ 0) :
    NodeCentreAdm cl (nodeExt cl x) := by
  classical
  refine nodeCentreAdm_of_close (fun ℓ => nodeExt_leaf cl x ℓ) δ hδ (fun a => ?_)
  by_cases hb : a.1.2 ∈ (tree a.1.1).branching
  · let b : GBranch tree := ⟨a.1, hb⟩
    have hbr : a = b.toNode := rfl
    have hne : chi d (x b) (δ a) ≠ 0 := by
      have := (Finset.prod_ne_zero_iff.1 hx) b (Finset.mem_univ _)
      rwa [← hbr] at this
    have := norm_sub_le_one_of_chi_ne_zero hne
    have h2 : nodeExt cl x a = x b := by
      have := nodeExt_branch cl x b
      rwa [← hbr] at this
    rw [h2]; exact this
  · have hl : a.1.2 ∈ (tree a.1.1).leaves := by
      rcases (TTree.mem_nodes_iff _ _).1 a.2 with h1 | h1
      · exact h1
      · exact absurd h1 hb
    have h2 : nodeExt cl x a = cl ⟨a.1, hl⟩ := nodeExt_leaf cl x ⟨a.1, hl⟩
    rw [h2]
    exact hleaf ⟨a.1, hl⟩

end WaveTurbulence.RepAnalytic

namespace WaveTurbulence.RepAnalytic
open WaveTurbulence Finset TTree

variable {w d : ℕ} {tree : Fin w → TTree}

/-- The branching-node centre assignments compatible with the leaf centres `cl`. -/
def nodeCentreSet (cl : GLeaf tree → (Fin d → ℤ)) : Set (GBranch tree → (Fin d → ℤ)) :=
  {x | NodeCentreAdm cl (nodeExt cl x)}

/-- **`treelemma` (2), node centres.**  At most `C_0^m` node-centre assignments, `m = ∑_j n(𝒯_j)`. -/
theorem nodeCentreSet_finite_card (cl : GLeaf tree → (Fin d → ℤ)) :
    (nodeCentreSet cl).Finite ∧ (nodeCentreSet cl).ncard ≤ nodeBallCard d ^ ∑ j, (tree j).order := by
  obtain ⟨hF, hC⟩ := nodeCentre_count (tree := tree) (d := d) cl
  have hmaps : Set.MapsTo (nodeExt cl) (nodeCentreSet cl)
      {cn : GNode tree → (Fin d → ℤ) | NodeCentreAdm cl cn} := fun x hx => hx
  have hinj : Set.InjOn (nodeExt cl : (GBranch tree → (Fin d → ℤ)) → GNode tree → (Fin d → ℤ))
      (nodeCentreSet cl) := by
    intro x _ y _ h
    funext b
    have := congrFun h b.toNode
    rwa [nodeExt_branch, nodeExt_branch] at this
  exact ⟨Set.Finite.of_injOn hmaps hinj hF, (Set.ncard_le_ncard_of_injOn _ hmaps hinj hF).trans hC⟩

end WaveTurbulence.RepAnalytic
