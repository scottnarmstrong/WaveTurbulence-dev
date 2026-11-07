/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.RepAnalytic.RankCount
public import WaveTurbulence.Foundations.Stage1.RepAnalytic.Partition
public import WaveTurbulence.Foundations.WaveB.Lemmas

/-! # W5, node centres: the counting behind TARGET `treelemma` (2)

TARGET Lemma `treelemma` (L2422; DH21 Lemma 6.6, DH23 Lemma A.4): for a decoration whose leaves lie in
fixed unit balls, the collection of decorations splits into at most `C_0^m` sub-collections, each with all
node momenta in fixed unit balls.  In the partition-of-unity language of `RepAnalytic.Partition`: given
the leaf centres `c_ℓ ∈ ℤ^d` (the lattice points `a c_ℓ`), the node-centre assignments
`c : GNode → ℤ^d` that can occur with `‖k_n - a c_n‖ ≤ 1` for a branching-consistent `k` (with
`‖k_ℓ - a c_ℓ‖ ≤ 1` at leaves) number at most `M^m`, `M = nodeBallCard d`, `m = ∑ order`.
Each node's centre is determined, up to `M` choices, by its three children (`k_n = k_{n0} - k_{n1} +
k_{n2}`), so that we count bottom-up; no ordering by leaf counts is needed for (2).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RepAnalytic
open WaveTurbulence Finset TTree

variable {w d : ℕ} {tree : Fin w → TTree}

theorem latPt_add (n m : Fin d → ℤ) : latPt d (n + m) = latPt d n + latPt d m := by
  ext i; simp [latPt, mul_add]

theorem latPt_sub (n m : Fin d → ℤ) : latPt d (n - m) = latPt d n - latPt d m := by
  ext i; simp [latPt, mul_sub]

theorem abs_le_of_norm_latPt_le {n : Fin d → ℤ} {r : ℝ} (h : ‖latPt d n‖ ≤ r) (i : Fin d) :
    |(n i : ℝ)| ≤ r / lsp d := by
  have h1 : |latPt d n i| ≤ ‖latPt d n‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (latPt d n) i
  have h2 : |latPt d n i| = lsp d * |(n i : ℝ)| := by
    simp [latPt, abs_mul, abs_of_pos (lsp_pos d)]
  rw [le_div_iff₀ (lsp_pos d)]
  nlinarith

/-- Compatibility of node centres `cn` with leaf centres `cl`: each branching node's centre lies within
`4` of the combination of its children's centres. -/
def NodeCentreAdm (cl : GLeaf tree → (Fin d → ℤ)) (cn : GNode tree → (Fin d → ℤ)) : Prop :=
  (∀ ℓ : GLeaf tree, cn ℓ.toNode = cl ℓ) ∧
    ∀ b : GBranch tree, ‖latPt d (cn b.toNode - (cn (b.child 0) - cn (b.child 1) + cn (b.child 2)))‖ ≤ 4

/-- The centres of any branching-consistent labelling that is `1`-close to the centres are compatible. -/
theorem nodeCentreAdm_of_close {cl : GLeaf tree → (Fin d → ℤ)} {cn : GNode tree → (Fin d → ℤ)}
    (hleaf : ∀ ℓ : GLeaf tree, cn ℓ.toNode = cl ℓ) (δ : GNode tree → Mom d)
    (hδ : ∀ b : GBranch tree, δ b.toNode = δ (b.child 0) - δ (b.child 1) + δ (b.child 2))
    (hclose : ∀ a, ‖δ a - latPt d (cn a)‖ ≤ 1) : NodeCentreAdm cl cn := by
  refine ⟨hleaf, fun b => ?_⟩
  rw [latPt_sub, latPt_add, latPt_sub]
  have h0 := hclose b.toNode
  have h1 := hclose (b.child 0)
  have h2 := hclose (b.child 1)
  have h3 := hclose (b.child 2)
  have key : latPt d (cn b.toNode) - (latPt d (cn (b.child 0)) - latPt d (cn (b.child 1)) +
      latPt d (cn (b.child 2))) = -(δ b.toNode - latPt d (cn b.toNode)) +
      ((δ (b.child 0) - latPt d (cn (b.child 0))) - (δ (b.child 1) - latPt d (cn (b.child 1))) +
        (δ (b.child 2) - latPt d (cn (b.child 2)))) := by
    rw [hδ b]; abel
  rw [key]
  calc _ ≤ ‖-(δ b.toNode - latPt d (cn b.toNode))‖ + ‖((δ (b.child 0) - latPt d (cn (b.child 0))) -
        (δ (b.child 1) - latPt d (cn (b.child 1))) + (δ (b.child 2) - latPt d (cn (b.child 2))))‖ :=
        norm_add_le _ _
    _ ≤ 1 + (‖δ (b.child 0) - latPt d (cn (b.child 0))‖ + ‖δ (b.child 1) - latPt d (cn (b.child 1))‖ +
        ‖δ (b.child 2) - latPt d (cn (b.child 2))‖) := by
        rw [norm_neg]
        have e : ‖(δ (b.child 0) - latPt d (cn (b.child 0))) - (δ (b.child 1) - latPt d (cn (b.child 1))) +
            (δ (b.child 2) - latPt d (cn (b.child 2)))‖ ≤ ‖δ (b.child 0) - latPt d (cn (b.child 0))‖ +
            ‖δ (b.child 1) - latPt d (cn (b.child 1))‖ + ‖δ (b.child 2) - latPt d (cn (b.child 2))‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
        linarith
    _ ≤ 4 := by linarith

end WaveTurbulence.RepAnalytic
