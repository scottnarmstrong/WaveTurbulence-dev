/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.RepAnalytic.NodeCentres

/-! # W5, node centres: the count (TARGET `treelemma` (2), loss `C_0^m`) -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RepAnalytic
open WaveTurbulence Finset TTree

variable {w d : ℕ} {tree : Fin w → TTree}

/-- `C_0 = (2·4(d+1)+1)^d`: a bound for the number of lattice points `a n` in a ball of radius `4`. -/
def nodeBallCard (d : ℕ) : ℕ := (2 * (4 * (d + 1)) + 1) ^ d

theorem nodeBallCard_pos (d : ℕ) : 0 < nodeBallCard d := by unfold nodeBallCard; positivity

open Classical in
/-- The leaf centres, extended by `0`. -/
noncomputable def leafExt (cl : GLeaf tree → (Fin d → ℤ)) (a : GNode tree) : Fin d → ℤ :=
  if h : a.1.2 ∈ (tree a.1.1).leaves then cl ⟨a.1, h⟩ else 0

open Classical in
/-- Leaf centres `cl` and branching centres `x`, as a function on all nodes. -/
noncomputable def nodeExt (cl : GLeaf tree → (Fin d → ℤ)) (x : GBranch tree → (Fin d → ℤ))
    (a : GNode tree) : Fin d → ℤ :=
  if h : a.1.2 ∈ (tree a.1.1).branching then x ⟨a.1, h⟩ else leafExt cl a

theorem nodeExt_branch (cl : GLeaf tree → (Fin d → ℤ)) (x : GBranch tree → (Fin d → ℤ))
    (b : GBranch tree) : nodeExt cl x b.toNode = x b := by
  unfold nodeExt
  show (if h : b.1.2 ∈ (tree b.1.1).branching then x ⟨b.1, h⟩ else leafExt cl b.toNode) = x b
  simp only [b.2, dite_true]
  rfl

theorem nodeExt_leaf (cl : GLeaf tree → (Fin d → ℤ)) (x : GBranch tree → (Fin d → ℤ))
    (ℓ : GLeaf tree) : nodeExt cl x ℓ.toNode = cl ℓ := by
  unfold nodeExt leafExt
  show (if h : ℓ.1.2 ∈ (tree ℓ.1.1).branching then x ⟨ℓ.1, h⟩ else
    if h : ℓ.1.2 ∈ (tree ℓ.1.1).leaves then cl ⟨ℓ.1, h⟩ else 0) = cl ℓ
  have hnb : ¬ ℓ.1.2 ∈ (tree ℓ.1.1).branching := fun hb =>
    TTree.not_mem_branching_of_mem_leaves _ ℓ.2 hb
  simp only [hnb, ℓ.2, dite_false, dite_true]
  rfl

/-- The centre combination of the children. -/
noncomputable def childCombo (cl : GLeaf tree → (Fin d → ℤ)) (x : GBranch tree → (Fin d → ℤ))
    (b : GBranch tree) : Fin d → ℤ :=
  nodeExt cl x (b.child 0) - nodeExt cl x (b.child 1) + nodeExt cl x (b.child 2)

open Classical in
/-- The candidate centres of the branching node `b` given the others. -/
noncomputable def candidates (cl : GLeaf tree → (Fin d → ℤ)) (x : GBranch tree → (Fin d → ℤ))
    (b : GBranch tree) : Finset (Fin d → ℤ) :=
  (Fintype.piFinset fun i => Finset.Icc (childCombo cl x b i - 4 * ((d : ℤ) + 1))
      (childCombo cl x b i + 4 * ((d : ℤ) + 1))).filter
    fun z => ‖latPt d (z - childCombo cl x b)‖ ≤ 4

theorem mem_candidates {cl : GLeaf tree → (Fin d → ℤ)} {x : GBranch tree → (Fin d → ℤ)}
    {b : GBranch tree} {z : Fin d → ℤ} :
    z ∈ candidates cl x b ↔ ‖latPt d (z - childCombo cl x b)‖ ≤ 4 := by
  classical
  unfold candidates
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun i => ?_, h⟩
    have := abs_le_of_norm_latPt_le h i
    have hl : (4 : ℝ) / lsp d = 4 * ((d : ℝ) + 1) := by unfold lsp; field_simp
    rw [hl] at this
    have h2 : |((z - childCombo cl x b) i : ℤ)| ≤ 4 * ((d : ℤ) + 1) := by
      have : (|((z - childCombo cl x b) i : ℤ)| : ℝ) ≤ ((4 * ((d : ℤ) + 1) : ℤ) : ℝ) := by
        push_cast; simpa using this
      exact_mod_cast this
    rw [Finset.mem_Icc]
    have := abs_le.1 h2
    simp only [Pi.sub_apply] at this
    constructor <;> linarith [this.1, this.2]

theorem card_candidates_le (cl : GLeaf tree → (Fin d → ℤ)) (x : GBranch tree → (Fin d → ℤ))
    (b : GBranch tree) : (candidates cl x b).card ≤ nodeBallCard d := by
  classical
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Fintype.card_piFinset]
  simp only [Int.card_Icc]
  unfold nodeBallCard
  have h1 : ∀ i : Fin d, (childCombo cl x b i + 4 * ((d : ℤ) + 1) + 1 -
      (childCombo cl x b i - 4 * ((d : ℤ) + 1))).toNat = 2 * (4 * (d + 1)) + 1 := fun i => by omega
  simp only [h1]
  simp

end WaveTurbulence.RepAnalytic
