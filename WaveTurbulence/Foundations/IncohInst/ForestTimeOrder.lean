/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.TreeTimeOrder
public import WaveTurbulence.Foundations.WaveB.FrozenB1

/-! # The source parent-child clock constraints bound every node by its actual root clock -/

public section
noncomputable section
open scoped Classical
namespace WaveTurbulence.IncohInst

/-- The root above an existing source branching node is itself branching. -/
@[expose] def branchRoot {w : ℕ} {tree : Fin w → TTree} (b : GBranch tree) : GBranch tree :=
  ⟨(b.1.1, []), root_mem_branching_of_mem b.2⟩

/-- Read a branching clock at an address, extending by zero outside its actual branching set. -/
@[expose] def branchClockAt {w : ℕ} {tree : Fin w → TTree} (τ : GBranch tree → ℝ)
    (i : Fin w) (p : TTree.Path) : ℝ :=
  if hp : p ∈ (tree i).branching then τ ⟨(i, p), hp⟩ else 0

@[simp] theorem branchClockAt_branch {w : ℕ} {tree : Fin w → TTree} (τ : GBranch tree → ℝ)
    (b : GBranch tree) : branchClockAt τ b.1.1 b.1.2 = τ b := by
  rcases b with ⟨⟨i, p⟩, hp⟩
  simp only [branchClockAt, dite_eq_left hp]

/-- Every source branching clock is bounded by its source root, solely from parent-child order. -/
theorem branch_time_le_root {w : ℕ} {tree : Fin w → TTree} (τ : GBranch tree → ℝ)
    (h : ∀ b b' : GBranch tree, b'.IsChildOf b → τ b' < τ b) (b : GBranch tree) :
    τ b ≤ τ (branchRoot b) := by
  have ho : TimeOrdered (tree b.1.1) (branchClockAt τ b.1.1) := by
    intro p hp j hj
    have hc := h (⟨(b.1.1, p), hp⟩ : GBranch tree) ⟨(b.1.1, p ++ [j]), hj⟩ ⟨rfl, j, rfl⟩
    simpa only [branchClockAt, dite_eq_left hp, dite_eq_left hj] using hc
  have he := time_le_root_of_ordered (tree b.1.1) (branchClockAt τ b.1.1) ho b.1.2 b.2
  have hr : branchClockAt τ b.1.1 [] = τ (branchRoot b) :=
    branchClockAt_branch τ (branchRoot b)
  rwa [branchClockAt_branch, hr] at he

end WaveTurbulence.IncohInst
