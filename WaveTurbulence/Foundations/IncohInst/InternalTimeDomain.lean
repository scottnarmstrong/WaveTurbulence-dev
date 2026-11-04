/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.ForestTimeOrder
public import WaveTurbulence.Foundations.IncohInst.SourceTimeMeasurability

/-! # The exact external-time-independent source domain -/

public section
namespace WaveTurbulence.IncohInst
open MeasureTheory Set

/-- The literal source layer and branching-order constraints, before external root cuts. -/
@[expose] def internalTimeDomain {w : ℕ} (LG : LayeredGarden w) : Set (GBranch LG.garden.tree → ℝ) :=
  {τ | ∀ b, (LG.layer b.toNode : ℝ) < τ b ∧ τ b < LG.layer b.toNode + 1 ∧ 0 < τ b ∧
    ∀ b' : GBranch LG.garden.tree, b'.IsChildOf b → τ b' < τ b}

/-- The actual internal constraints are measurable. -/
theorem measurableSet_internalTimeDomain {w : ℕ} (LG : LayeredGarden w) :
    MeasurableSet (internalTimeDomain LG) := by
  classical
  unfold internalTimeDomain
  measurability

/-- Forgetting only the external clock constraints leaves precisely the internal domain. -/
theorem mem_kDomain_iff {w : ℕ} (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ)
    (s : ℝ) (τ : GBranch LG.garden.tree → ℝ) :
    τ ∈ kDomain LG up s ↔ τ ∈ internalTimeDomain LG ∧
      (∀ b, τ b < up b) ∧ (∀ b, LG.garden.IsLoneParent b → s < τ b) := by
  constructor
  · intro h
    exact ⟨fun b => ⟨(h b).1, (h b).2.1, (h b).2.2.1, (h b).2.2.2.2.1⟩,
      fun b => (h b).2.2.2.1, fun b => (h b).2.2.2.2.2⟩
  · rintro ⟨h, hu, hl⟩ b
    exact ⟨(h b).1, (h b).2.1, (h b).2.2.1, hu b, (h b).2.2.2, hl b⟩

/-- The actual root upper bounds imply every branch upper bound; no extra time inequality
is required from the source carrier. -/
theorem internalTimeDomain_branch_upper {w : ℕ} (LG : LayeredGarden w)
    {τ : GBranch LG.garden.tree → ℝ} (hτ : τ ∈ internalTimeDomain LG)
    (up : Fin w → ℝ)
    (hroot : ∀ b : GBranch LG.garden.tree, τ (branchRoot b) < up b.1.1) :
    ∀ b : GBranch LG.garden.tree, τ b < up b.1.1 := by
  intro b
  exact (branch_time_le_root τ (fun b b' hb => (hτ b).2.2.2 b' hb) b).trans_lt (hroot b)

end WaveTurbulence.IncohInst
