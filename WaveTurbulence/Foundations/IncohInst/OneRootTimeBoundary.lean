/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.InternalTimeDomain
public import Mathlib.MeasureTheory.Constructions.Pi

/-! # Exact source time-domain reduction for one-trivial-tree couples -/

public section
noncomputable section
open MeasureTheory Set
namespace WaveTurbulence.IncohInst

/-- If only one source tree has branching nodes, exactly its single root clock is cut by
external time. The other external clock remains passive. -/
theorem couple_kDomain_ae_oneRootCut (LG : LayeredGarden 2) (a : Fin 2)
    (hb : ([] : TTree.Path) ∈ (LG.garden.tree a).branching)
    (hwidth : ∀ b : GBranch LG.garden.tree, b.1.1 = a) (ts : Fin 2 → ℝ) :
    kDomain LG (fun b => ts b.1.1) 0 =ᵐ[volume]
      internalTimeDomain LG ∩ {τ | τ ⟨(a, []), hb⟩ ≤ ts a} := by
  have hne : ∀ᵐ τ : GBranch LG.garden.tree → ℝ, τ ⟨(a, []), hb⟩ ≠ ts a :=
    Measure.ae_eval_ne (fun _ : GBranch LG.garden.tree => (volume : Measure ℝ)) ⟨(a, []), hb⟩ (ts a)
  filter_upwards [hne] with τ hne
  apply propext
  rw [mem_kDomain_iff]
  constructor
  · rintro ⟨hi, hu, _⟩
    exact ⟨hi, (hu ⟨(a, []), hb⟩).le⟩
  · rintro ⟨hi, hr⟩
    refine ⟨hi, ?_, fun b _ => (hi b).2.2.1⟩
    intro b
    have he : branchRoot b = (⟨(a, []), hb⟩ : GBranch LG.garden.tree) :=
      Subtype.ext (Prod.ext (hwidth b) rfl)
    have hh := branch_time_le_root τ (fun b b' hb => (hi b).2.2.2 b' hb) b
    rw [he] at hh
    rw [hwidth b]
    exact hh.trans_lt (lt_of_le_of_ne hr hne)

end WaveTurbulence.IncohInst
