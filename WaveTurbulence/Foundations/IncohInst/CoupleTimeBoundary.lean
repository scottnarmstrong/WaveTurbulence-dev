/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.InternalTimeDomain
public import WaveTurbulence.Foundations.IncohInst.CoupleRootClocks
public import Mathlib.MeasureTheory.Constructions.Pi

/-! # The original strict couple time cuts equal the closed analytic root cuts almost everywhere -/

public section
noncomputable section
open MeasureTheory Set
namespace WaveTurbulence.IncohInst

/-- The literal source upper-time constraints reduce to the two source root cuts.
Only the two null external root hyperplanes are discarded. -/
theorem couple_kDomain_ae_rootCut (LG : LayeredGarden 2)
    (hb : ∀ i, ([] : TTree.Path) ∈ (LG.garden.tree i).branching) (ts : Fin 2 → ℝ) :
    kDomain LG (fun b => ts b.1.1) 0 =ᵐ[volume]
      internalTimeDomain LG ∩ {τ | ∀ i : Fin 2, τ ⟨(i, []), hb i⟩ ≤ ts i} := by
  have hne : ∀ᵐ τ : GBranch LG.garden.tree → ℝ,
      ∀ i : Fin 2, τ ⟨(i, []), hb i⟩ ≠ ts i := by
    apply ae_all_iff.mpr
    intro i
    exact Measure.ae_eval_ne (fun _ : GBranch LG.garden.tree => (volume : Measure ℝ)) ⟨(i, []), hb i⟩ (ts i)
  filter_upwards [hne] with τ hne
  apply propext
  rw [mem_kDomain_iff]
  constructor
  · rintro ⟨hi, hu, _⟩
    exact ⟨hi, fun i => (hu ⟨(i, []), hb i⟩).le⟩
  · rintro ⟨hi, hr⟩
    refine ⟨hi, ?_, fun b _ => (hi b).2.2.1⟩
    apply internalTimeDomain_branch_upper LG hi ts
    intro b
    have he : branchRoot b = (⟨(b.1.1, []), hb b.1.1⟩ : GBranch LG.garden.tree) := Subtype.ext rfl
    rw [he]
    exact lt_of_le_of_ne (hr b.1.1) (hne b.1.1)

end WaveTurbulence.IncohInst
