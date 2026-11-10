/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.MeasureTheory.Integral.Pi
/-! Finite dependent time arrays curry by a volume-preserving equivalence. -/
@[expose] public section
namespace WaveTurbulence.Induct
open MeasureTheory Finset

noncomputable def finiteTimeCurry {ι : Type*} [Fintype ι] (β : ι → Type*) [∀ i, Fintype (β i)] :
    ((Σ i, β i) → ℝ) ≃ᵐ ((i : ι) → β i → ℝ) :=
  MeasurableEquiv.piCurry (fun i (_ : β i) => ℝ)

theorem measurePreserving_finiteTimeCurry {ι : Type*} [Fintype ι] (β : ι → Type*) [∀ i, Fintype (β i)] :
    MeasurePreserving (finiteTimeCurry β) volume volume := by
  let e := finiteTimeCurry β
  apply MeasurePreserving.symm e.symm
  refine ⟨e.symm.measurable, (Measure.pi_eq fun s hs => ?_).symm⟩
  have hpre : e.symm ⁻¹' Set.univ.pi s = Set.univ.pi (fun i => Set.univ.pi (fun b : β i => s ⟨i, b⟩)) := by
    ext τ
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const]
    exact ⟨fun h i b => h ⟨i, b⟩, fun h ⟨i, b⟩ => h i b⟩
  rw [e.symm.map_apply, hpre, volume_pi_pi]
  simp_rw [volume_pi_pi]
  rw [Fintype.prod_sigma]

end WaveTurbulence.Induct
