/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Pi

/-! # Flattening finite blocks of real time coordinates preserves product volume -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open MeasureTheory

/-- Independent finite blocks of actual time coordinates have the same volume
as their flattened sigma-indexed real coordinate family. -/
theorem measurePreserving_piCurry_real {ι : Type*} [Fintype ι]
    (κ : ι → Type*) [∀ i, Fintype (κ i)] :
    MeasurePreserving (MeasurableEquiv.piCurry (fun (i : ι) (_ : κ i) => ℝ)) volume volume := by
  let e := MeasurableEquiv.piCurry (fun (i : ι) (_ : κ i) => ℝ)
  apply MeasurePreserving.symm e.symm
  refine ⟨e.symm.measurable,?_⟩
  apply (Measure.pi_eq (μ := fun _ : (Σ i, κ i) => (volume : Measure ℝ)) ?_).symm
  intro s _hs
  have hp : e.symm ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => s ⟨i,j⟩)) := by
    ext x
    change (∀ z : (Σ i, κ i), z ∈ Set.univ → x z.1 z.2 ∈ s z) ↔
      ∀ i, i ∈ Set.univ → ∀ j, j ∈ Set.univ → x i j ∈ s ⟨i,j⟩
    simp only [Set.mem_univ,forall_const]
    exact ⟨fun h i j => h ⟨i,j⟩,fun h ⟨i,j⟩ => h i j⟩
  rw [e.symm.map_apply,hp,volume_pi_pi]
  simp_rw [volume_pi_pi]
  exact (Fintype.prod_sigma (fun z : (Σ i, κ i) => (volume : Measure ℝ) (s z))).symm

end WaveTurbulence.RegRed
