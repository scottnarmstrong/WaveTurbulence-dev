/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Transport of spherical volume by linear isometries

Used to disintegrate the angular resonant measure over moving great spheres.
-/

public section

noncomputable section

open MeasureTheory Set Metric
open scoped Pointwise ENNReal

namespace WaveTurbulence.WKEL2

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [MeasurableSpace F] [BorelSpace E] [BorelSpace F]

/-- A linear isometric equivalence restricts to the unit spheres. -/
@[expose] def unitSphereEquiv (e : E ≃ₗᵢ[ℝ] F) : sphere (0 : E) 1 ≃ᵐ sphere (0 : F) 1 :=
  (e.toHomeomorph.subtype (fun x => by simp only [mem_sphere_zero_iff_norm, LinearIsometryEquiv.coe_toHomeomorph, e.norm_map])).toMeasurableEquiv

theorem coe_unitSphereEquiv (e : E ≃ₗᵢ[ℝ] F) (v : sphere (0 : E) 1) :
    (unitSphereEquiv e v : F) = e (v : E) := rfl

/-- Linear isometries carry radial sectors to the corresponding radial sectors. -/
theorem preimage_unitSphere_sector (e : E ≃ₗᵢ[ℝ] F) (s : Set (sphere (0 : F) 1)) :
    e ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) =
      Ioo (0 : ℝ) 1 • (Subtype.val '' ((unitSphereEquiv e) ⁻¹' s)) := by
  ext x
  constructor
  · rintro ⟨r, hr, y, ⟨v, hv, rfl⟩, he⟩
    let w := (unitSphereEquiv e).symm v
    refine ⟨r, hr, (w : E), ⟨w, ?_, rfl⟩, ?_⟩
    · change (unitSphereEquiv e) w ∈ s
      rw [(unitSphereEquiv e).apply_symm_apply]
      exact hv
    · apply e.injective
      have hmap : e (w : E) = (v : F) := by
        change ((unitSphereEquiv e) w : F) = (v : F)
        rw [(unitSphereEquiv e).apply_symm_apply]
      rw [e.map_smul, hmap]
      exact he
  · rintro ⟨r, hr, y, ⟨v, hv, rfl⟩, he⟩
    refine ⟨r, hr, ((unitSphereEquiv e) v : F), ⟨unitSphereEquiv e v, hv, rfl⟩, ?_⟩
    rw [coe_unitSphereEquiv]
    change r • e (v : E) = e x
    rw [← e.map_smul]
    exact congrArg e he

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- Canonical spherical volume is preserved by the induced unit-sphere equivalence. -/
theorem measurePreserving_unitSphereEquiv (e : E ≃ₗᵢ[ℝ] F) :
    MeasurePreserving (unitSphereEquiv e)
      (volume : Measure E).toSphere (volume : Measure F).toSphere := by
  refine ⟨(unitSphereEquiv e).measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (unitSphereEquiv e).measurable hs,
    Measure.toSphere_apply' _ ((unitSphereEquiv e).measurable hs),
    Measure.toSphere_apply' _ hs, e.toLinearEquiv.finrank_eq]
  congr 1
  have hmp : MeasurePreserving e.toMeasurableEquiv := e.measurePreserving
  have h := hmp.measure_preimage_equiv (Ioo (0 : ℝ) 1 • (Subtype.val '' s))
  simp only [LinearIsometryEquiv.coe_toMeasurableEquiv] at h
  rw [preimage_unitSphere_sector] at h
  exact h

end WaveTurbulence.WKEL2
