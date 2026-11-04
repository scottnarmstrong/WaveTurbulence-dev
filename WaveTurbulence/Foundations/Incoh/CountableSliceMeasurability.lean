/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-! # Strong measurability of continuous spectral slices over countably many cells -/

public section
open MeasureTheory Set TopologicalSpace

namespace WaveTurbulence.Incoh

/-- Countably many continuous spectral slices have a measurable, separable joint image. No
second-countability assumption is imposed on the derivative operator's target space. -/
theorem stronglyMeasurable_countable_slices {U V W : Type*}
    [Countable U] [MeasurableSpace U] [MeasurableSingletonClass U]
    [MeasurableSpace V] [TopologicalSpace V] [SecondCountableTopology V] [OpensMeasurableSpace V]
    [TopologicalSpace W] [PseudoMetrizableSpace W]
    (f : U → V → W) (hf : ∀ u, Continuous (f u)) :
    StronglyMeasurable (Function.uncurry f) := by
  borelize W
  apply stronglyMeasurable_iff_measurable_separable.mpr
  refine ⟨measurable_from_prod_countable_right (fun u => (hf u).measurable), ?_⟩
  have hs : IsSeparable (⋃ u : U, range (f u)) := IsSeparable.iUnion (fun u => isSeparable_range (hf u))
  apply hs.mono
  rintro _ ⟨⟨u, v⟩, rfl⟩
  exact mem_iUnion.mpr ⟨u, mem_range_self v⟩

end WaveTurbulence.Incoh
