/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamPhysicalChartSupport
import Mathlib.Tactic

/-! # Every concrete source cap supports its normalized physical chart -/

public section
namespace WaveTurbulence.Vine.Param.NormalizedVineCertificate
open Finset
variable {X : VineType} (C : NormalizedVineCertificate X)

/-- The pinned natural-number source cap on the exact finite atom carrier. -/
@[expose] def physicalCap (s : Fin X.template.slots.length) : Finset (Fin (C.shape.n+1)) :=
  univ.filter (fun v => v.1 ∈ slotCap X s)

/-- The finite source support certificate supplies all-cap support of the
constructed physical chart, rather than an assumed analytic property. -/
theorem physicalChart_capSupported {p : Fin (baseProfileCount X)}
    (H : NormalizedBaseSupport p C) (s : Fin X.template.slots.length) :
    C.physicalChart.CapSupported (C.physicalCap s) := by
  intro i
  simpa only [physicalChart,physicalCap,mem_filter,mem_univ,true_and] using H.difference_support i s

end WaveTurbulence.Vine.Param.NormalizedVineCertificate
