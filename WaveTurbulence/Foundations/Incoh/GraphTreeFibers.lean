/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.GraphClockBounds

/-! # Rectangular clock fibers computed from a finite source parent-child graph -/

public section
noncomputable section
open scoped Classical
open MeasureTheory Set
namespace WaveTurbulence.Incoh

/-- The remaining clocks obey their actual layers and all remaining parent-child edges. -/
@[expose] def graphRemainingDomain {d n r : ℕ} (R : RootCoordinates n r)
    (Q : Fin n → LayerLink d) (E : Finset ((Fin n × Fin 2) × (Fin n × Fin 2))) :
    Set (Fin R.restCount → ℝ) :=
  {u | (∀ k, (vertexLayer Q (R.restVertex k) : ℝ) < u k ∧
      u k ≤ (vertexLayer Q (R.restVertex k) : ℝ) + 1) ∧
    ∀ i j, (R.restVertex i, R.restVertex j) ∈ E → u i < u j}

theorem measurableSet_graphRemainingDomain {d n r : ℕ} (R : RootCoordinates n r)
    (Q : Fin n → LayerLink d) (E : Finset ((Fin n × Fin 2) × (Fin n × Fin 2))) :
    MeasurableSet (graphRemainingDomain R Q E) := by
  unfold graphRemainingDomain
  measurability

/-- All fields of the rectangular-fiber carrier are constructed from actual finite graph data.
The selected-clock ordering is imposed by `timeDomain`, not assumed in any field. -/
@[expose] def graphTreeFibers {d n m : ℕ} (S : SelectedLinkClocks n (m + 2))
    (Q : Fin n → LayerLink d) (E : Finset ((Fin n × Fin 2) × (Fin n × Fin 2))) :
    TreeClockFibers m Q where
  selection := S
  remainingDomain := graphRemainingDomain S.coordinates Q E
  measurable_remainingDomain := measurableSet_graphRemainingDomain S.coordinates Q E
  lower u j := graphLower S.coordinates Q E j u
  upper u j := graphUpper S.coordinates Q E j u
  measurable_lower := Measurable.of_eval fun j => measurable_graphLower S.coordinates Q E j
  measurable_upper := Measurable.of_eval fun j => measurable_graphUpper S.coordinates Q E j
  lower_le_upper u j := graphLower_le_upper S.coordinates Q E j u
  remaining_mem_box := by
    intro u hu
    exact ⟨fun k => (hu.1 k).1.le, fun k => (hu.1 k).2⟩
  interval_mem_box := by
    intro u _ v hv
    constructor
    · intro j
      have h := (graph_interval_iff S.coordinates Q E j u (v j)).mp (hv j)
      exact ((graphRawLower_lt_iff S.coordinates Q E j u (v j)).mp h.1).1.le
    · intro j
      have h := (graph_interval_iff S.coordinates Q E j u (v j)).mp (hv j)
      exact ((le_graphUpper_iff S.coordinates Q E j u (v j)).mp h.2).1

end WaveTurbulence.Incoh
