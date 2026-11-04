/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.GraphTreeFibers
public import WaveTurbulence.Foundations.Incoh.GraphClockCoordinates

/-! # The literal graph constraints of the constructed tree fibers -/

public section
noncomputable section
open scoped Classical
namespace WaveTurbulence.Incoh

/-- Fiber membership reads exactly the actual layer, remaining-edge and mixed-edge constraints.
Only selected-to-remaining parent constraints have closed endpoints. -/
theorem mem_graphTreeFibers_timeDomain_iff {d n m : ℕ} (S : SelectedLinkClocks n (m + 2))
    (Q : Fin n → LayerLink d) (E : Finset ((Fin n × Fin 2) × (Fin n × Fin 2)))
    (t : Fin n → Fin 2 → ℝ) :
    t ∈ (graphTreeFibers S Q E).timeDomain ↔
      (∀ v : Fin n × Fin 2, (vertexLayer Q v : ℝ) < t v.1 v.2 ∧
        t v.1 v.2 ≤ (vertexLayer Q v : ℝ) + 1) ∧
      (∀ i j, (S.coordinates.restVertex i, S.coordinates.restVertex j) ∈ E →
        t (S.coordinates.restVertex i).1 (S.coordinates.restVertex i).2 <
        t (S.coordinates.restVertex j).1 (S.coordinates.restVertex j).2) ∧
      (∀ j k, (S.coordinates.restVertex k, S.coordinates.rootVertex j) ∈ E →
        t (S.coordinates.restVertex k).1 (S.coordinates.restVertex k).2 <
        t (S.coordinates.rootVertex j).1 (S.coordinates.rootVertex j).2) ∧
      (∀ j k, (S.coordinates.rootVertex j, S.coordinates.restVertex k) ∈ E →
        t (S.coordinates.rootVertex j).1 (S.coordinates.rootVertex j).2 ≤
        t (S.coordinates.restVertex k).1 (S.coordinates.restVertex k).2) ∧
      (∀ j : Fin (m + 1),
        t (S.coordinates.rootVertex j.succ).1 (S.coordinates.rootVertex j.succ).2 <
        t (S.coordinates.rootVertex j.castSucc).1 (S.coordinates.rootVertex j.castSucc).2) := by
  change ((∀ k, (vertexLayer Q (S.coordinates.restVertex k) : ℝ) < (S.coordinates.equiv t).2 k ∧
      (S.coordinates.equiv t).2 k ≤ (vertexLayer Q (S.coordinates.restVertex k) : ℝ) + 1) ∧
    (∀ i j, (S.coordinates.restVertex i, S.coordinates.restVertex j) ∈ E →
      (S.coordinates.equiv t).2 i < (S.coordinates.equiv t).2 j)) ∧
    (∀ j, graphLower S.coordinates Q E j (S.coordinates.equiv t).2 < (S.coordinates.equiv t).1 j ∧
      (S.coordinates.equiv t).1 j ≤ graphUpper S.coordinates Q E j (S.coordinates.equiv t).2) ∧
    (∀ j : Fin (m + 1), (S.coordinates.equiv t).1 j.succ < (S.coordinates.equiv t).1 j.castSucc) ↔ _
  simp only [graph_interval_iff]
  simp only [graphRawLower_lt_iff, le_graphUpper_iff,
    RootCoordinates.equiv_rootVertex, RootCoordinates.equiv_restVertex]
  constructor
  · rintro ⟨⟨hr, he⟩, hs, ho⟩
    refine ⟨?_, he, ?_, ?_, ho⟩
    · intro v
      rcases S.coordinates.vertex_cases v with ⟨j, rfl⟩ | ⟨k, rfl⟩
      · exact ⟨(hs j).1.1, (hs j).2.1⟩
      · exact hr k
    · intro j k hk
      exact (hs j).1.2 k hk
    · intro j k hk
      exact (hs j).2.2 k hk
  · rintro ⟨hl, he, hc, hp, ho⟩
    refine ⟨⟨fun k => hl _, he⟩, ?_, ho⟩
    intro j
    exact ⟨⟨(hl _).1, hc j⟩, (hl _).2, hp j⟩

end WaveTurbulence.Incoh
