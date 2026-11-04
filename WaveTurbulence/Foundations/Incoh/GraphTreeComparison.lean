/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.GraphTreeDomain
public import Mathlib.Order.Fin.Basic

/-! # Comparing the graph fibers with literal strict source clock constraints -/

public section
noncomputable section
open scoped Classical
namespace WaveTurbulence.Incoh

/-- Literal source graph constraints, with only upper layer boundaries closed. -/
@[expose] def graphStrictDomain {d n : ℕ} (Q : Fin n → LayerLink d)
    (E : Finset ((Fin n × Fin 2) × (Fin n × Fin 2))) : Set (Fin n → Fin 2 → ℝ) :=
  {t | (∀ v : Fin n × Fin 2, (vertexLayer Q v : ℝ) < t v.1 v.2 ∧
    t v.1 v.2 ≤ (vertexLayer Q v : ℝ) + 1) ∧
    ∀ v w, (v, w) ∈ E → t v.1 v.2 < t w.1 w.2}

/-- Strict graph constraints imply the computed intervals whenever the selected clocks are ordered. -/
theorem mem_graphTreeFibers_of_strict_and_ordered {d n m : ℕ}
    (S : SelectedLinkClocks n (m + 2)) (Q : Fin n → LayerLink d)
    (E : Finset ((Fin n × Fin 2) × (Fin n × Fin 2)))
    {t : Fin n → Fin 2 → ℝ} (ht : t ∈ graphStrictDomain Q E)
    (ho : ∀ j : Fin (m + 1),
      t (S.coordinates.rootVertex j.succ).1 (S.coordinates.rootVertex j.succ).2 <
      t (S.coordinates.rootVertex j.castSucc).1 (S.coordinates.rootVertex j.castSucc).2) :
    t ∈ (graphTreeFibers S Q E).timeDomain := by
  rw [mem_graphTreeFibers_timeDomain_iff]
  exact ⟨ht.1, fun i j h => ht.2 _ _ h, fun j k h => ht.2 _ _ h,
    fun j k h => (ht.2 _ _ h).le, ho⟩

/-- Computed intervals imply strict graph constraints away from coordinate equality hyperplanes.
The only structural hypothesis orders edges joining two selected source vertices. -/
theorem mem_graphStrictDomain_of_fibers {d n m : ℕ}
    (S : SelectedLinkClocks n (m + 2)) (Q : Fin n → LayerLink d)
    (E : Finset ((Fin n × Fin 2) × (Fin n × Fin 2)))
    (hedge : ∀ i j, (S.coordinates.rootVertex i, S.coordinates.rootVertex j) ∈ E → j < i)
    {t : Fin n → Fin 2 → ℝ}
    (hne : ∀ v w, (v, w) ∈ E → t v.1 v.2 ≠ t w.1 w.2)
    (ht : t ∈ (graphTreeFibers S Q E).timeDomain) : t ∈ graphStrictDomain Q E := by
  obtain ⟨hl, hr, hc, hp, ho⟩ := (mem_graphTreeFibers_timeDomain_iff S Q E t).mp ht
  refine ⟨hl, ?_⟩
  intro v w he
  rcases S.coordinates.vertex_cases v with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    rcases S.coordinates.vertex_cases w with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have ha : StrictAnti (fun j => t (S.coordinates.rootVertex j).1
        (S.coordinates.rootVertex j).2) := Fin.strictAnti_iff_succ_lt.mpr ho
    exact ha (hedge i j he)
  · exact lt_of_le_of_ne (hp i j he) (hne _ _ he)
  · exact hc j i he
  · exact hr i j he

end WaveTurbulence.Incoh
