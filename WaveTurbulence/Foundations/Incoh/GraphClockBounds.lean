/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.TreeClockFibers
public import Mathlib.MeasureTheory.Order.Lattice

/-! # Actual finite interval bounds induced by the source parent-child graph -/

public section
noncomputable section
open scoped Classical
open MeasureTheory

namespace WaveTurbulence.Incoh

/-- The actual original vertex of a remaining clock. -/
@[expose] def RootCoordinates.restVertex {n r : ℕ} (R : RootCoordinates n r)
    (k : Fin R.restCount) : Fin n × Fin 2 :=
  finProdFinEquiv.symm (R.permutation.symm (Sum.inr k))

/-- A source child clock supplies a lower bound; the dummy entry retains the source layer. -/
@[expose] def graphLowerCandidate {d n r : ℕ} (R : RootCoordinates n r)
    (Q : Fin n → LayerLink d) (E : Finset ((Fin n × Fin 2) × (Fin n × Fin 2)))
    (j : Fin r) (o : Option (Fin R.restCount)) : (Fin R.restCount → ℝ) → ℝ :=
  match o with
  | none => fun _ => (vertexLayer Q (R.rootVertex j) : ℝ)
  | some k => if (R.restVertex k, R.rootVertex j) ∈ E then fun u => u k
    else fun _ => (vertexLayer Q (R.rootVertex j) : ℝ)

/-- A source parent clock supplies an upper bound; the dummy entry retains the source layer. -/
@[expose] def graphUpperCandidate {d n r : ℕ} (R : RootCoordinates n r)
    (Q : Fin n → LayerLink d) (E : Finset ((Fin n × Fin 2) × (Fin n × Fin 2)))
    (j : Fin r) (o : Option (Fin R.restCount)) : (Fin R.restCount → ℝ) → ℝ :=
  match o with
  | none => fun _ => (vertexLayer Q (R.rootVertex j) : ℝ) + 1
  | some k => if (R.rootVertex j, R.restVertex k) ∈ E then fun u => u k
    else fun _ => (vertexLayer Q (R.rootVertex j) : ℝ) + 1

/-- The actual maximum of the finite lower clock constraints. -/
@[expose] def graphRawLower {d n r : ℕ} (R : RootCoordinates n r)
    (Q : Fin n → LayerLink d) (E : Finset ((Fin n × Fin 2) × (Fin n × Fin 2)))
    (j : Fin r) : (Fin R.restCount → ℝ) → ℝ :=
  Finset.univ.sup' ⟨none, Finset.mem_univ _⟩ (graphLowerCandidate R Q E j)

/-- The actual minimum of the finite upper clock constraints. -/
@[expose] def graphUpper {d n r : ℕ} (R : RootCoordinates n r)
    (Q : Fin n → LayerLink d) (E : Finset ((Fin n × Fin 2) × (Fin n × Fin 2)))
    (j : Fin r) : (Fin R.restCount → ℝ) → ℝ :=
  Finset.univ.inf' ⟨none, Finset.mem_univ _⟩ (graphUpperCandidate R Q E j)

/-- Clamp inconsistent lower bounds to the upper bound; the resulting half-open interval is
empty exactly when the original source interval is empty. -/
@[expose] def graphLower {d n r : ℕ} (R : RootCoordinates n r)
    (Q : Fin n → LayerLink d) (E : Finset ((Fin n × Fin 2) × (Fin n × Fin 2)))
    (j : Fin r) (u : Fin R.restCount → ℝ) : ℝ := min (graphRawLower R Q E j u) (graphUpper R Q E j u)

theorem measurable_graphRawLower {d n r : ℕ} (R : RootCoordinates n r)
    (Q : Fin n → LayerLink d) (E : Finset ((Fin n × Fin 2) × (Fin n × Fin 2))) (j : Fin r) :
    Measurable (graphRawLower R Q E j) := by
  apply Finset.measurable_sup'
  intro o _
  cases o with
  | none => exact measurable_const
  | some k =>
    dsimp only [graphLowerCandidate]
    split_ifs
    · exact measurable_pi_apply k
    · exact measurable_const

theorem measurable_graphUpper {d n r : ℕ} (R : RootCoordinates n r)
    (Q : Fin n → LayerLink d) (E : Finset ((Fin n × Fin 2) × (Fin n × Fin 2))) (j : Fin r) :
    Measurable (graphUpper R Q E j) := by
  apply (Finset.measurable_sup' (α := OrderDual ℝ) ⟨none, Finset.mem_univ _⟩)
  intro o _
  cases o with
  | none => exact measurable_const
  | some k =>
    dsimp only [graphUpperCandidate]
    split_ifs
    · exact measurable_pi_apply k
    · exact measurable_const

theorem measurable_graphLower {d n r : ℕ} (R : RootCoordinates n r)
    (Q : Fin n → LayerLink d) (E : Finset ((Fin n × Fin 2) × (Fin n × Fin 2))) (j : Fin r) :
    Measurable (graphLower R Q E j) :=
  (measurable_graphRawLower R Q E j).min (measurable_graphUpper R Q E j)

theorem graphLower_le_upper {d n r : ℕ} (R : RootCoordinates n r)
    (Q : Fin n → LayerLink d) (E : Finset ((Fin n × Fin 2) × (Fin n × Fin 2))) (j : Fin r)
    (u : Fin R.restCount → ℝ) : graphLower R Q E j u ≤ graphUpper R Q E j u := min_le_right _ _

/-- The finite lower bound is exactly the source layer and all remaining child clocks. -/
theorem graphRawLower_lt_iff {d n r : ℕ} (R : RootCoordinates n r)
    (Q : Fin n → LayerLink d) (E : Finset ((Fin n × Fin 2) × (Fin n × Fin 2)))
    (j : Fin r) (u : Fin R.restCount → ℝ) (x : ℝ) :
    graphRawLower R Q E j u < x ↔
      (vertexLayer Q (R.rootVertex j) : ℝ) < x ∧
      ∀ k, (R.restVertex k, R.rootVertex j) ∈ E → u k < x := by
  change (Finset.univ.sup' (show Finset.univ.Nonempty from ⟨none, Finset.mem_univ _⟩)
    (graphLowerCandidate R Q E j)) u < x ↔ _
  rw [Finset.sup'_apply, Finset.sup'_lt_iff]
  constructor
  · intro h
    refine ⟨h none (Finset.mem_univ _), ?_⟩
    intro k hk
    simpa only [graphLowerCandidate, ite_eq_left hk] using h (some k) (Finset.mem_univ _)
  · rintro ⟨hl, hc⟩ o _
    cases o with
    | none => exact hl
    | some k =>
      dsimp only [graphLowerCandidate]
      split_ifs with hk
      · exact hc k hk
      · exact hl

/-- The finite upper bound is exactly the source layer and all remaining parent clocks. -/
theorem le_graphUpper_iff {d n r : ℕ} (R : RootCoordinates n r)
    (Q : Fin n → LayerLink d) (E : Finset ((Fin n × Fin 2) × (Fin n × Fin 2)))
    (j : Fin r) (u : Fin R.restCount → ℝ) (x : ℝ) :
    x ≤ graphUpper R Q E j u ↔
      x ≤ (vertexLayer Q (R.rootVertex j) : ℝ) + 1 ∧
      ∀ k, (R.rootVertex j, R.restVertex k) ∈ E → x ≤ u k := by
  change x ≤ (Finset.univ.inf' (show Finset.univ.Nonempty from ⟨none, Finset.mem_univ _⟩)
    (graphUpperCandidate R Q E j)) u ↔ _
  rw [Finset.inf'_apply, Finset.le_inf'_iff]
  constructor
  · intro h
    refine ⟨h none (Finset.mem_univ _), ?_⟩
    intro k hk
    simpa only [graphUpperCandidate, ite_eq_left hk] using h (some k) (Finset.mem_univ _)
  · rintro ⟨hl, hc⟩ o _
    cases o with
    | none => exact hl
    | some k =>
      dsimp only [graphUpperCandidate]
      split_ifs with hk
      · exact hc k hk
      · exact hl

/-- Clamping preserves the half-open interval, including inconsistent source constraints. -/
theorem graph_interval_iff {d n r : ℕ} (R : RootCoordinates n r)
    (Q : Fin n → LayerLink d) (E : Finset ((Fin n × Fin 2) × (Fin n × Fin 2)))
    (j : Fin r) (u : Fin R.restCount → ℝ) (x : ℝ) :
    (graphLower R Q E j u < x ∧ x ≤ graphUpper R Q E j u) ↔
      (graphRawLower R Q E j u < x ∧ x ≤ graphUpper R Q E j u) := by
  unfold graphLower
  constructor
  · rintro ⟨hl, hu⟩
    exact ⟨(min_lt_iff.mp hl).resolve_right (not_lt.mpr hu), hu⟩
  · rintro ⟨hl, hu⟩
    exact ⟨lt_of_le_of_lt (min_le_left _ _) hl, hu⟩

end WaveTurbulence.Incoh
