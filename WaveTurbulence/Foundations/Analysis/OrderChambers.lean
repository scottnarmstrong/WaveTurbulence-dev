/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.SimplexVolume
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Order chambers in a cube

The chambers cut out by distinct coordinate orderings give the
linear-extension formula for heap-ordered domains.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Analysis

/-- The recursive simplex is exactly the bounded antitone tuples. -/
theorem mem_orderedSimplex_iff : ∀ (n : ℕ) {D : ℝ} {x : Fin n → ℝ},
    x ∈ orderedSimplex n D ↔ (∀ i, x i ∈ Icc 0 D) ∧ Antitone x := by
  intro n
  induction n with
  | zero =>
      intro D x
      constructor
      · intro _
        exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
      · intro _
        trivial
  | succ n ih =>
      intro D x
      constructor
      · rintro ⟨h0, ht⟩
        obtain ⟨hb, ha⟩ := ih.mp ht
        refine ⟨?_, ?_⟩
        · intro i
          exact Fin.cases h0 (fun j => ⟨(hb j).1, (hb j).2.trans h0.2⟩) i
        · intro i j hij
          cases i using Fin.cases with
          | zero =>
              cases j using Fin.cases with
              | zero => exact le_rfl
              | succ j => exact (hb j).2
          | succ i =>
              cases j using Fin.cases with
              | zero =>
                  have hv : i.val + 1 ≤ 0 := by
                    simpa only [Fin.le_def, Fin.val_succ, Fin.val_zero] using hij
                  omega
              | succ j => exact ha (Fin.succ_le_succ_iff.mp hij)
      · rintro ⟨hb, ha⟩
        refine ⟨hb 0, ih.mpr ⟨?_, ?_⟩⟩
        · intro i
          exact ⟨(hb i.succ).1, ha (Fin.zero_le i.succ)⟩
        · intro i j hij
          exact ha (Fin.succ_le_succ_iff.mpr hij)

/-- Coordinate coincidences form a null hyperplane. -/
theorem volume_coordinate_eq_zero {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    volume {x : Fin n → ℝ | x i = x j} = 0 := by
  let l : (Fin n → ℝ) →ₗ[ℝ] ℝ := (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj j
  have hk : l.ker ≠ ⊤ := by
    intro h
    have hm : (Pi.single i (1 : ℝ)) ∈ l.ker := by rw [h]; trivial
    have hz : (1 : ℝ) = 0 := by
      simpa only [LinearMap.mem_ker, l, LinearMap.sub_apply, LinearMap.proj_apply,
        Pi.single_eq_same, Pi.single_eq_of_ne hij.symm, sub_zero] using hm
    exact one_ne_zero hz
  have hh := Measure.addHaar_submodule (volume : Measure (Fin n → ℝ)) l.ker hk
  have heq : (l.ker : Set (Fin n → ℝ)) = {x | x i = x j} := by
    ext x
    change x ∈ l.ker ↔ x i = x j
    rw [LinearMap.mem_ker]
    simp only [l, LinearMap.sub_apply, LinearMap.proj_apply, sub_eq_zero]
  rwa [heq] at hh

/-- Almost every tuple has pairwise distinct coordinates. -/
theorem ae_injective_coordinates (n : ℕ) :
    ∀ᵐ x : Fin n → ℝ ∂volume, Function.Injective x := by
  have hh : ∀ i j : Fin n, ∀ᵐ x : Fin n → ℝ ∂volume, i ≠ j → x i ≠ x j := by
    intro i j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ h => (h hij).elim
    · exact (ae_iff.mpr (by simpa only [not_not] using volume_coordinate_eq_zero hij)).mono fun _ h _ => h
  filter_upwards [Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hh i j] with x hx
  intro i j h
  by_contra hij
  exact hx i j hij h

end WaveTurbulence.Analysis
