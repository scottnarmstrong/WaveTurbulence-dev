/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Frozen.Defs.Mom
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Summing a series absolutely in every Schwartz seminorm

The smooth function and its decay are constructed from actual scalar and
derivative series. No completeness instance for Schwartz space is assumed.
-/

public section

noncomputable section

open scoped SchwartzMap ContDiff

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- The actual pointwise scalar series. -/
@[expose] def schwartzSeriesFunction (F : ℕ → 𝓢(Mom d, ℝ)) (k : Mom d) : ℝ := ∑' j, F j k

variable {F : ℕ → 𝓢(Mom d, ℝ)}

/-- Absolute seminorm summability gives a smooth scalar sum. -/
theorem contDiff_schwartzSeriesFunction
    (hF : ∀ q n : ℕ, Summable (fun j => SchwartzMap.seminorm ℝ q n (F j))) :
    ContDiff ℝ ∞ (schwartzSeriesFunction F) := by
  exact contDiff_tsum (N := (⊤ : ℕ∞)) (f := fun j => ⇑(F j))
    (v := fun n j => SchwartzMap.seminorm ℝ 0 n (F j))
    (fun j => (F j).smooth ⊤) (fun n _ => hF 0 n)
    (fun n j k _ => SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ (F j) n k)

/-- Every Fréchet derivative is the actual sum of the corresponding derivative series. -/
theorem iteratedFDeriv_schwartzSeriesFunction
    (hF : ∀ q n : ℕ, Summable (fun j => SchwartzMap.seminorm ℝ q n (F j))) (n : ℕ) (k : Mom d) :
    iteratedFDeriv ℝ n (schwartzSeriesFunction F) k = ∑' j, iteratedFDeriv ℝ n (F j) k := by
  exact iteratedFDeriv_tsum_apply (N := (⊤ : ℕ∞)) (f := fun j => ⇑(F j))
    (v := fun n j => SchwartzMap.seminorm ℝ 0 n (F j))
    (fun j => (F j).smooth ⊤) (fun n _ => hF 0 n)
    (fun n j k _ => SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ (F j) n k) le_top k

/-- Weighted derivative bounds of the sum follow from the actual seminorm sums. -/
theorem norm_pow_iteratedFDeriv_schwartzSeriesFunction_le
    (hF : ∀ q n : ℕ, Summable (fun j => SchwartzMap.seminorm ℝ q n (F j)))
    (q n : ℕ) (k : Mom d) :
    ‖k‖ ^ q * ‖iteratedFDeriv ℝ n (schwartzSeriesFunction F) k‖ ≤
      ∑' j, SchwartzMap.seminorm ℝ q n (F j) := by
  have hn : Summable (fun j => ‖iteratedFDeriv ℝ n (F j) k‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun j => SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ (F j) n k) (hF 0 n)
  rw [iteratedFDeriv_schwartzSeriesFunction hF n k]
  calc
    _ ≤ ‖k‖ ^ q * ∑' j, ‖iteratedFDeriv ℝ n (F j) k‖ :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hn) (by positivity)
    _ = ∑' j, ‖k‖ ^ q * ‖iteratedFDeriv ℝ n (F j) k‖ := tsum_mul_left.symm
    _ ≤ _ := (hn.mul_left _).tsum_le_tsum
      (fun j => SchwartzMap.le_seminorm ℝ q n (F j) k) (hF q n)

/-- The seminorm-absolutely-convergent scalar sum is an actual Schwartz function. -/
@[expose] def schwartzSeries (F : ℕ → 𝓢(Mom d, ℝ))
    (hF : ∀ q n : ℕ, Summable (fun j => SchwartzMap.seminorm ℝ q n (F j))) : 𝓢(Mom d, ℝ) where
  toFun := schwartzSeriesFunction F
  smooth' := contDiff_schwartzSeriesFunction hF
  decay' q n := ⟨_, norm_pow_iteratedFDeriv_schwartzSeriesFunction_le hF q n⟩

theorem schwartzSeries_apply
    (hF : ∀ q n : ℕ, Summable (fun j => SchwartzMap.seminorm ℝ q n (F j))) (k : Mom d) :
    schwartzSeries F hF k = ∑' j, F j k := rfl

/-- The exact Schwartz seminorm is bounded by the corresponding seminorm sum. -/
theorem seminorm_schwartzSeries_le
    (hF : ∀ q n : ℕ, Summable (fun j => SchwartzMap.seminorm ℝ q n (F j))) (q n : ℕ) :
    SchwartzMap.seminorm ℝ q n (schwartzSeries F hF) ≤ ∑' j, SchwartzMap.seminorm ℝ q n (F j) := by
  apply SchwartzMap.seminorm_le_bound ℝ q n _
    (tsum_nonneg fun j => apply_nonneg (SchwartzMap.seminorm ℝ q n) (F j))
  exact norm_pow_iteratedFDeriv_schwartzSeriesFunction_le hF q n

end WaveTurbulence.WKEL2
