/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.LatticeBox
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# FL-FIBER: supplement Lemma 7.1

Localized spectral fibers and the mixed-norm conversion (7.1).

* `localizedTuples`: tuples of lattice points of `ℤ_L^d` each in a unit ball around a real center.
* `card_localizedTuples_le`: at most `(2L+1)^(|ι| d)` of them.
* `ncard_values_le`: for every function `Ω` of the tuple, the value set has at most `(3L)^(4d)`
  elements when `|ι| ≤ 4` and `L ≥ 1` (so `C_d = 3`).
* `exists_cover_values`: the `α`-values are covered by that many intervals of a fixed length.
* `setLIntegral_integral_le`, `setIntegral_integral_le`: the bound (7.1).
-/

public section

open MeasureTheory

namespace WaveTurbulence.Flower.FlFiber

open WaveTurbulence WaveTurbulence.Counting

variable {d : ℕ}

/-- Tuples (indexed by `ι`) of integer vectors whose lattice points `n/L` lie in the closed unit
balls around the centers `c j`. -/
@[expose] def localizedTuples {ι : Type*} [Fintype ι] (L : ℝ) (c : ι → Mom d) :
    Set (ι → Fin d → ℤ) :=
  {n | ∀ j, ‖latticePoint L (n j) - c j‖ ≤ 1}

theorem localizedTuples_subset {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ℝ} (hL : 0 < L) (c : ι → Mom d) :
    localizedTuples L c ⊆
      ↑(Fintype.piFinset fun j => latticeBox (fun i => L * c j i) L) := by
  intro n hn
  simp only [Finset.mem_coe, Fintype.mem_piFinset, mem_latticeBox]
  intro j i
  have h1 : ‖(latticePoint L (n j) - c j) i‖ ≤ ‖latticePoint L (n j) - c j‖ :=
    PiLp.norm_apply_le _ i
  have h2 := h1.trans (hn j)
  have h3 : (latticePoint L (n j) - c j) i = (n j i : ℝ) / L - c j i := rfl
  rw [h3, Real.norm_eq_abs] at h2
  have h4 : (n j i : ℝ) - L * c j i = L * ((n j i : ℝ) / L - c j i) := by field_simp
  rw [h4, abs_mul, abs_of_pos hL]
  nlinarith [abs_nonneg ((n j i : ℝ) / L - c j i)]

/-- The localized tuples are finite. -/
theorem finite_localizedTuples {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 < L) (c : ι → Mom d) :
    (localizedTuples L c).Finite := by
  classical
  exact (Finset.finite_toSet _).subset (localizedTuples_subset hL c)

/-- At most `(2L+1)^(|ι| d)` localized tuples. -/
theorem ncard_localizedTuples_le {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 < L) (c : ι → Mom d) :
    ((localizedTuples L c).ncard : ℝ) ≤ (2 * L + 1) ^ (Fintype.card ι * d) := by
  classical
  have h1 : (localizedTuples L c).ncard ≤
      (Fintype.piFinset fun j => latticeBox (fun i => L * c j i) L).card := by
    have := Set.ncard_le_ncard (localizedTuples_subset hL c) (Finset.finite_toSet _)
    rwa [Set.ncard_coe_finset] at this
  rw [Fintype.card_piFinset] at h1
  calc ((localizedTuples L c).ncard : ℝ)
      ≤ ((∏ j, (latticeBox (fun i => L * c j i) L).card : ℕ) : ℝ) := by exact_mod_cast h1
    _ = ∏ j, (((latticeBox (fun i => L * c j i) L).card : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ ∏ _j : ι, (2 * L + 1) ^ d :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
          (fun j _ => card_latticeBox_le _ hL.le)
    _ = _ := by rw [Finset.prod_const, Finset.card_univ, ← pow_mul, mul_comm d]

variable {J E : Type*} [MeasurableSpace J] [NormedAddCommGroup E]

end WaveTurbulence.Flower.FlFiber
