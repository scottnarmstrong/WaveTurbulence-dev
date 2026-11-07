/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.ShapeFacts
import Mathlib.Tactic

/-!
# The nonzero output momentum is bounded below by the lattice spacing

The common affine coset in the exact draft makes `r = e - f` a genuine
lattice difference. This is the source input required for F23's second
linear estimate, rather than an additional assumption.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.SumintPar

/-- Taking a difference cancels the common coset shift. -/
theorem latticePoint_sub {d : ℕ} (L : ℝ) (n m : Fin d → ℤ) :
    latticePoint L (n - m) = latticePoint L n - latticePoint L m := by
  ext j
  change (((n j - m j : ℤ) : ℝ) / L) = (n j : ℝ) / L - (m j : ℝ) / L
  push_cast
  ring

/-- A nonzero lattice vector has norm at least the reciprocal mesh parameter. -/
theorem inv_le_norm_latticePoint {d : ℕ} {L : ℝ} (hL : 0 < L)
    {n : Fin d → ℤ} (hn : n ≠ 0) : L⁻¹ ≤ ‖latticePoint L n‖ := by
  have hj : ∃ j, n j ≠ 0 := by
    by_contra h
    push Not at h
    apply hn
    funext j
    exact h j
  obtain ⟨j, hj⟩ := hj
  have hz : (1 : ℝ) ≤ |(n j : ℝ)| := by exact_mod_cast Int.one_le_abs hj
  have hc : |(n j : ℝ) / L| ≤ ‖latticePoint L n‖ := by
    have hh := PiLp.norm_apply_le (latticePoint L n) j
    change ‖((n j : ℝ) / L)‖ ≤ ‖latticePoint L n‖ at hh
    simpa only [Real.norm_eq_abs] using hh
  calc
    L⁻¹ = 1 / L := (one_div L).symm
    _ ≤ |(n j : ℝ)| / L := div_le_div_of_nonneg_right hz hL.le
    _ = |(n j : ℝ) / L| := by rw [abs_div, abs_of_pos hL]
    _ ≤ _ := hc

/-- The exact output coset condition implies the lower momentum hypothesis of `lemlin`. -/
theorem inv_le_norm_coset_difference {d : ℕ} {L : ℝ} (hL : 0 < L)
    {w e f : Mom d} (he : ∃ n : Fin d → ℤ, e = w + latticePoint L n)
    (hf : ∃ n : Fin d → ℤ, f = w + latticePoint L n) (hne : e ≠ f) :
    L⁻¹ ≤ ‖e - f‖ := by
  obtain ⟨n, rfl⟩ := he
  obtain ⟨m, rfl⟩ := hf
  have heq : w + latticePoint L n - (w + latticePoint L m) = latticePoint L (n - m) := by
    rw [latticePoint_sub]
    abel
  rw [heq]
  apply inv_le_norm_latticePoint hL
  intro hz
  have hnm : n = m := sub_eq_zero.mp hz
  exact hne (by rw [hnm])

end WaveTurbulence.SumintPar
