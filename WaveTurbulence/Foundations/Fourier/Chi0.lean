/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# The fixed time and momentum cutoff

TARGET L617–L623. The scalar cutoff is the product of two affine copies of
Mathlib's explicit `expNegInvGlue` transition. It is even, smooth, valued in
`[0,1]`, one on `[-1/2,1/2]`, and zero outside `(-1,1)`.

Erratum F41 (owner ruling): the literal derivative bound `(2m)!` in L623 is
impossible for this plateau and support. The intended quantitative bound is
`C * A^m * (2*m)!`, for fixed absolute constants. The quantitative estimate
is a separate proof obligation; the results below establish the geometric
and smoothness properties only.
-/

public section

open Set

namespace WaveTurbulence.Fourier

/-- TARGET L617–L623: a concrete cutoff, expressed using the standard
`exp(-1/x)` smooth transition. See the module docstring for erratum F41. -/
@[expose] noncomputable def chi0 (x : ℝ) : ℝ :=
  Real.smoothTransition (2 - 2 * x) * Real.smoothTransition (2 + 2 * x)

/-- The complementary cutoff of TARGET L623. -/
@[expose] noncomputable def chiInfinity (x : ℝ) : ℝ := 1 - chi0 x

/-- The tensor product convention of TARGET L623. -/
@[expose] noncomputable def chi0Tensor {d : ℕ} (x : Fin d → ℝ) : ℝ :=
  ∏ i, chi0 (x i)

theorem chi0_nonneg (x : ℝ) : 0 ≤ chi0 x :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem chi0_le_one (x : ℝ) : chi0 x ≤ 1 :=
  calc
    chi0 x ≤ 1 * Real.smoothTransition (2 + 2 * x) :=
      mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _)
        (Real.smoothTransition.nonneg _)
    _ ≤ 1 := by simpa using Real.smoothTransition.le_one (2 + 2 * x)

theorem chi0_even (x : ℝ) : chi0 (-x) = chi0 x := by
  unfold chi0
  ring_nf

theorem chi0_eq_one {x : ℝ} (hx : |x| ≤ 1 / 2) : chi0 x = 1 := by
  obtain ⟨hl, hu⟩ := abs_le.mp hx
  rw [chi0, Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), mul_one]

theorem chi0_eq_zero {x : ℝ} (hx : 1 ≤ |x|) : chi0 x = 0 := by
  rcases le_abs.mp hx with h | h
  · rw [chi0, Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
  · rw [chi0, Real.smoothTransition.zero_of_nonpos (x := 2 + 2 * x) (by linarith),
      mul_zero]

@[fun_prop] theorem chi0_contDiff {n : ℕ∞} : ContDiff ℝ n chi0 := by
  unfold chi0
  fun_prop

@[fun_prop] theorem chiInfinity_contDiff {n : ℕ∞} : ContDiff ℝ n chiInfinity :=
  contDiff_const.sub chi0_contDiff

theorem chi0_hasCompactSupport : HasCompactSupport chi0 := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
  intro x hx
  apply chi0_eq_zero
  by_contra h
  have hh := abs_lt.mp (lt_of_not_ge h)
  exact hx ⟨hh.1.le, hh.2.le⟩

theorem chi0_integrable : MeasureTheory.Integrable chi0 :=
  (chi0_contDiff (n := 0)).continuous.integrable_of_hasCompactSupport chi0_hasCompactSupport

theorem chi0Tensor_nonneg {d : ℕ} (x : Fin d → ℝ) : 0 ≤ chi0Tensor x :=
  Finset.prod_nonneg fun _ _ => chi0_nonneg _

theorem chi0Tensor_le_one {d : ℕ} (x : Fin d → ℝ) : chi0Tensor x ≤ 1 :=
  by
    simpa [chi0Tensor] using Finset.prod_le_prod₀ (s := Finset.univ)
      (f := fun i => chi0 (x i)) (g := fun _ => (1 : ℝ))
      (fun _ _ => chi0_nonneg _) (fun _ _ => chi0_le_one _)

theorem chi0Tensor_eq_one {d : ℕ} {x : Fin d → ℝ}
    (hx : ∀ i, |x i| ≤ 1 / 2) : chi0Tensor x = 1 := by
  unfold chi0Tensor
  exact Finset.prod_eq_one fun i _ => chi0_eq_one (hx i)

theorem chi0Tensor_eq_zero {d : ℕ} {x : Fin d → ℝ} (i : Fin d)
    (hx : 1 ≤ |x i|) : chi0Tensor x = 0 := by
  exact Finset.prod_eq_zero (Finset.mem_univ i) (chi0_eq_zero hx)

@[fun_prop] theorem chi0Tensor_contDiff {d : ℕ} {n : ℕ∞} :
    ContDiff ℝ n (chi0Tensor (d := d)) := by
  apply contDiff_prod
  intro i _
  apply chi0_contDiff.comp
  fun_prop

end WaveTurbulence.Fourier
