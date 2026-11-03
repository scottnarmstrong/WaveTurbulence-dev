/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Fintype.Pi

/-! # From coordinate partial derivatives to operator-norm derivatives

An order-`j` coordinate word is a sequence of `j` coordinate basis vectors.
For a `C^N` function its iterated derivative on that word is the corresponding
mixed coordinate partial derivative. Bounding all such words is the usual
coordinate derivative bound, with repetitions allowed.
-/

public section
open Finset
open scoped BigOperators
namespace WaveTurbulence.WeylSums

/-- A quantitative finite-dimensional comparison, valid also at order zero. -/
theorem norm_multilinear_le_coordinate_bound {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ℕ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin j => EuclideanSpace ℝ ι) ℂ)
    (D : ℝ) (hD : 0 ≤ D)
    (hb : ∀ v : Fin j → ι, ‖T (fun k => EuclideanSpace.single (v k) 1)‖ ≤ D) :
    ‖T‖ ≤ (Fintype.card ι : ℝ)^j*D := by
  classical
  apply T.opNorm_le_bound (by positivity)
  intro x
  have hrepr (k : Fin j) : x k = ∑ i : ι, (x k i) • EuclideanSpace.single i 1 := by
    ext i
    simp [Pi.single_apply]
  have hexp : T x = ∑ v : Fin j → ι,
      (∏ k, x k (v k)) • T (fun k => EuclideanSpace.single (v k) 1) := by
    calc
      T x = T (fun k => ∑ i : ι, (x k i) • EuclideanSpace.single i 1) := congrArg T (funext hrepr)
      _ = _ := by
        rw [T.map_sum]
        apply sum_congr rfl
        intro v hv
        exact T.map_smul_univ _ _
  rw [hexp]
  calc
    _ ≤ ∑ v : Fin j → ι, ‖(∏ k, x k (v k)) • T (fun k => EuclideanSpace.single (v k) 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _v : Fin j → ι, (∏ k, ‖x k‖)*D := by
      apply sum_le_sum
      intro v hv
      rw [norm_smul, norm_prod]
      apply mul_le_mul _ (hb v) (norm_nonneg _) (prod_nonneg (fun k hk => norm_nonneg _))
      exact prod_le_prod₀ (fun k hk => norm_nonneg _) (fun k hk => PiLp.norm_apply_le (x k) (v k))
    _ = (Fintype.card ι : ℝ)^j*D*∏ k, ‖x k‖ := by
      simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
      ring

/-- Coordinate-word derivative bounds, the standard mixed-partial convention. -/
@[expose] def CoordinateDerivativeBound {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ℕ)
    (f : EuclideanSpace ℝ ι → ℂ) (D : ℝ) : Prop :=
  ∀ j ≤ N, ∀ x, ∀ v : Fin j → ι,
    ‖iteratedFDeriv ℝ j f x (fun k => EuclideanSpace.single (v k) 1)‖ ≤ D

/-- One constant controls every operator derivative through order `N`. -/
theorem CoordinateDerivativeBound.operator_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ℕ} {f : EuclideanSpace ℝ ι → ℂ} {D : ℝ} (hD : 0 ≤ D)
    (hb : CoordinateDerivativeBound N f D) (j : ℕ) (hj : j ≤ N) (x : EuclideanSpace ℝ ι) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ (Fintype.card ι+1 : ℝ)^N*D := by
  apply (norm_multilinear_le_coordinate_bound j _ D hD (hb j hj x)).trans
  apply mul_le_mul_of_nonneg_right _ hD
  calc
    (Fintype.card ι : ℝ)^j ≤ (Fintype.card ι+1 : ℝ)^j :=
      pow_le_pow_left₀ (show (0 : ℝ) ≤ Fintype.card ι by positivity) (by linarith) j
    _ ≤ (Fintype.card ι+1 : ℝ)^N := pow_le_pow_right₀ (by have h := Nat.cast_nonneg (α := ℝ) (Fintype.card ι); linarith) hj

end WaveTurbulence.WeylSums
