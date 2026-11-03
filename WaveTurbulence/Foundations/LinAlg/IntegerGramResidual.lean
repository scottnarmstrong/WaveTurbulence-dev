/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LinAlg.OrthogonalResidualFamily
public import WaveTurbulence.Foundations.LinAlg.LatticeObservations

/-!
# Integral denominator-free Gram residuals

The projection step of TARGET Lemma A.6 preserves integer coordinates when
its Gram determinant is used to clear denominators.
-/

public section

namespace WaveTurbulence.LinAlg
open Finset
open scoped Classical InnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}

/-- The integer Gram matrix for an integer-coordinate family. -/
@[expose] def integerGram (w : ι → Fin d → ℤ) : Matrix ι ι ℤ :=
  fun i j => ∑ a, w i a * w j a

omit [Fintype ι] [DecidableEq ι] in
/-- Casting the integer Gram matrix gives the real Gram matrix. -/
theorem integerGram_cast (w : ι → Fin d → ℤ) :
    (integerGram w).map (fun a : ℤ => (a : ℝ)) =
      Matrix.gram ℝ (fun i => latticePoint 1 (w i)) := by
  ext i j
  simp only [Matrix.map_apply, integerGram, Matrix.gram_apply, inner_latticePoint,
    one_pow, div_one]

/-- Casting Cramer's coefficients commutes with forming the Gram matrix. -/
theorem integerGram_cramer_cast (w : ι → Fin d → ℤ) (u : Fin d → ℤ) (j : ι) :
    (((integerGram w).cramer (fun i => ∑ a, w i a * u a) j : ℤ) : ℝ) =
      (Matrix.gram ℝ (fun i => latticePoint 1 (w i))).cramer
        (fun i => ⟪latticePoint 1 (w i), latticePoint 1 u⟫_ℝ) j := by
  rw [Matrix.cramer_apply, Matrix.cramer_apply, Int.cast_det, Matrix.map_updateCol,
    integerGram_cast]
  congr 2
  funext i
  simp only [Function.comp_apply, inner_latticePoint, one_pow, div_one]

/-- The integer coordinate formula for the denominator-free residual. -/
@[expose] noncomputable def integerGramResidual (w : ι → Fin d → ℤ) (u : Fin d → ℤ) :
    Fin d → ℤ := fun a =>
  (integerGram w).det * u a -
    ∑ i, (integerGram w).cramer (fun j => ∑ b, w j b * u b) i * w i a

/-- The real residual is exactly the image of the integer residual. -/
theorem gramResidual_latticePoint_one (w : ι → Fin d → ℤ) (u : Fin d → ℤ) :
    gramResidual (fun i => latticePoint 1 (w i)) (latticePoint 1 u) =
      latticePoint 1 (integerGramResidual w u) := by
  have hd : ((integerGram w).det : ℝ) =
      (Matrix.gram ℝ (fun i => latticePoint 1 (w i))).det := by
    rw [Int.cast_det, integerGram_cast]
  apply WithLp.ofLp_injective
  funext a
  simp only [gramResidual, WithLp.ofLp_sub, WithLp.ofLp_smul, WithLp.ofLp_sum,
    Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, latticePoint, WithLp.ofLp_toLp,
    div_one, integerGramResidual, Int.cast_sub, Int.cast_mul, Int.cast_sum,
    hd, integerGram_cramer_cast, smul_eq_mul]

/-- The integer-coordinate orthogonalization of an integer-coordinate family. -/
@[expose] noncomputable def integerOrthogonalFamily {q : ℕ} (w : Fin q → Fin d → ℤ)
    (j : Fin q) : Fin d → ℤ :=
  integerGramResidual (w ∘ prefixIndex j) (w j)

/-- Integer orthogonalization agrees exactly with real denominator-free orthogonalization. -/
theorem integerOrthogonalFamily_cast {q : ℕ} (w : Fin q → Fin d → ℤ) (j : Fin q) :
    orthogonalResidualFamily (fun i => latticePoint 1 (w i)) j =
      latticePoint 1 (integerOrthogonalFamily w j) := by
  simpa only [orthogonalResidualFamily, integerOrthogonalFamily, Function.comp_def] using
    gramResidual_latticePoint_one (w ∘ prefixIndex j) (w j)

end WaveTurbulence.LinAlg
