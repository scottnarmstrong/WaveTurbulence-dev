/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LinAlg.GramResidual
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Orthogonalization without division

Apply the denominator-free Gram residual to each initial segment of an
independent family. The resulting nonzero orthogonal family has the same span.
-/

public section

namespace WaveTurbulence.LinAlg
open Finset Module
open scoped Classical InnerProductSpace

/-- The canonical embedding of the indices strictly preceding `j`. -/
@[expose] def prefixIndex {q : ℕ} (j : Fin q) : Fin j.val ↪ Fin q where
  toFun i := ⟨i.val, lt_trans i.isLt j.isLt⟩
  inj' _ _ h := Fin.ext (congrArg (fun i : Fin q => i.val) h)

@[simp] theorem range_prefixIndex {q : ℕ} (j : Fin q) :
    Set.range (prefixIndex j) = Set.Iio j := by
  ext i
  constructor
  · rintro ⟨k, rfl⟩
    exact k.isLt
  · intro hi
    exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {q : ℕ}

/-- The integer-preserving orthogonalization of a finite ordered family. -/
@[expose] noncomputable def orthogonalResidualFamily (w : Fin q → E) (j : Fin q) : E :=
  gramResidual (w ∘ prefixIndex j) (w j)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- The input family before `j` has exactly the expected span. -/
theorem range_prefix_family (w : Fin q → E) (j : Fin q) :
    Set.range (w ∘ prefixIndex j) = w '' Set.Iio j := by
  rw [Set.range_comp, range_prefixIndex]

/-- Independence prevents a denominator-free Gram residual from vanishing. -/
theorem orthogonalResidualFamily_ne_zero {w : Fin q → E} (hw : LinearIndependent ℝ w)
    (j : Fin q) : orthogonalResidualFamily w j ≠ 0 := by
  apply gramResidual_ne_zero (hw.comp _ (prefixIndex j).injective)
  rw [range_prefix_family]
  exact hw.notMem_span_image (by simp)

/-- The `j`th residual belongs to the span through index `j`. -/
theorem orthogonalResidualFamily_mem_span_Iic (w : Fin q → E) (j : Fin q) :
    orthogonalResidualFamily w j ∈ Submodule.span ℝ (w '' Set.Iic j) := by
  apply Submodule.span_mono (s := insert (w j) (Set.range (w ∘ prefixIndex j))) ?_
    (gramResidual_mem_span _ _)
  rw [range_prefix_family]
  rintro x (rfl | ⟨i, hi, rfl⟩)
  · exact ⟨j, Set.mem_Iic.mpr le_rfl, rfl⟩
  · exact ⟨i, Set.mem_Iic.mpr (Set.mem_Iio.mp hi).le, rfl⟩

/-- Distinct residuals are orthogonal. -/
theorem orthogonalResidualFamily_pairwise (w : Fin q → E) :
    Pairwise fun i j => ⟪orthogonalResidualFamily w i, orthogonalResidualFamily w j⟫_ℝ = 0 := by
  have hlt {i j : Fin q} (hij : i < j) :
      ⟪orthogonalResidualFamily w j, orthogonalResidualFamily w i⟫_ℝ = 0 := by
    have hm : orthogonalResidualFamily w i ∈
        Submodule.span ℝ (Set.range (w ∘ prefixIndex j)) := by
      rw [range_prefix_family]
      apply Submodule.span_mono (Set.image_mono (Set.Iic_subset_Iio.mpr hij))
        (orthogonalResidualFamily_mem_span_Iic w i)
    apply LinearMap.eqOn_span (f := (innerSL ℝ (orthogonalResidualFamily w j)).toLinearMap)
      (g := 0) ?_ hm
    rintro _ ⟨k, rfl⟩
    change ⟪gramResidual (w ∘ prefixIndex j) (w j), w (prefixIndex j k)⟫_ℝ = 0
    rw [real_inner_comm]
    exact inner_gramResidual (w ∘ prefixIndex j) (w j) k
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · rw [real_inner_comm]
    exact hlt h
  · exact hlt h

/-- The denominator-free orthogonalization remains independent. -/
theorem orthogonalResidualFamily_linearIndependent {w : Fin q → E}
    (hw : LinearIndependent ℝ w) : LinearIndependent ℝ (orthogonalResidualFamily w) :=
  linearIndependent_of_ne_zero_of_inner_eq_zero
    (orthogonalResidualFamily_ne_zero hw) (orthogonalResidualFamily_pairwise w)

/-- The denominator-free orthogonalization preserves the span. -/
theorem span_orthogonalResidualFamily [FiniteDimensional ℝ E] {w : Fin q → E} (hw : LinearIndependent ℝ w) :
    Submodule.span ℝ (Set.range (orthogonalResidualFamily w)) =
      Submodule.span ℝ (Set.range w) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Submodule.span_mono (Set.image_subset_range _ _)
      (orthogonalResidualFamily_mem_span_Iic w j)
  · rw [finrank_span_eq_card (orthogonalResidualFamily_linearIndependent hw),
      finrank_span_eq_card hw]

/-- A uniform norm bound for every residual in a bounded input family. -/
theorem norm_orthogonalResidualFamily_le {w : Fin q → E} {B : ℝ}
    (hB : 1 ≤ B) (hw : ∀ i, ‖w i‖ ≤ B) (j : Fin q) :
    ‖orthogonalResidualFamily w j‖ ≤ (q + 1).factorial * B ^ (2 * q + 1) := by
  have h := norm_gramResidual_le (by linarith : 0 ≤ B)
    (fun i => hw (prefixIndex j i)) (hw j)
  simp only [Fintype.card_fin] at h
  apply h.trans
  apply mul_le_mul
  · exact_mod_cast Nat.factorial_le (by omega : j.val + 1 ≤ q + 1)
  · exact pow_le_pow_right₀ hB (by omega)
  · positivity
  · positivity

/-- A uniform functional-value bound independent of the functional's norm. -/
theorem abs_apply_orthogonalResidualFamily_le {w : Fin q → E} {B : ℝ}
    (hB : 1 ≤ B) (hw : ∀ i, ‖w i‖ ≤ B) (ℓ : E →ₗ[ℝ] ℝ)
    (hlw : ∀ i, |ℓ (w i)| ≤ B) (j : Fin q) :
    |ℓ (orthogonalResidualFamily w j)| ≤ (q + 1).factorial * B ^ (2 * q + 1) := by
  have h := abs_apply_gramResidual_le (by linarith : 0 ≤ B)
    (fun i => hw (prefixIndex j i)) (hw j) ℓ
    (fun i => hlw (prefixIndex j i)) (hlw j)
  simp only [Fintype.card_fin] at h
  apply h.trans
  apply mul_le_mul
  · exact_mod_cast Nat.factorial_le (by omega : j.val + 1 ≤ q + 1)
  · exact pow_le_pow_right₀ hB (by omega)
  · positivity
  · positivity

end WaveTurbulence.LinAlg
