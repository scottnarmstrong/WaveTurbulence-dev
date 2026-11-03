/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LinAlg.IntegerOrthogonalSelection
public import WaveTurbulence.Foundations.LinAlg.LatticeRescaling
public import WaveTurbulence.Foundations.LinAlg.LatticeRepresentatives

/-!
# Bounded orthogonal lattice representations

TARGET Lemma A.6 (`finitelem`, L2435–L2445), the representing-system conclusion.
We use the ambient large-box convention `2 ≤ L ≤ M`, as for the representative
count. Integer Cramer residuals give a polynomial exponent depending only on `d`.
The representing value vector is explicitly a point of `(L⁻² ℤ)^q`.
-/

public section

namespace WaveTurbulence.LinAlg
open Finset
open scoped Classical InnerProductSpace

/-- An explicit, deliberately generous dimension-dependent height exponent. -/
@[expose] def representationHeightExponent (d : ℕ) : ℕ :=
  (d + 1) * (d + 1).factorial + 3 * (2 * d + 1)

/-- TARGET Lemma A.6: bounded nonzero orthogonal lattice vectors span all the
bounded tests with bounded pairing, and their pairing values lie in `L⁻²ℤ`. -/
theorem exists_lattice_representation {d : ℕ} {L M : ℝ} (hL : 2 ≤ L) (hLM : L ≤ M)
    (k : Fin d → ℤ) :
    ∃ q ≤ d, ∃ v : Fin q → Fin d → ℤ, ∃ m : Fin q → ℤ,
      (∀ i, latticePoint L (v i) ≠ 0) ∧
      (Pairwise fun i j => ⟪latticePoint L (v i), latticePoint L (v j)⟫_ℝ = 0) ∧
      (∀ i, ‖latticePoint L (v i)‖ ≤ M ^ representationHeightExponent d) ∧
      ‖latticePoint (L ^ 2) m‖ ≤ M ^ representationHeightExponent d ∧
      (∀ z : Fin d → ℤ, ‖latticePoint L z‖ ≤ M →
        |⟪latticePoint L k, latticePoint L z⟫_ℝ| ≤ M →
        latticePoint L z ∈ Submodule.span ℝ (Set.range fun i => latticePoint L (v i))) ∧
      (∀ γ : Fin q → ℝ,
        ⟪latticePoint L k, ∑ i, γ i • latticePoint L (v i)⟫_ℝ =
          ∑ i, ((m i : ℝ) / L ^ 2) * γ i) := by
  have hLpos : 0 < L := by linarith
  have hM : 2 ≤ M := hL.trans hLM
  have hM0 : 0 ≤ M := by linarith
  have hM1 : 1 ≤ M := by linarith
  have hL0 : 0 ≤ L := hLpos.le
  have hLM3 : L * M ≤ M ^ 3 := by
    calc
      _ ≤ M ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right hLM hM0]
      _ ≤ _ := pow_le_pow_right₀ hM1 (by decide : 2 ≤ 3)
  have hL2M3 : L ^ 2 * M ≤ M ^ 3 := by
    calc
      _ ≤ M ^ 2 * M := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hL0 hLM 2) hM0
      _ = _ := by ring
  let H : Finset (Fin d → ℤ) := (integerCoordinateBox d (L * M)).filter
    (fun z => ‖latticePoint L z‖ ≤ M ∧ |⟪latticePoint L k, latticePoint L z⟫_ℝ| ≤ M)
  let ℓ : Mom d →ₗ[ℝ] ℝ := (innerSL ℝ (latticePoint 1 k)).toLinearMap
  have hH (w) (hw : w ∈ H) : ‖latticePoint 1 w‖ ≤ M ^ 3 :=
    (norm_latticePoint_one_le hLpos w (mem_filter.mp hw).2.1).trans hLM3
  have hℓ (w) (hw : w ∈ H) : |ℓ (latticePoint 1 w)| ≤ M ^ 3 :=
    (abs_inner_latticePoint_one_le hLpos k w (mem_filter.mp hw).2.2).trans hL2M3
  obtain ⟨q, hq, v, hv0, hvorth, hvspan, hvnorm, hvℓ⟩ :=
    exists_integer_orthogonal_selection H (one_le_pow₀ hM1) hH ℓ hℓ
  let m : Fin q → ℤ := fun i => ∑ a, k a * v i a
  let A : ℝ := (d + 1).factorial * (M ^ 3) ^ (2 * d + 1)
  have hA : 0 ≤ A := by positivity
  have hheight : (d + 1 : ℝ) * A ≤ M ^ representationHeightExponent d := by
    let N := (d + 1) * (d + 1).factorial
    have hN : (N : ℝ) ≤ M ^ N := by
      exact (by norm_num : (N : ℝ) ≤ (N + 1 : ℝ)).trans (nat_succ_le_pow_of_two_le hM N)
    calc
      _ = (N : ℝ) * M ^ (3 * (2 * d + 1)) := by simp only [N, A, Nat.cast_mul,
          Nat.cast_add, Nat.cast_one, ← pow_mul]; ring
      _ ≤ M ^ N * M ^ (3 * (2 * d + 1)) := mul_le_mul_of_nonneg_right hN (by positivity)
      _ = _ := by rw [← pow_add]; rfl
  have hAsmall : A ≤ (d + 1 : ℝ) * A := by nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hm (i : Fin q) : |(m i : ℝ) / L ^ 2| ≤ A := by
    have heq : (m i : ℝ) = ℓ (latticePoint 1 (v i)) := by
      change (m i : ℝ) = ⟪latticePoint 1 k, latticePoint 1 (v i)⟫_ℝ
      rw [inner_latticePoint, one_pow, div_one]
    rw [heq, abs_div, abs_of_pos (sq_pos_of_pos hLpos)]
    exact (div_le_self (abs_nonneg _) (by nlinarith : 1 ≤ L ^ 2)).trans (hvℓ i)
  refine ⟨q, hq, v, m, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    apply hv0 i
    rw [latticePoint_one_eq_smul hLpos.ne' (v i), hi, smul_zero]
  · intro i j hij
    simp only [latticePoint_eq_inv_smul L, inner_smul_left, inner_smul_right,
      conj_trivial, hvorth hij, mul_zero]
  · intro i
    exact ((norm_latticePoint_le_one (by linarith) (v i)).trans (hvnorm i)).trans
      (hAsmall.trans hheight)
  · calc
      _ ≤ ∑ i, |latticePoint (L ^ 2) m i| := norm_mom_le_sum_abs _
      _ ≤ ∑ _i : Fin q, A := by
        apply sum_le_sum
        intro i _
        exact hm i
      _ = (q : ℝ) * A := by simp
      _ ≤ (d + 1 : ℝ) * A := mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : q ≤ d + 1)) hA
      _ ≤ _ := hheight
  · intro z hz hzk
    have hzH : z ∈ H := by
      apply mem_filter.mpr
      refine ⟨?_, hz, hzk⟩
      apply Fintype.mem_piFinset.mpr
      intro a
      apply mem_integer_interval_of_abs_le
      have ha := (PiLp.norm_apply_le (latticePoint 1 z) a).trans
        (norm_latticePoint_one_le hLpos z hz)
      simpa only [latticePoint, div_one, Real.norm_eq_abs] using ha
    rw [span_latticePoint_eq hLpos.ne', latticePoint_eq_inv_smul L z]
    apply Submodule.smul_mem
    rw [hvspan]
    exact Submodule.subset_span (mem_image.mpr ⟨z, hzH, rfl⟩)
  · intro γ
    simp only [inner_sum, inner_smul_right, inner_latticePoint, m, mul_comm]

end WaveTurbulence.LinAlg
