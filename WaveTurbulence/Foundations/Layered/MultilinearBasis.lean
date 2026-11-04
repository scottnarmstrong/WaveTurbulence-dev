/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Frozen.Defs.Mom
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-!
# Operator norms of multilinear maps from their values on basis words

For a continuous multilinear map `M` on `n` copies of `ℝ^d` (Euclidean), the operator norm is at most the
sum of `‖M(e_{w₁}, …, e_{wₙ})‖` over all words `w : Fin n → Fin d` in the standard basis
(`norm_le_sum_basis_words`); conversely each such value is at most `‖M‖`
(`norm_apply_basis_word_le`). Hence the iterated Fréchet derivatives and the coordinate partial derivatives
of TARGET (normX2) control each other up to the factor `d^n`.
-/

public section

open Finset

namespace WaveTurbulence.Layered

variable {d n : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The standard basis vector `e_j` of `ℝ^d`. -/
noncomputable def basisVec (j : Fin d) : Mom d := EuclideanSpace.single j 1

theorem norm_basisVec (j : Fin d) : ‖basisVec j‖ = 1 := by
  simp [basisVec, EuclideanSpace.single, PiLp.norm_single]

theorem norm_apply_basis_word_le (M : ContinuousMultilinearMap ℝ (fun _ : Fin n => Mom d) G)
    (w : Fin n → Fin d) : ‖M (fun i => basisVec (w i))‖ ≤ ‖M‖ := by
  refine (M.le_opNorm _).trans ?_
  simp [norm_basisVec]

/-- **The operator norm is at most the sum of the values on basis words.** -/
theorem norm_le_sum_basis_words (M : ContinuousMultilinearMap ℝ (fun _ : Fin n => Mom d) G) :
    ‖M‖ ≤ ∑ w : Fin n → Fin d, ‖M (fun i => basisVec (w i))‖ := by
  refine M.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun v => ?_
  have hv : ∀ i, v i = ∑ j : Fin d, v i j • basisVec j := by
    intro i
    ext l
    simp [basisVec, Finset.sum_apply, EuclideanSpace.single, Pi.single_apply]
  have hM : M v = ∑ w : Fin n → Fin d, (∏ i, v i (w i)) • M (fun i => basisVec (w i)) := by
    conv_lhs => rw [show v = fun i => ∑ j : Fin d, v i j • basisVec j from funext hv]
    rw [M.map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [M.map_smul_univ]
  rw [hM]
  calc ‖∑ w : Fin n → Fin d, (∏ i, v i (w i)) • M (fun i => basisVec (w i))‖
      ≤ ∑ w : Fin n → Fin d, ‖(∏ i, v i (w i)) • M (fun i => basisVec (w i))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ w : Fin n → Fin d, (∏ i, ‖v i‖) * ‖M (fun i => basisVec (w i))‖ := by
        refine Finset.sum_le_sum fun w _ => ?_
        rw [norm_smul, norm_prod]
        gcongr with i
        exact PiLp.norm_apply_le (v i) (w i)
    _ = (∑ w : Fin n → Fin d, ‖M (fun i => basisVec (w i))‖) * ∏ i, ‖v i‖ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

end WaveTurbulence.Layered
