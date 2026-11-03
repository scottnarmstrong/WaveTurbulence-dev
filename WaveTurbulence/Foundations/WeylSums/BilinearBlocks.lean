/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.CoordinateBoxSupport
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Sum/difference coordinates on the two momentum blocks

The diagonal-to-original map has norm at most one. Consequently the source
finite derivative bound for the amplitude is preserved under this map.
The fixed joint cutoff has coordinate support radius two.
-/

public section
open Finset
open scoped BigOperators ContDiff
namespace WaveTurbulence.WeylSums

/-- The original coordinates are half the sum and half the difference. -/
@[expose] noncomputable def bilinearDiagonalLinear (d : ℕ) :
    EuclideanSpace ℝ (Fin d × Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin d × Fin 2) where
  toFun z := WithLp.toLp 2 (fun i => (z (i.1,0)+(-1 : ℝ)^i.2.val*z (i.1,1))/2)
  map_add' x y := by
    ext i
    simp only [PiLp.add_apply]
    ring
  map_smul' c x := by
    ext i
    simp only [PiLp.smul_apply,  smul_eq_mul, RingHom.id_apply]
    ring

/-- The same finite-dimensional map as a bounded operator. -/
@[expose] noncomputable def bilinearDiagonalMap (d : ℕ) :
    EuclideanSpace ℝ (Fin d × Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin d × Fin 2) :=
  (bilinearDiagonalLinear d).toContinuousLinearMap

theorem bilinearDiagonalMap_apply {d : ℕ} (z : EuclideanSpace ℝ (Fin d × Fin 2)) (i : Fin d × Fin 2) :
    bilinearDiagonalMap d z i = (z (i.1,0)+(-1 : ℝ)^i.2.val*z (i.1,1))/2 := rfl

/-- The map is an orthogonal map followed by scaling by `1/√2`. -/
theorem bilinearDiagonalMap_norm_sq {d : ℕ} (z : EuclideanSpace ℝ (Fin d × Fin 2)) :
    2*‖bilinearDiagonalMap d z‖^2 = ‖z‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    Fintype.sum_prod_type, Fintype.sum_prod_type, mul_sum]
  apply sum_congr rfl
  intro i hi
  simp only [Fin.sum_univ_two, bilinearDiagonalMap_apply, Fin.val_zero, Fin.val_one,
    pow_zero, pow_one, one_mul, neg_one_mul]
  ring

theorem bilinearDiagonalMap_norm_le (d : ℕ) : ‖bilinearDiagonalMap d‖ ≤ 1 := by
  apply (bilinearDiagonalMap d).opNorm_le_bound (by norm_num : (0 : ℝ) ≤ 1)
  intro z
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hs := bilinearDiagonalMap_norm_sq z
  nlinarith only [hs, sq_nonneg ‖z‖]

/-- The fixed joint cutoff in the diagonal variables, before translation and dilation. -/
@[expose] noncomputable def bilinearJointCutoff (d : ℕ)
    (z : EuclideanSpace ℝ (Fin d × Fin 2)) : ℂ :=
  (∏ i : Fin d × Fin 2, Fourier.chi0 (bilinearDiagonalMap d z i) : ℝ)

/-- Its support is contained in a coordinate cube independent of the centers. -/
theorem bilinearJointCutoff_support {d : ℕ} (z : EuclideanSpace ℝ (Fin d × Fin 2))
    (hz : bilinearJointCutoff d z ≠ 0) (i : Fin d × Fin 2) : |z i| ≤ 2 := by
  have hall : ∀ j : Fin d × Fin 2, Fourier.chi0 (bilinearDiagonalMap d z j) ≠ 0 := by
    simpa only [bilinearJointCutoff, ne_eq, Complex.ofReal_eq_zero,
      prod_ne_zero_iff, mem_univ, true_imp_iff] using hz
  have hu : |(z (i.1,0)+z (i.1,1))/2| < 1 := by
    by_contra hh
    apply hall (i.1,0)
    apply Fourier.chi0_eq_zero
    simpa only [bilinearDiagonalMap_apply, Fin.val_zero, pow_zero, one_mul] using not_lt.mp hh
  have hv : |(z (i.1,0)-z (i.1,1))/2| < 1 := by
    by_contra hh
    apply hall (i.1,1)
    apply Fourier.chi0_eq_zero
    simpa only [bilinearDiagonalMap_apply, Fin.val_one, pow_one, neg_one_mul, sub_eq_add_neg] using not_lt.mp hh
  obtain ⟨hul,huu⟩ := abs_lt.mp hu
  obtain ⟨hvl,hvu⟩ := abs_lt.mp hv
  rcases i with ⟨j,k⟩
  fin_cases k
  · change |z (j,0)| ≤ 2
    apply abs_le.mpr
    constructor <;> linarith only [hul,huu,hvl,hvu]
  · change |z (j,1)| ≤ 2
    apply abs_le.mpr
    constructor <;> linarith only [hul,huu,hvl,hvu]

theorem bilinearJointCutoff_hasCompactSupport (d : ℕ) : HasCompactSupport (bilinearJointCutoff d) :=
  hasCompactSupport_of_coordinate_box _ 2 (by norm_num) bilinearJointCutoff_support

@[fun_prop] theorem bilinearJointCutoff_contDiff (d : ℕ) : ContDiff ℝ ∞ (bilinearJointCutoff d) := by
  have hreal : ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ (Fin d × Fin 2) =>
      ∏ i : Fin d × Fin 2, Fourier.chi0 (bilinearDiagonalMap d z i)) := by
    apply contDiff_prod
    intro i hi
    apply Fourier.chi0_contDiff.comp
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d × Fin 2 => ℝ) i).contDiff.comp
      (bilinearDiagonalMap d).contDiff
  exact Complex.ofRealCLM.contDiff.comp hreal

end WaveTurbulence.WeylSums
