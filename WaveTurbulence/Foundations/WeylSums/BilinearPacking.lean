/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.ParityReindex
public import WaveTurbulence.Foundations.WeylSums.BilinearAmplitudeFourier
public import WaveTurbulence.Foundations.WeylSums.MinorArcSums

/-! # Physical and diagonal coordinates for joint bilinear amplitudes -/

public section
open Finset
open scoped BigOperators
namespace WaveTurbulence.WeylSums

/-- Pack the two physical momentum vectors in one Euclidean space. -/
@[expose] noncomputable def packBilinear {d : ℕ} (x y : Mom d) :
    EuclideanSpace ℝ (Fin d × Fin 2) := WithLp.toLp 2 (fun i => if i.2 = 0 then x i.1 else y i.1)

/-- Extract one of the two momentum vectors. -/
@[expose] noncomputable def unpackBilinear {d : ℕ}
    (z : EuclideanSpace ℝ (Fin d × Fin 2)) (k : Fin 2) : Mom d :=
  WithLp.toLp 2 (fun j => z (j,k))

/-- The source amplitude as a function of the joint physical coordinates. -/
@[expose] noncomputable def packedBilinearAmplitude {d : ℕ} (Φ : Mom d → Mom d → ℂ)
    (z : EuclideanSpace ℝ (Fin d × Fin 2)) : ℂ :=
  Φ (unpackBilinear z 0) (unpackBilinear z 1)

@[simp] theorem unpack_packBilinear_zero {d : ℕ} (x y : Mom d) :
    unpackBilinear (packBilinear x y) 0 = x := by ext j; simp [unpackBilinear,packBilinear]

@[simp] theorem unpack_packBilinear_one {d : ℕ} (x y : Mom d) :
    unpackBilinear (packBilinear x y) 1 = y := by ext j; simp [unpackBilinear,packBilinear]

/-- Spatial centers under sum/difference coordinates. -/
@[expose] noncomputable def diagonalBilinearCenter {d : ℕ} (a b : Mom d) :
    EuclideanSpace ℝ (Fin d × Fin 2) :=
  WithLp.toLp 2 (fun i => if i.2 = 0 then a i.1+b i.1 else a i.1-b i.1)

/-- The inverse diagonal map recovers both physical lattice momenta exactly. -/
theorem bilinearDiagonalMap_pairSample {d : ℕ} {L : ℝ} (hL : L ≠ 0)
    (v : Fin d → ℤ × ℤ) :
    bilinearDiagonalMap d (pairLatticeSample L (fun _ => 0) (pairDiagonalize v)) =
      packBilinear (latticePoint L (fun j => (v j).1)) (latticePoint L (fun j => (v j).2)) := by
  ext ⟨j,k⟩
  fin_cases k
  · simp [bilinearDiagonalMap_apply, pairLatticeSample_apply_zero,
      pairLatticeSample_apply_one, pairDiagonalize, packBilinear, latticePoint]
    field_simp [hL]
    ring
  · simp [bilinearDiagonalMap_apply, pairLatticeSample_apply_zero,
      pairLatticeSample_apply_one, pairDiagonalize, packBilinear, latticePoint]
    field_simp [hL]
    ring

/-- The fixed joint cutoff is precisely the product of the two physical cutoffs. -/
theorem bilinearJointCutoff_eq {d : ℕ} (z : EuclideanSpace ℝ (Fin d × Fin 2)) :
    bilinearJointCutoff d z =
      (latticeCutoff (unpackBilinear (bilinearDiagonalMap d z) 0)*
        latticeCutoff (unpackBilinear (bilinearDiagonalMap d z) 1) : ℝ) := by
  simp only [bilinearJointCutoff, Fintype.prod_prod_type, Fin.prod_univ_two,
    latticeCutoff, unpackBilinear, PiLp.toLp_apply, prod_mul_distrib, Complex.ofReal_mul]

/-- The diagonal map also carries the spatial centers to their physical centers. -/
theorem bilinearDiagonalMap_center {d : ℕ} (a b : Mom d) :
    bilinearDiagonalMap d (diagonalBilinearCenter a b) = packBilinear a b := by
  ext ⟨j,k⟩
  fin_cases k <;> simp [bilinearDiagonalMap_apply, diagonalBilinearCenter, packBilinear]
  all_goals ring

/-- Localization commutes exactly with the linear coordinate change. -/
theorem weightedDiagonalAmplitude_eq_physical {d : ℕ}
    (Φ : Mom d → Mom d → ℂ) (width : ℝ) (a b : Mom d)
    (z : EuclideanSpace ℝ (Fin d × Fin 2)) :
    weightedDiagonalAmplitude (packedBilinearAmplitude Φ) width (diagonalBilinearCenter a b) z =
      Φ (unpackBilinear (bilinearDiagonalMap d z) 0) (unpackBilinear (bilinearDiagonalMap d z) 1) *
      (latticeCutoff (width⁻¹ • (unpackBilinear (bilinearDiagonalMap d z) 0-a))*
        latticeCutoff (width⁻¹ • (unpackBilinear (bilinearDiagonalMap d z) 1-b)) : ℝ) := by
  have hu (k : Fin 2) :
      unpackBilinear (bilinearDiagonalMap d (width⁻¹ • (z-diagonalBilinearCenter a b))) k =
        width⁻¹ • (unpackBilinear (bilinearDiagonalMap d z) k-unpackBilinear (packBilinear a b) k) := by
    ext j
    simp [unpackBilinear, map_smul, map_sub, bilinearDiagonalMap_center]
  simp only [weightedDiagonalAmplitude, packedBilinearAmplitude, scaledTranslatedCutoff,
    bilinearJointCutoff_eq, hu, unpack_packBilinear_zero, unpack_packBilinear_one]

/-- The localized diagonal amplitude evaluated on the sum/difference image
recovers the original physical amplitude and cutoffs. -/
theorem weightedDiagonalAmplitude_pairDiagonalize {d : ℕ} {L : ℝ} (hL : L ≠ 0)
    (Φ : Mom d → Mom d → ℂ) (width : ℝ) (a b : Mom d) (v : Fin d → ℤ × ℤ) :
    weightedDiagonalAmplitude (packedBilinearAmplitude Φ) width (diagonalBilinearCenter a b)
      (pairLatticeSample L (fun _ => 0) (pairDiagonalize v)) =
      Φ (latticePoint L (fun j => (v j).1)) (latticePoint L (fun j => (v j).2)) *
      (latticeCutoff (width⁻¹ • (latticePoint L (fun j => (v j).1)-a))*
        latticeCutoff (width⁻¹ • (latticePoint L (fun j => (v j).2)-b)) : ℝ) := by
  rw [weightedDiagonalAmplitude_eq_physical, bilinearDiagonalMap_pairSample hL]
  simp only [unpack_packBilinear_zero, unpack_packBilinear_one]

end WaveTurbulence.WeylSums
