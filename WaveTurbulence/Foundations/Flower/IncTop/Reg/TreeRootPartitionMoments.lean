/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.TreeRootPartition
public import WaveTurbulence.Foundations.Incoh.LeafFourierMomentMass
public import WaveTurbulence.Foundations.Incoh.CompactSpatialNorm

/-! Ported by source from C2-B-TOP `Cut2BReg.TreeRootPartitionMoments` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.
 # Translation-invariant actual Fourier moment mass of the temporary tree root input -/

public section
noncomputable section
open MeasureTheory WithLp
open scoped ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
/-- Each translated temporary root input has the finite source spatial norms needed for typing. -/
theorem exists_spatialNorm_bound_treeRootPartitionSpatial {d : ℕ} (N M : ℕ) (q : Fin d → ℤ) :
    ∃ B : ℝ, 0 < B ∧ Fourier.spatialNorm N M (treeRootPartitionSpatial q) ≤ ENNReal.ofReal B :=
  exists_spatialNorm_bound_of_smooth_compact N M
    (contDiff_treeRootPartitionSpatial q) (hasCompactSupport_treeRootPartitionSpatial q)

/-- Translating the actual root input translates its literal leaf-localization center. -/
theorem leafCell_treeRootPartition_translateSpatial {d : ℕ} (q c : Fin d → ℤ) (x : Mom d) :
    leafCell (treeRootPartitionSpatial q) c x =
      leafCell (treeRootPartitionSpatial (0 : Fin d → ℤ)) (c - q) (x - NTSP.intVec q) := by
  have he : (x - NTSP.intVec q) - NTSP.intVec (c - q) = x - NTSP.intVec c := by
    rw [NTSP.intVec_sub]
    abel
  simp only [leafCell, treeRootPartitionSpatial, leafCellProfile, NTSP.intVec_zero, sub_zero, he]

/-- The actual Fourier absolute value is invariant under the root-cell translation. -/
theorem norm_timeFourier_leafCell_treeRootPartition_translateSpatial {d : ℕ} (q c : Fin d → ℤ)
    (ξ : Fin d → ℝ) :
    ‖Fourier.timeFourier (fun x => leafCell (treeRootPartitionSpatial q) c (toLp 2 x)) ξ‖ =
      ‖Fourier.timeFourier (fun x => leafCell (treeRootPartitionSpatial (0 : Fin d → ℤ)) (c - q) (toLp 2 x)) ξ‖ := by
  have he : (fun x : Fin d → ℝ => leafCell (treeRootPartitionSpatial q) c (toLp 2 x)) =
      fun x => leafCell (treeRootPartitionSpatial (0 : Fin d → ℤ)) (c - q)
        (toLp 2 (x + (-ofLp (NTSP.intVec q)))) := by
    funext x
    rw [leafCell_treeRootPartition_translateSpatial]
    congr 1
  rw [he, Fourier.timeFourier_translate
    (fun x : Fin d → ℝ => leafCell (treeRootPartitionSpatial (0 : Fin d → ℤ)) (c - q) (toLp 2 x))
    (-ofLp (NTSP.intVec q))]
  simp only [Circle.norm_smul]

/-- Every actual root-input Fourier moment has the same mass after translation. -/
theorem leafFourierMomentMass_treeRootPartition_translateSpatial {d : ℕ} (J : ℕ) (q c : Fin d → ℤ) :
    leafFourierMomentMass J (treeRootPartitionSpatial q) c =
      leafFourierMomentMass J (treeRootPartitionSpatial (0 : Fin d → ℤ)) (c - q) := by
  unfold leafFourierMomentMass
  apply lintegral_congr
  intro ξ
  rw [← ofReal_norm, ← ofReal_norm, norm_mul, norm_mul,
    norm_timeFourier_leafCell_treeRootPartition_translateSpatial]

/-- The complete localized root Fourier moment total is exactly independent of the root cell. -/
theorem leafFourierMomentTotal_treeRootPartition_translateSpatial {d : ℕ} (J : ℕ) (q : Fin d → ℤ) :
    leafFourierMomentTotal J (treeRootPartitionSpatial q) =
      leafFourierMomentTotal J (treeRootPartitionSpatial (0 : Fin d → ℤ)) := by
  unfold leafFourierMomentTotal
  calc
    _ = ∑' c : Fin d → ℤ, leafFourierMomentMass J (treeRootPartitionSpatial (0 : Fin d → ℤ)) (c - q) :=
      tsum_congr (fun c => leafFourierMomentMass_treeRootPartition_translateSpatial J q c)
    _ = _ := (Equiv.subRight q).tsum_eq (fun c =>
      leafFourierMomentMass J (treeRootPartitionSpatial (0 : Fin d → ℤ)) c)

end WaveTurbulence.Flower.IncTop