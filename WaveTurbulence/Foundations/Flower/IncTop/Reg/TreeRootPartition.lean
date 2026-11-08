/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LeafCellProfile
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.RootInputSourceIdentity
public import WaveTurbulence.Foundations.ApproxNT.Cells

/-! Ported by source from C2-B-TOP `Cut2BReg.TreeRootPartition` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.
 # Actual smooth root partition for the tree's lone leaf

The temporary root input is a translated partition function. A fixed
larger translated cutoff equals one on its support and makes the chosen
extension locally finite in the root momentum.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
/-- The actual root partition input, with no imposed momentum decay on the original tree. -/
@[expose] def treeRootPartitionSpatial {d : ℕ} (q : Fin d → ℤ) : Mom d → ℂ :=
  leafCellProfile d (NTSP.intVec q)

/-- The original tree is recovered exactly by the actual root partition. -/
theorem hasSum_treeRootPartitionSpatial {d : ℕ} (k : Mom d) :
    HasSum (fun q : Fin d → ℤ => treeRootPartitionSpatial q k) 1 := by
  simpa only [treeRootPartitionSpatial, leafCellProfile, leafCell, one_mul] using
    hasSum_leafCell (fun _ : Mom d => (1 : ℂ)) k

theorem contDiff_treeRootPartitionSpatial {d : ℕ} (q : Fin d → ℤ) :
    ContDiff ℝ ∞ (treeRootPartitionSpatial q) := contDiff_leafCellProfile d _

theorem hasCompactSupport_treeRootPartitionSpatial {d : ℕ} (q : Fin d → ℤ) :
    HasCompactSupport (treeRootPartitionSpatial q) := hasCompactSupport_leafCellProfile d _

/-- Fixed dimensional width of the larger root cutoff. -/
@[expose] def treeRootCutoffWidthSpatial (d : ℕ) : ℝ := 2 * (1 + Real.sqrt d)

theorem two_le_treeRootCutoffWidthSpatial (d : ℕ) : 2 ≤ treeRootCutoffWidthSpatial d := by
  unfold treeRootCutoffWidthSpatial
  nlinarith [Real.sqrt_nonneg (d : ℝ)]

/-- A translated fixed cutoff, independent of all orders, leaf centers and source inputs. -/
@[expose] def treeRootCutoffSpatial {d : ℕ} (q : Fin d → ℤ) (k : Mom d) : ℂ :=
  NTSP.chiScaled (treeRootCutoffWidthSpatial d) (k - NTSP.intVec q)

theorem contDiff_treeRootCutoffSpatial {d : ℕ} (q : Fin d → ℤ) :
    ContDiff ℝ ∞ (treeRootCutoffSpatial q) :=
  (NTSP.contDiff_chiScaled _).comp (by fun_prop)

/-- The larger root cutoff does not change the actual temporary partition input. -/
theorem treeRootCutoff_mul_partitionSpatial {d : ℕ} (q : Fin d → ℤ) (k : Mom d) :
    treeRootCutoffSpatial q k * treeRootPartitionSpatial q k = treeRootPartitionSpatial q k := by
  by_cases hz : treeRootPartitionSpatial q k = 0
  · rw [hz, mul_zero]
  · have hs := tsupport_leafCellProfile_subset d (NTSP.intVec q) (subset_closure hz)
    have hw : 0 < treeRootCutoffWidthSpatial d :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (two_le_treeRootCutoffWidthSpatial d)
    have he : treeRootCutoffSpatial q k = 1 := by
      rw [treeRootCutoffSpatial, NTSP.chiScaled_apply, Fourier.chi0Tensor_eq_one, Complex.ofReal_one]
      intro i
      change |(treeRootCutoffWidthSpatial d)⁻¹ * (k - NTSP.intVec q) i| ≤ 1 / 2
      rw [abs_mul, abs_inv, abs_of_pos hw, ← div_eq_inv_mul, div_le_iff₀ hw]
      have hi : |(k - NTSP.intVec q) i| ≤ ‖k - NTSP.intVec q‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (k - NTSP.intVec q) i
      unfold treeRootCutoffWidthSpatial
      change ‖k - NTSP.intVec q‖ ≤ Real.sqrt d at hs
      linarith only [hi, hs]
    rw [he, one_mul]

/-- All actual derivatives of the fixed translated root cutoff have uniform dimensional bounds. -/
theorem norm_iteratedFDeriv_treeRootCutoff_leSpatial {d : ℕ} (q : Fin d → ℤ) (j : ℕ) (k : Mom d) :
    ‖iteratedFDeriv ℝ j (treeRootCutoffSpatial q) k‖ ≤ NTSP.chiDerivConst d j :=
  NTSP.norm_iteratedFDeriv_chiScaled_le
    ((by norm_num : (1 : ℝ) ≤ 2).trans (two_le_treeRootCutoffWidthSpatial d)) (NTSP.intVec q) j k

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Exact raw tree source decomposition, with the temporary root input removed by summation. -/
theorem MomentumTreeData.hasSum_sourceTreeKernel_rootPartitionSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (f : Fin m → Mom d → ℂ) (t : Fin 2 → ℝ) (k : Mom d) :
    HasSum (fun q : Fin d → ℤ => treeRootCutoffSpatial q k *
      (MomentumTreeData.sourceTreeKernelSpatial (P := P.withRootInput)) ζ R L γ δ Q I (appendRootInputSpatial f (treeRootPartitionSpatial q)) t k)
      ((MomentumTreeData.sourceTreeKernelSpatial (P := P)) ζ R L γ δ Q I f t k) := by
  have hs := (hasSum_treeRootPartitionSpatial k).mul_left ((MomentumTreeData.sourceTreeKernelSpatial (P := P)) ζ R L γ δ Q I f t k)
  simp only [mul_one] at hs
  convert hs using 1
  funext q
  rw [(MomentumTreeData.sourceTreeKernel_withRootInputSpatial (P := P))]
  calc
    _ = (MomentumTreeData.sourceTreeKernelSpatial (P := P)) ζ R L γ δ Q I f t k * (treeRootCutoffSpatial q k * treeRootPartitionSpatial q k) := by ring
    _ = _ := by rw [treeRootCutoff_mul_partitionSpatial]

end WaveTurbulence.Flower.IncTop