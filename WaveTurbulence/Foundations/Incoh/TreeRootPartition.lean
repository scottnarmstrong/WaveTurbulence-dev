/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LeafCellProfile
public import WaveTurbulence.Foundations.Incoh.RootInputSourceIdentity
public import WaveTurbulence.Foundations.ApproxNT.Cells

/-! # Actual smooth root partition for the tree's lone leaf

The temporary root input is a translated partition function. A fixed
larger translated cutoff equals one on its support and makes the chosen
extension locally finite in the root momentum.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace WaveTurbulence.Incoh

/-- The actual root partition input, with no imposed momentum decay on the original tree. -/
@[expose] def treeRootPartition {d : ℕ} (q : Fin d → ℤ) : Mom d → ℂ :=
  leafCellProfile d (NTSP.intVec q)

/-- The original tree is recovered exactly by the actual root partition. -/
theorem hasSum_treeRootPartition {d : ℕ} (k : Mom d) :
    HasSum (fun q : Fin d → ℤ => treeRootPartition q k) 1 := by
  simpa only [treeRootPartition, leafCellProfile, leafCell, one_mul] using
    hasSum_leafCell (fun _ : Mom d => (1 : ℂ)) k

theorem contDiff_treeRootPartition {d : ℕ} (q : Fin d → ℤ) :
    ContDiff ℝ ∞ (treeRootPartition q) := contDiff_leafCellProfile d _

theorem hasCompactSupport_treeRootPartition {d : ℕ} (q : Fin d → ℤ) :
    HasCompactSupport (treeRootPartition q) := hasCompactSupport_leafCellProfile d _

/-- Fixed dimensional width of the larger root cutoff. -/
@[expose] def treeRootCutoffWidth (d : ℕ) : ℝ := 2 * (1 + Real.sqrt d)

theorem two_le_treeRootCutoffWidth (d : ℕ) : 2 ≤ treeRootCutoffWidth d := by
  unfold treeRootCutoffWidth
  nlinarith [Real.sqrt_nonneg (d : ℝ)]

/-- A translated fixed cutoff, independent of all orders, leaf centers and source inputs. -/
@[expose] def treeRootCutoff {d : ℕ} (q : Fin d → ℤ) (k : Mom d) : ℂ :=
  NTSP.chiScaled (treeRootCutoffWidth d) (k - NTSP.intVec q)

theorem contDiff_treeRootCutoff {d : ℕ} (q : Fin d → ℤ) :
    ContDiff ℝ ∞ (treeRootCutoff q) :=
  (NTSP.contDiff_chiScaled _).comp (by fun_prop)

/-- The larger root cutoff does not change the actual temporary partition input. -/
theorem treeRootCutoff_mul_partition {d : ℕ} (q : Fin d → ℤ) (k : Mom d) :
    treeRootCutoff q k * treeRootPartition q k = treeRootPartition q k := by
  by_cases hz : treeRootPartition q k = 0
  · rw [hz, mul_zero]
  · have hs := tsupport_leafCellProfile_subset d (NTSP.intVec q) (subset_closure hz)
    have hw : 0 < treeRootCutoffWidth d :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (two_le_treeRootCutoffWidth d)
    have he : treeRootCutoff q k = 1 := by
      rw [treeRootCutoff, NTSP.chiScaled_apply, Fourier.chi0Tensor_eq_one, Complex.ofReal_one]
      intro i
      change |(treeRootCutoffWidth d)⁻¹ * (k - NTSP.intVec q) i| ≤ 1 / 2
      rw [abs_mul, abs_inv, abs_of_pos hw, ← div_eq_inv_mul, div_le_iff₀ hw]
      have hi : |(k - NTSP.intVec q) i| ≤ ‖k - NTSP.intVec q‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (k - NTSP.intVec q) i
      unfold treeRootCutoffWidth
      change ‖k - NTSP.intVec q‖ ≤ Real.sqrt d at hs
      linarith only [hi, hs]
    rw [he, one_mul]

/-- All actual derivatives of the fixed translated root cutoff have uniform dimensional bounds. -/
theorem norm_iteratedFDeriv_treeRootCutoff_le {d : ℕ} (q : Fin d → ℤ) (j : ℕ) (k : Mom d) :
    ‖iteratedFDeriv ℝ j (treeRootCutoff q) k‖ ≤ NTSP.chiDerivConst d j :=
  NTSP.norm_iteratedFDeriv_chiScaled_le
    ((by norm_num : (1 : ℝ) ≤ 2).trans (two_le_treeRootCutoffWidth d)) (NTSP.intVec q) j k

/-- Exact raw tree source decomposition, with the temporary root input removed by summation. -/
theorem MomentumTreeData.hasSum_sourceTreeKernel_rootPartition {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (f : Fin m → Mom d → ℂ) (t : Fin 2 → ℝ) (k : Mom d) :
    HasSum (fun q : Fin d → ℤ => treeRootCutoff q k *
      P.withRootInput.sourceTreeKernel ζ R L γ δ Q I (appendRootInput f (treeRootPartition q)) t k)
      (P.sourceTreeKernel ζ R L γ δ Q I f t k) := by
  have hs := (hasSum_treeRootPartition k).mul_left (P.sourceTreeKernel ζ R L γ δ Q I f t k)
  simp only [mul_one] at hs
  convert hs using 1
  funext q
  rw [P.sourceTreeKernel_withRootInput]
  calc
    _ = P.sourceTreeKernel ζ R L γ δ Q I f t k * (treeRootCutoff q k * treeRootPartition q k) := by ring
    _ = _ := by rw [treeRootCutoff_mul_partition]

end WaveTurbulence.Incoh
