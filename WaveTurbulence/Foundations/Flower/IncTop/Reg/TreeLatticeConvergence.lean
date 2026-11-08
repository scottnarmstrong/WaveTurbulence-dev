/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.TreeRootUpperAgreement

/-! Ported by source from C2-B-TOP `Cut2BReg.TreeLatticeConvergence` (sha256 in COPIED-SHA256SUMS); mechanical edits only.
 # Raw tree absolute lattice convergence without an external-root decay premise -/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- Remove one nonzero temporary root profile from the absolute source lattice sum.
Only the source profile bounds and its structural cell cover are assumed. -/
theorem MomentumTreeData.summable_norm_treeLeafWeight_lattice
    {d n m w K M : ℕ} (P : MomentumTreeData n m w) (f : Fin m → Mom d → ℂ)
    (S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, P.withRootInput.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin n × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c)
    {C B L : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n)
    (hL : 1 ≤ L) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (k : Mom d) :
    Summable (fun p : (Fin n × Fin 2) → Fin d → ℤ =>
      ‖P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j)))‖) := by
  classical
  have hex : ∃ q : Fin d → ℤ, treeRootPartitionSpatial q k ≠ 0 := by
    by_contra hh
    push Not at hh
    have hs := (hasSum_treeRootPartitionSpatial k).tsum_eq
    simp only [hh, tsum_zero] at hs
    exact zero_ne_one hs
  obtain ⟨q, hq⟩ := hex
  obtain ⟨Bq, hBq, hfq⟩ := exists_spatialNorm_bound_appendRootPartitionSpatial f hf q
  have hs := (MomentumTreeData.summable_norm_sourceLeafWeight_latticeSpatial (P := P.withRootInput))
    (appendRootInputSpatial f (treeRootPartitionSpatial q)) S hcover hS hL hK hM hBq.le hfq k
  simp_rw [(MomentumTreeData.sourceLeafWeight_withRootInputSpatial (P := P)), norm_mul] at hs
  exact (summable_mul_right_iff (norm_ne_zero_iff.mpr hq)).mp hs

end WaveTurbulence.Flower.IncTop