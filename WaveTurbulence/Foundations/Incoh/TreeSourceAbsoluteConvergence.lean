/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SourceAbsoluteConvergence
public import WaveTurbulence.Foundations.Incoh.TreeAugmentedInputBounds
public import WaveTurbulence.Foundations.Incoh.CoupleLinkCellLocalization

/-! # Absolute convergence of the actual tree lattice weight with its lone input omitted -/

public section
noncomputable section
open scoped Classical
namespace WaveTurbulence.Incoh

/-- The omitted root input causes no convergence hypothesis: choose a nonzero smooth partition
value at the fixed root, prove augmented convergence, and cancel that scalar. -/
theorem MomentumTreeData.summable_norm_treeSourceLeafWeight_lattice {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (hd : 0 < d)
    (f : Fin m → Mom d → ℂ) {B L : ℝ}
    (hL : 1 ≤ L) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (k : Mom d) :
    Summable (fun p : (Fin n × Fin 2) → Fin d → ℤ =>
      ‖P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j)))‖) := by
  have hex : ∃ q : Fin d → ℤ, treeRootPartition q k ≠ 0 := by
    by_contra hn
    have hz : ∀ q : Fin d → ℤ, treeRootPartition q k = 0 := by simpa using hn
    have hs := (hasSum_treeRootPartition k).tsum_eq
    simp only [hz, tsum_zero] at hs
    exact zero_ne_one hs
  obtain ⟨q, hq⟩ := hex
  obtain ⟨Bq, hBq, hfq⟩ := exists_spatialNorm_bound_appendRootPartition f hf q
  obtain ⟨C, _, hloc⟩ := exists_uniform_couple_link_cell_localization d hd
  choose S hScard hcover using fun c => hloc n (m + 1) w P.withRootInput P.withRootInput_all_leaves c
  have hs := P.withRootInput.summable_norm_sourceLeafWeight_lattice
    (appendRootInput f (treeRootPartition q)) S hcover hScard hL hK hM hBq.le hfq k
  simp only [P.sourceLeafWeight_withRootInput, norm_mul] at hs
  exact (summable_mul_right_iff (norm_ne_zero_iff.mpr hq)).mp hs

end WaveTurbulence.Incoh
