/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.TreeRootPartition
public import Mathlib.Topology.LocallyFinite

/-! # Uniform finite root-cell overlap and local finite models for the tree extension -/

public section
noncomputable section
open MeasureTheory Set Metric
open scoped Topology

namespace WaveTurbulence.Incoh

/-- Fixed support radius for all translated tree root cutoffs. -/
@[expose] def treeRootCutoffRadius (d : ℕ) : ℝ := treeRootCutoffWidth d * Real.sqrt d

theorem treeRootCutoffRadius_nonneg (d : ℕ) : 0 ≤ treeRootCutoffRadius d := by
  unfold treeRootCutoffRadius treeRootCutoffWidth
  positivity

/-- The actual closed cutoff support has the uniform translated radius. -/
theorem tsupport_treeRootCutoff_subset {d : ℕ} (q : Fin d → ℤ) :
    tsupport (treeRootCutoff q) ⊆ {k : Mom d | ‖k - NTSP.intVec q‖ ≤ treeRootCutoffRadius d} := by
  apply closure_minimal
  · intro k hk
    exact NTSP.norm_le_of_chiScaled_ne_zero
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (two_le_treeRootCutoffWidth d)) hk
  · exact isClosed_le (by fun_prop) continuous_const

/-- The landed finite integer boxes cover each root cutoff support exactly as needed. -/
theorem mem_intBox_of_rootCutoff_support {d : ℕ} (q : Fin d → ℤ) (k : Mom d)
    (hk : k ∈ tsupport (treeRootCutoff q)) : q ∈ ApproxNT.intBox k (treeRootCutoffRadius d) := by
  have hn := tsupport_treeRootCutoff_subset q hk
  change ‖k - NTSP.intVec q‖ ≤ treeRootCutoffRadius d at hn
  apply ApproxNT.mem_intBox
  intro i
  have hi := (PiLp.norm_apply_le (k - NTSP.intVec q) i).trans hn
  simpa only [PiLp.sub_apply, NTSP.intVec_apply, Real.norm_eq_abs, abs_sub_comm] using hi

/-- Uniform dimensional overlap count, independent of the root momentum and source order. -/
theorem card_treeRootCutoff_cover_le {d : ℕ} (k : Mom d) :
    ((ApproxNT.intBox k (treeRootCutoffRadius d)).card : ℝ) ≤ (2 * treeRootCutoffRadius d + 1) ^ d :=
  ApproxNT.card_intBox_le k (treeRootCutoffRadius_nonneg d)

/-- A single finite root-cell set controls the whole unit neighborhood of a momentum. -/
theorem treeRootCutoff_eq_zero_on_ball_of_notMem {d : ℕ} (k₀ : Mom d) (q : Fin d → ℤ)
    (hq : q ∉ ApproxNT.intBox k₀ (treeRootCutoffRadius d + 1))
    {k : Mom d} (hk : k ∈ ball k₀ 1) : treeRootCutoff q k = 0 := by
  by_contra hn
  have hs := tsupport_treeRootCutoff_subset q (subset_closure hn)
  change ‖k - NTSP.intVec q‖ ≤ treeRootCutoffRadius d at hs
  have hdist : ‖k - k₀‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hk
  have hnorm : ‖NTSP.intVec q - k₀‖ ≤ treeRootCutoffRadius d + 1 := by
    have h := norm_add_le (NTSP.intVec q - k) (k - k₀)
    rw [sub_add_sub_cancel] at h
    rw [norm_sub_rev (NTSP.intVec q) k] at h
    linarith only [h, hs, hdist]
  apply hq
  apply ApproxNT.mem_intBox
  intro i
  simpa only [PiLp.sub_apply, NTSP.intVec_apply, Real.norm_eq_abs] using
    (PiLp.norm_apply_le (NTSP.intVec q - k₀) i).trans hnorm

/-- The actual root cutoff family is locally finite, including all support boundary points. -/
theorem locallyFinite_treeRootCutoff {d : ℕ} :
    LocallyFinite (fun q : Fin d → ℤ => tsupport (treeRootCutoff q)) := by
  intro k₀
  refine ⟨ball k₀ 1, ball_mem_nhds _ (by norm_num), ?_⟩
  apply (ApproxNT.intBox k₀ (treeRootCutoffRadius d + 1)).finite_toSet.subset
  intro q hq
  obtain ⟨k, hk, hball⟩ := hq
  have hs := tsupport_treeRootCutoff_subset q hk
  change ‖k - NTSP.intVec q‖ ≤ treeRootCutoffRadius d at hs
  have hdist : ‖k - k₀‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hball
  have hnorm : ‖NTSP.intVec q - k₀‖ ≤ treeRootCutoffRadius d + 1 := by
    have h := norm_add_le (NTSP.intVec q - k) (k - k₀)
    rw [sub_add_sub_cancel] at h
    rw [norm_sub_rev (NTSP.intVec q) k] at h
    linarith only [h, hs, hdist]
  exact ApproxNT.mem_intBox (fun i => by
    simpa only [PiLp.sub_apply, NTSP.intVec_apply, Real.norm_eq_abs] using
      (PiLp.norm_apply_le (NTSP.intVec q - k₀) i).trans hnorm)

end WaveTurbulence.Incoh
