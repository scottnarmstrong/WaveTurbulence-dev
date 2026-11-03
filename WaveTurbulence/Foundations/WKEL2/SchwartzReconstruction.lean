/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.CompatibleJetApproximation
public import WaveTurbulence.Foundations.WKEL2.SchwartzSeriesConvergence
public import WaveTurbulence.Foundations.WKEL2.SchwartzJetTopology

/-!
# Reconstruction of Schwartz functions from compatible completed jets
-/

public section

noncomputable section

open Filter
open scoped SchwartzMap Topology

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

local instance reconstructNormedBase (s : ℝ) (m : ℕ) :
    NormedAddCommGroup (WeightedSobolevSpace d s m) := inferInstance
local instance reconstructSpaceBase (s : ℝ) (m : ℕ) :
    NormedSpace ℝ (WeightedSobolevSpace d s m) := inferInstance

/-- Geometric approximation at increasing orders gives an absolutely summable Schwartz series. -/
theorem summable_seminorm_jetApprox_increment (s : ℝ) (hs : 0 ≤ s)
    {U : ∀ m : ℕ, WeightedSobolevSpace d s m} (hU : IsCompatibleWeightedJets s U)
    (F : ℕ → 𝓢(Mom d, ℝ))
    (hF : ∀ j, ‖schwartzToWeightedSobolevCLM s j (F j) - U j‖ ≤ (1 / 2 : ℝ) ^ j)
    (q n : ℕ) : Summable (fun j => SchwartzMap.seminorm ℝ q n (F (j + 1) - F j)) := by
  let C := (2 : ℝ) ^ d * (d : ℝ) ^ q * (d : ℝ) ^ n
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hg : Summable (fun j : ℕ => (1 / 2 : ℝ) ^ j) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  apply Summable.of_norm_bounded_eventually_nat
    (((summable_nat_add_iff 1).2 hg).add hg |>.mul_left C)
  filter_upwards [eventually_ge_atTop (q + n + d)] with j hj
  rw [Real.norm_eq_abs, abs_of_nonneg (apply_nonneg _ _)]
  exact (schwartzSeminorm_le_weightedJet s hs q n _).trans
    (mul_le_mul_of_nonneg_left (norm_jetApprox_increment_le s hU F _ hF hj) hC)

/-- Every compatible family of finite completed weighted jets comes from an actual Schwartz function. -/
theorem exists_schwartz_of_compatible_jets (s : ℝ) (hs : 0 ≤ s)
    (U : ∀ m : ℕ, WeightedSobolevSpace d s m) (hU : IsCompatibleWeightedJets s U) :
    ∃ f : 𝓢(Mom d, ℝ), ∀ m, schwartzToWeightedSobolevCLM s m f = U m := by
  classical
  choose F hF using fun j => exists_schwartz_jetApprox s j (U j)
    (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) j)
  have hF' : ∀ j, ‖schwartzToWeightedSobolevCLM s j (F j) - U j‖ ≤ (1 / 2 : ℝ) ^ j :=
    fun j => (hF j).le
  let G : ℕ → 𝓢(Mom d, ℝ) := fun j => F (j + 1) - F j
  have hG : ∀ q n, Summable (fun j => SchwartzMap.seminorm ℝ q n (G j)) :=
    summable_seminorm_jetApprox_increment s hs hU F hF'
  have htel (N : ℕ) : F 0 + ∑ j ∈ Finset.range N, G j = F N := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ← add_assoc, ih]; dsimp [G]; abel
  let f := F 0 + schwartzSeries G hG
  have hlim : Tendsto F atTop (𝓝 f) := by
    have H := (tendsto_const_nhds (x := F 0)).add (tendsto_schwartzSeries_partialSums hG)
    simpa only [htel] using H
  refine ⟨f, fun m => ?_⟩
  exact tendsto_nhds_unique ((schwartzToWeightedSobolevCLM s m).continuous.tendsto f |>.comp hlim)
    (tendsto_geometric_jetApprox s hU F hF' m)

end WaveTurbulence.WKEL2
