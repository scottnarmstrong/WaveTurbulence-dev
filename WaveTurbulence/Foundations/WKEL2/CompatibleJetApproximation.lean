/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.WeightedSobolevForget
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Simultaneous Schwartz approximation of compatible completed jets
-/

public section

noncomputable section

open Filter
open scoped SchwartzMap Topology

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

local instance compatibleNormedBase (s : ℝ) (m : ℕ) :
    NormedAddCommGroup (WeightedSobolevSpace d s m) := inferInstance
local instance compatibleSpaceBase (s : ℝ) (m : ℕ) :
    NormedSpace ℝ (WeightedSobolevSpace d s m) := inferInstance

/-- A common differential jet has consistent restrictions to all smaller orders. -/
@[expose] def IsCompatibleWeightedJets (s : ℝ) (U : ∀ m : ℕ, WeightedSobolevSpace d s m) : Prop :=
  ∀ (m r : ℕ) (hrm : r ≤ m), weightedSobolevForgetCLM s m r hrm (U m) = U r

/-- The actual Schwartz image approximates any completed jet at any positive accuracy. -/
theorem exists_schwartz_jetApprox (s : ℝ) (m : ℕ) (u : WeightedSobolevSpace d s m)
    {ε : ℝ} (hε : 0 < ε) : ∃ f : 𝓢(Mom d, ℝ), ‖schwartzToWeightedSobolevCLM s m f - u‖ < ε := by
  obtain ⟨f, hf⟩ := (denseRange_schwartzToWeightedSobolevCLM (d := d) s m).exists_dist_lt u hε
  refine ⟨f, ?_⟩
  rw [← dist_eq_norm, dist_comm]
  exact hf

/-- High-order approximants also approximate every fixed lower order, without a norm loss. -/
theorem norm_jetApprox_low_le (s : ℝ) {U : ∀ m : ℕ, WeightedSobolevSpace d s m}
    (hU : IsCompatibleWeightedJets s U) (F : ℕ → 𝓢(Mom d, ℝ)) (δ : ℕ → ℝ)
    (hF : ∀ n, ‖schwartzToWeightedSobolevCLM s n (F n) - U n‖ ≤ δ n)
    {m n : ℕ} (hmn : m ≤ n) : ‖schwartzToWeightedSobolevCLM s m (F n) - U m‖ ≤ δ n := by
  have H : weightedSobolevForgetCLM s n m hmn (schwartzToWeightedSobolevCLM s n (F n) - U n) =
      schwartzToWeightedSobolevCLM s m (F n) - U m := by
    rw [map_sub, weightedSobolevForgetCLM_schwartz, hU n m hmn]
  rw [← H]
  exact (norm_weightedSobolevForgetCLM_le s hmn _).trans (hF n)

/-- Successive high-order approximants have small differences in every preceding weighted jet. -/
theorem norm_jetApprox_increment_le (s : ℝ) {U : ∀ m : ℕ, WeightedSobolevSpace d s m}
    (hU : IsCompatibleWeightedJets s U) (F : ℕ → 𝓢(Mom d, ℝ)) (δ : ℕ → ℝ)
    (hF : ∀ n, ‖schwartzToWeightedSobolevCLM s n (F n) - U n‖ ≤ δ n)
    {m n : ℕ} (hmn : m ≤ n) :
    ‖weightedJetCLM s m (F (n + 1) - F n)‖ ≤ δ (n + 1) + δ n := by
  rw [← norm_schwartzToWeightedSobolevCLM, map_sub]
  calc
    _ = ‖(schwartzToWeightedSobolevCLM s m (F (n + 1)) - U m) -
        (schwartzToWeightedSobolevCLM s m (F n) - U m)‖ := by congr 1; abel
    _ ≤ ‖schwartzToWeightedSobolevCLM s m (F (n + 1)) - U m‖ +
        ‖schwartzToWeightedSobolevCLM s m (F n) - U m‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add (norm_jetApprox_low_le s hU F δ hF (hmn.trans (Nat.le_succ n)))
      (norm_jetApprox_low_le s hU F δ hF hmn)

/-- A geometric high-order approximation converges to every fixed completed jet. -/
theorem tendsto_geometric_jetApprox (s : ℝ) {U : ∀ m : ℕ, WeightedSobolevSpace d s m}
    (hU : IsCompatibleWeightedJets s U) (F : ℕ → 𝓢(Mom d, ℝ))
    (hF : ∀ n, ‖schwartzToWeightedSobolevCLM s n (F n) - U n‖ ≤ (1 / 2 : ℝ) ^ n) (m : ℕ) :
    Tendsto (fun n => schwartzToWeightedSobolevCLM s m (F n)) atTop (𝓝 (U m)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (eventually_atTop.2 ⟨m, fun n hn => norm_jetApprox_low_le s hU F _ hF hn⟩)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)

end WaveTurbulence.WKEL2
