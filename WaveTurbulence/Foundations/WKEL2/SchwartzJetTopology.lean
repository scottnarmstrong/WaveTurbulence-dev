/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.SchwartzSeminormJetBound
public import WaveTurbulence.Foundations.WKEL2.WeightedSobolevCoordinates

/-!
# The actual Schwartz topology equals the topology of all finite weighted L² jets

The equivalence holds for every nonnegative fixed weight exponent. Thus no
change of exponent is needed when reconstructing Schwartz solutions.
-/

public section

noncomputable section

open Filter
open scoped SchwartzMap Topology

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

local instance topologyNormedBase (s : ℝ) (m : ℕ) :
    NormedAddCommGroup (WeightedSobolevSpace d s m) := inferInstance
local instance topologySpaceBase (s : ℝ) (m : ℕ) :
    NormedSpace ℝ (WeightedSobolevSpace d s m) := inferInstance

/-- Convergence in the defining Schwartz topology is equivalent to convergence in every finite jet. -/
theorem tendsto_schwartz_iff_weightedJet_norm {α : Type*} {l : Filter α}
    (s : ℝ) (hs : 0 ≤ s) (u : α → 𝓢(Mom d, ℝ)) (f : 𝓢(Mom d, ℝ)) :
    Tendsto u l (𝓝 f) ↔ ∀ m : ℕ,
      Tendsto (fun x => ‖weightedJetCLM s m (u x - f)‖) l (𝓝 0) := by
  constructor
  · intro hu m
    have H₀ : Tendsto (fun x => u x - f) l (𝓝 0) := by
      simpa only [sub_self] using hu.sub (tendsto_const_nhds (x := f))
    have H := ((weightedJetCLM s m).continuous.tendsto 0).comp H₀
    simpa only [Function.comp_def, map_zero, norm_zero] using H.norm
  · intro hu
    apply ((schwartz_withSeminorms ℝ (Mom d) ℝ).tendsto_nhds u f).2
    rintro ⟨q, n⟩ ε hε
    let C := (2 : ℝ) ^ d * (d : ℝ) ^ q * (d : ℝ) ^ n
    have H : Tendsto (fun x => (C + 1) * ‖weightedJetCLM s (q + n + d) (u x - f)‖) l (𝓝 0) := by
      simpa only [mul_zero] using (hu (q + n + d)).const_mul (C + 1)
    filter_upwards [H.eventually (gt_mem_nhds hε)] with x hx
    change SchwartzMap.seminorm ℝ q n (u x - f) < ε
    have Hs := schwartzSeminorm_le_weightedJet s hs q n (u x - f)
    exact Hs.trans_lt ((mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right zero_le_one) (norm_nonneg _)).trans_lt hx)

/-- Completed jet embeddings induce exactly the same convergence on Schwartz space. -/
theorem tendsto_schwartz_iff_weightedSobolev {α : Type*} {l : Filter α}
    (s : ℝ) (hs : 0 ≤ s) (u : α → 𝓢(Mom d, ℝ)) (f : 𝓢(Mom d, ℝ)) :
    Tendsto u l (𝓝 f) ↔ ∀ m : ℕ,
      Tendsto (fun x => schwartzToWeightedSobolevCLM s m (u x)) l
        (𝓝 (schwartzToWeightedSobolevCLM s m f)) := by
  constructor
  · intro hu m
    exact ((schwartzToWeightedSobolevCLM s m).continuous.tendsto f).comp hu
  · intro hu
    apply (tendsto_schwartz_iff_weightedJet_norm s hs u f).2
    intro m
    have H := ((hu m).sub (tendsto_const_nhds (x := schwartzToWeightedSobolevCLM s m f))).norm
    simpa only [sub_self, norm_zero, ← map_sub, norm_schwartzToWeightedSobolevCLM] using H

end WaveTurbulence.WKEL2
