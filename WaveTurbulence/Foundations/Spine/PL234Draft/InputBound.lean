/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.WeightedPointwise
public import WaveTurbulence.Foundations.IncohInst.Regref.SpatialBridge
public import WaveTurbulence.Foundations.WKE.TaylorGateNorm

/-!
# The WKE solution is uniformly bounded in `𝔖^{Λ₁,Λ₂}` (TARGET L1173)

Copied, unchanged in substance, from REGREF scratch `RegrefDraft/Inputs.lean` (wt-torus,
`/home/scott/wt-scratch/regref/src/RegrefDraft/Inputs.lean`, 2026-11-04 07:12), into this namespace:

* `SNormR_schwartz_le`: Schwartz seminorms bound the `𝔖^{Λ₁,Λ₂}` norm;
* `exists_SNormR_bound_of_continuousOn`: a solution continuous into the Schwartz space is uniformly bounded
  on a compact interval.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal SchwartzMap

namespace WaveTurbulence.PL234

variable {d : ℕ}

/-- `‖f‖_{𝔖^{Λ₁,Λ₂}} ≤ 2^{Λ₂} max_{(k,n) ≤ (Λ₂,Λ₁)} ‖f‖_{k,n}` for a Schwartz function. -/
theorem SNormR_schwartz_le (f : 𝓢(Mom d, ℝ)) (Λ₁ Λ₂ : ℕ) :
    SNormR Λ₁ Λ₂ f ≤ ENNReal.ofReal (2 ^ Λ₂ *
      (Finset.Iic (Λ₂, Λ₁)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f) := by
  rw [NormBridgeScratch.SNormR_eq_spatialNorm]
  refine WKE.spatialNorm_real_le_of_weighted_derivatives f (by positivity) fun r hr k => ?_
  rw [Real.rpow_natCast]
  exact SchwartzMap.one_add_le_sup_seminorm_apply (m := (Λ₂, Λ₁)) le_rfl hr f k

/-- **A solution continuous into the Schwartz space is uniformly bounded in `𝔖^{Λ₁,Λ₂}` on a compact interval.** -/
theorem exists_SNormR_bound_of_continuousOn {φ : ℝ → 𝓢(Mom d, ℝ)} {T : ℝ}
    (hφ : ContinuousOn φ (Icc 0 T)) (Λ₁ Λ₂ : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ τ ∈ Icc 0 T, SNormR Λ₁ Λ₂ (φ τ) ≤ ENNReal.ofReal B := by
  set s := Finset.Iic (Λ₂, Λ₁) with hs
  have hb : ∀ m ∈ s, ∃ b : ℝ, ∀ τ ∈ Icc 0 T, SchwartzMap.seminorm ℝ m.1 m.2 (φ τ) ≤ b := by
    intro m _
    have hc : Continuous (SchwartzMap.seminorm ℝ m.1 m.2 : 𝓢(Mom d, ℝ) → ℝ) :=
      (schwartz_withSeminorms ℝ (Mom d) ℝ).continuous_seminorm m
    obtain ⟨b, hb⟩ := (isCompact_Icc.image_of_continuousOn (hc.comp_continuousOn hφ)).bddAbove
    exact ⟨b, fun τ hτ => hb ⟨τ, hτ, rfl⟩⟩
  choose b hb using hb
  refine ⟨2 ^ Λ₂ * ∑ m ∈ s.attach, max (b m.1 m.2) 0, by positivity, fun τ hτ => ?_⟩
  refine (SNormR_schwartz_le (φ τ) Λ₁ Λ₂).trans (ENNReal.ofReal_le_ofReal ?_)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun _ _ => le_max_right _ _) fun m hm => ?_
  · refine le_trans ?_ (Finset.single_le_sum (f := fun m : s => max (b m.1 m.2) 0)
      (fun _ _ => le_max_right _ _) (Finset.mem_attach s ⟨m, hm⟩))
    exact (hb m hm τ hτ).trans (le_max_left _ _)

end WaveTurbulence.PL234
