/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.EdgeBoxes
public import WaveTurbulence.Foundations.SumintPar.AffinePredecessor
public import WaveTurbulence.Foundations.SumintPar.LocalizationBox
import Mathlib.Tactic

/-!
# The exact sumint datum satisfies the fixed-box localization

The vector identity is obtained from the drafted affine coefficient
identities. Output balls supply coordinate errors at most one.
-/

@[expose] public section
set_option autoImplicit false

open Finset

namespace WaveTurbulence.SumintPar

/-- The predecessor identity, evaluated in a momentum coordinate. -/
theorem alternative_predecessor_coordinate {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hD : D.Admissible A L γ η Dsteps)
    (x : D.S.VIdx → Fin d → ℤ) (E : Fin 4 → Mom d) (v : D.S.VIdx) (j : Fin d) :
    D.ℓVec L x E v j - (D.prev v).elim 0 (fun w => D.ℓVec L x E w j) =
      (∑ w, (D.σk v w : ℝ) * D.kVec L x E w j) +
        ∑ c, (D.σe v c : ℝ) * E c j := by
  have hh := congrArg (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) j) (alternative_predecessor_identity D hD x E v)
  cases hp : D.prev v <;>
    simpa [hp, map_sum, map_sub, map_add, map_smul] using hh

/-- Every nonzero localization profile has twice-coordinate error at most one. -/
theorem profile_coordinate_error {d : ℕ} {a : Fin d → ℤ} {x : Mom d}
    (hx : localizationProfile a x ≠ 0) (j : Fin d) : |2 * x j - (a j : ℝ)| ≤ 1 :=
  (ApproxNT.abs_lt_one_of_thetaMom_ne_zero hx j).le

/-- Actual primary and alternative localization labels obey the fixed edge-box condition. -/
theorem source_edge_labels_mem {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hD : D.Admissible A L γ η Dsteps)
    (x : D.S.VIdx → Fin d → ℤ) (E : Fin 4 → Mom d)
    (a b : D.S.VIdx → Fin d → ℤ)
    (hk : ∀ v, localizationProfile (a v) (D.kVec L x E v) ≠ 0)
    (hl : ∀ v, localizationProfile (b v) (D.ℓVec L x E v) ≠ 0)
    (hE : ∀ c, ‖E c - D.centre c‖ ≤ 1) :
    ∀ v, edgeDifference D.prev b v ∈ Counting.latticeBox
      (edgeCenter (fun v w => (D.σk v w : ℝ)) (fun v c => (D.σe v c : ℝ)) a
        (fun c j => D.centre c j) v) (4 * (D.Λ v : ℝ)) := by
  apply edgeDifference_mem_box D.prev (fun v w => (D.σk v w : ℝ))
    (fun v c => (D.σe v c : ℝ)) (fun v j => D.kVec L x E v j)
    (fun v j => D.ℓVec L x E v j) (fun c j => E c j) (fun c j => D.centre c j)
    a b (fun v => (D.Λ v : ℝ))
  · exact alternative_predecessor_coordinate D hD x E
  · exact fun v j => profile_coordinate_error (hk v) j
  · intro c j
    exact (show |E c j - D.centre c j| ≤ ‖E c - D.centre c‖ from
      PiLp.norm_apply_le (E c - D.centre c) j).trans (hE c)
  · exact fun v j => profile_coordinate_error (hl v) j
  · exact coefficient_mass_le D hD
  · intro v
    exact_mod_cast hD.2.1 v

end WaveTurbulence.SumintPar
