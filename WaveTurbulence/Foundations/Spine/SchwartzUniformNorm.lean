/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.TaylorBoundPrefix
/-! The C1/C2 profile seminorm bounds in TARGET L2065 follow from continuity in Schwartz space. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Set Finset
open scoped ENNReal

theorem exists_uniform_SNormR {d : ℕ} {T : ℝ} {φ : ℝ → SchwartzMap (Mom d) ℝ}
    (hφ : ContinuousOn φ (Icc 0 T)) (A W : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ τ ∈ Icc 0 T, SNormR A W (φ τ) ≤ ENNReal.ofReal C := by
  choose C hC0 hC using fun r : ℕ => WKE.exists_uniform_weighted_bound hφ r (W : ℝ)
  let B : ℝ := 1 + ∑ r ∈ range (A + 1), C r
  have hB : 1 ≤ B := by
    have hs := sum_nonneg (fun r (_ : r ∈ range (A + 1)) => hC0 r)
    dsimp only [B]
    linarith
  refine ⟨B, hB, ?_⟩
  intro τ hτ
  rw [NormBridgeScratch.SNormR_eq_spatialNorm]
  apply WKE.spatialNorm_real_le_of_weighted_derivatives _ (zero_le_one.trans hB)
  intro r hr k
  apply (hC r τ hτ k).trans
  have hs : C r ≤ ∑ s ∈ range (A + 1), C s :=
    single_le_sum (fun s _ => hC0 s) (mem_range.mpr (by omega))
  dsimp only [B]
  linarith

end WaveTurbulence.LGSpine
