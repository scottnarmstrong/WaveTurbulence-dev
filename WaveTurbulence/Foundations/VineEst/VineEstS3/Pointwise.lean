/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.TimePointwise
public import WaveTurbulence.Foundations.Sumint.TimeBridge
public import WaveTurbulence.Foundations.XChain.SNormPointwise
public import WaveTurbulence.Foundations.VineEst.VineEstS3.XNormLe

/-! # Pointwise values from the snapshot-9 restriction norms (B3)

A continuous (in time) function `F(·, v)` with finite restriction norm is bounded pointwise, at every
point of `closure (interior B)` and every `v ∈ K`, by its `XNorm00Restr` (hence by `XNormRestr`).
This is the evaluation of the weights of `K*` on the diagonal of the parent clocks (B3 of V5).
The proofs are the LG-SPINE ones (`XNormPointwise`), adapted to the snapshot-9 `XNorm` (F80 guard).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS3
open WaveTurbulence MeasureTheory Set
open scoped ENNReal

/-- The order-zero restriction norm is dominated by the restriction norm at any orders. -/
theorem XNorm00Restr_le_XNormRestr {r d : ℕ} (θ : ℝ) (A B : ℕ)
    (T : Set (Fin r → ℝ)) (K : Set (Mom d)) (F : (Fin r → ℝ) → Mom d → ℂ) :
    XNorm00Restr θ T K F ≤ XNormRestr θ A B T K F := by
  unfold XNorm00Restr XNormRestr
  apply le_iInf
  intro G
  apply le_iInf
  intro hG
  have h0 : (⨅ (H : (Fin r → ℝ) → Mom d → ℂ)
      (_ : ∀ t ∈ T, ∀ k ∈ K, H t k = F t k), XNorm00 θ H) ≤ XNorm00 θ G :=
    iInf_le_of_le G (iInf_le_of_le hG le_rfl)
  exact h0.trans (XNorm00_le_XNorm θ A B G)

/-- **Pointwise bound (B3).** At every point `t` of `closure (interior T)` and every `v ∈ K`, a
function that is continuous in time at `v` is bounded by its order-zero restriction norm. -/
theorem enorm_le_XNorm00Restr_of_continuous {r : ℕ} {V : Type*} {θ : ℝ} (hθ : 0 ≤ θ)
    (T : Set (Fin r → ℝ)) (K : Set V) (F : (Fin r → ℝ) → V → ℂ)
    (t : Fin r → ℝ) (v : V) (ht : t ∈ closure (interior T)) (hv : v ∈ K)
    (hc : Continuous (fun s => F s v)) : ‖F t v‖ₑ ≤ XNorm00Restr θ T K F := by
  rw [NormBridgeScratch.XNorm00Restr_eq_mixedRestrictionNorm00]
  exact LGSpine.enorm_le_mixedRestrictionNorm00_closure_interior hθ T K F t v ht hv hc

/-- Pointwise bound by the restriction norm `XNormRestr θ Λ₁ Λ₂`. -/
theorem enorm_le_XNormRestr_of_continuous {r d : ℕ} {θ : ℝ} (hθ : 0 ≤ θ) (A B : ℕ)
    (T : Set (Fin r → ℝ)) (K : Set (Mom d)) (F : (Fin r → ℝ) → Mom d → ℂ)
    (t : Fin r → ℝ) (k : Mom d) (ht : t ∈ closure (interior T)) (hk : k ∈ K)
    (hc : Continuous (fun s => F s k)) : ‖F t k‖ₑ ≤ XNormRestr θ A B T K F :=
  (enorm_le_XNorm00Restr_of_continuous hθ T K F t k ht hk hc).trans
    (XNorm00Restr_le_XNormRestr θ A B T K F)

end WaveTurbulence.VineEstS3
