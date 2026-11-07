/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.MinkAux

/-! # Scalars and zero in the order-zero restriction norm -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3.Eng
open WaveTurbulence WaveTurbulence.Fourier MeasureTheory Set
open scoped ENNReal

variable {r : ℕ} {V : Type*}

theorem XNorm00_zero (θ : ℝ) : XNorm00 θ (fun (_ : Fin r → ℝ) (_ : V) => (0 : ℂ)) = 0 := by
  unfold XNorm00
  have hi : ∀ v : V, Integrable (fun t : Fin r → ℝ => (0 : ℂ)) volume := fun v => integrable_zero _ _ _
  rw [ite_eq_left (by exact hi)]
  have : ∀ lam v, timeFT (fun (_ : Fin r → ℝ) (_ : V) => (0 : ℂ)) lam v = 0 := fun lam v => by
    simp [timeFT]
  simp [this]

theorem XNorm00Restr_zero (θ : ℝ) (B : Set (Fin r → ℝ)) (K : Set V) :
    XNorm00Restr θ B K (fun (_ : Fin r → ℝ) (_ : V) => (0 : ℂ)) = 0 := by
  refine le_antisymm ?_ bot_le
  refine le_trans (iInf₂_le (fun (_ : Fin r → ℝ) (_ : V) => (0 : ℂ)) fun _ _ _ _ => rfl) ?_
  rw [XNorm00_zero]

theorem XNorm00Restr_const_mul_le (θ : ℝ) (B : Set (Fin r → ℝ)) (K : Set V) (c : ℂ)
    (f : (Fin r → ℝ) → V → ℂ) :
    XNorm00Restr θ B K (fun t v => c * f t v) ≤ ‖c‖ₑ * XNorm00Restr θ B K f := by
  by_cases hc : c = 0
  · subst hc
    simp only [zero_mul, enorm_zero]
    rw [XNorm00Restr_zero]
  have h0 : ‖c‖ₑ ≠ 0 := by simpa using hc
  have htop : ‖c‖ₑ ≠ ⊤ := enorm_ne_top
  unfold XNorm00Restr
  rw [ENNReal.mul_iInf_of_ne h0 htop]
  refine le_iInf fun G => ?_
  rw [ENNReal.mul_iInf_of_ne h0 htop]
  refine le_iInf fun hag => ?_
  refine le_trans (iInf₂_le (fun t v => c * G t v) fun t ht v hv => ?_) ?_
  · show c * G t v = c * f t v
    rw [hag t ht v hv]
  · have := SumintSigned.XNorm00_smul θ c G
    exact (le_of_eq (by simpa [smul_eq_mul] using this))

end WaveTurbulence.VineEstS3.Eng
