/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WaveB.FrozenB1
import Mathlib.Tactic

/-!
# Explicit extension from the allowed output momentum family

Order zero imposes time integrability and no momentum regularity. A
function on any containing output family can therefore be extended by
zero to the ambient type, with no increase in its Fourier norm. The
restriction estimate below uses an actual ambient extension.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.SumintSigned

/-- Extend the output-vector parameter by zero outside a specified family. -/
@[expose] noncomputable def vectorZeroExtension {r : ℕ} {V : Type*} (S : Set V)
    (f : (Fin r → ℝ) → S → ℂ) (t : Fin r → ℝ) (v : V) : ℂ := by
  classical
  exact if h : v ∈ S then f t ⟨v, h⟩ else 0

/-- Every time slice of the explicit zero extension is integrable. -/
theorem integrable_vectorZeroExtension {r : ℕ} {V : Type*} (S : Set V)
    (f : (Fin r → ℝ) → S → ℂ) (hf : ∀ v, Integrable (fun t => f t v)) (v : V) :
    Integrable (fun t => vectorZeroExtension S f t v) := by
  classical
  by_cases hv : v ∈ S
  · simpa only [vectorZeroExtension, dite_eq_left hv] using hf ⟨v, hv⟩
  · simp only [vectorZeroExtension, dite_eq_right hv]
    exact integrable_zero _ _ _

/-- Zero extension in the vector parameter never increases the order-zero norm. -/
theorem XNorm00_vectorZeroExtension_le {r : ℕ} {V : Type*} (θ : ℝ) (S : Set V)
    (f : (Fin r → ℝ) → S → ℂ) :
    XNorm00 θ (vectorZeroExtension S f) ≤ XNorm00 θ f := by
  classical
  by_cases hf : ∀ v, Integrable (fun t => f t v)
  · rw [XNorm00, ite_eq_left (integrable_vectorZeroExtension S f hf), XNorm00, ite_eq_left hf]
    apply lintegral_mono
    intro ξ
    apply mul_le_mul_right
    apply iSup_le
    intro v
    by_cases hv : v ∈ S
    · have he : timeFT (vectorZeroExtension S f) ξ v = timeFT f ξ ⟨v, hv⟩ := by
        unfold timeFT
        apply integral_congr_ae
        exact ae_of_all _ (fun t => by simp [vectorZeroExtension, hv])
      rw [he]
      exact le_iSup (fun w : S => ‖timeFT f ξ w‖ₑ) ⟨v, hv⟩
    · have he : timeFT (vectorZeroExtension S f) ξ v = 0 := by
        simp [timeFT, vectorZeroExtension, hv]
      rw [he, enorm_zero]
      exact bot_le
  · have hr : XNorm00 θ f = ⊤ := by rw [XNorm00, ite_eq_right hf]
    rw [hr]
    exact le_top

/-- A time extension on the output family produces a concrete extension for the exact restriction norm. -/
theorem XNorm00Restr_le_family_extension {r : ℕ} {V : Type*} (θ : ℝ)
    (B : Set (Fin r → ℝ)) (K S : Set V) (hKS : K ⊆ S)
    (F : (Fin r → ℝ) → V → ℂ) (f : (Fin r → ℝ) → S → ℂ)
    (hf : ∀ t ∈ B, ∀ v (hv : v ∈ K), f t ⟨v, hKS hv⟩ = F t v) :
    XNorm00Restr θ B K F ≤ XNorm00 θ f := by
  classical
  apply iInf_le_of_le (vectorZeroExtension S f)
  apply iInf_le_of_le
    (show ∀ t ∈ B, ∀ v ∈ K, vectorZeroExtension S f t v = F t v from ?_)
  · exact XNorm00_vectorZeroExtension_le θ S f
  · intro t ht v hv
    simpa [vectorZeroExtension, hKS hv] using hf t ht v hv

end WaveTurbulence.SumintSigned
