/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.XNormPointwise
/-! Order-zero momentum multipliers and removal of the explicit positive momentum weight.
No higher-derivative Fourier guard is used. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open MeasureTheory Set
open scoped ENNReal

theorem XNorm00_mul_momentum_le {r : ℕ} {V : Type*} (θ : ℝ)
    (M : V → ℂ) (hM : ∀ v, ‖M v‖ ≤ 1) (F : (Fin r → ℝ) → V → ℂ) :
    XNorm00 θ (fun t v => M v * F t v) ≤ XNorm00 θ F := by
  classical
  unfold XNorm00
  by_cases hi : ∀ v, Integrable fun t => F t v
  · rw [ite_eq_left hi, ite_eq_left (fun v => (hi v).const_mul (M v))]
    apply lintegral_mono
    intro ξ
    apply mul_le_mul_right
    apply iSup_le
    intro v
    have hft : timeFT (fun t v => M v * F t v) ξ v = M v * timeFT F ξ v := by
      unfold timeFT
      rw [← integral_const_mul]
      congr 1
      funext t
      ring
    rw [hft, enorm_mul]
    apply le_iSup_of_le v
    have hm : ‖M v‖ₑ ≤ 1 := by
      simpa only [← ofReal_norm, ENNReal.ofReal_one] using (ENNReal.ofReal_le_ofReal (hM v))
    exact (mul_le_mul_left hm ‖timeFT F ξ v‖ₑ).trans_eq (one_mul _)
  · rw [ite_eq_right hi]
    exact le_top

theorem XNorm00Restr_mul_momentum_le {r : ℕ} {V : Type*} (θ : ℝ)
    (T : Set (Fin r → ℝ)) (K : Set V) (M : V → ℂ) (hM : ∀ v, ‖M v‖ ≤ 1)
    (F : (Fin r → ℝ) → V → ℂ) :
    XNorm00Restr θ T K (fun t v => M v * F t v) ≤ XNorm00Restr θ T K F := by
  unfold XNorm00Restr
  refine le_iInf fun G => le_iInf fun hG => ?_
  have h0 : (⨅ (J : (Fin r → ℝ) → V → ℂ)
      (_ : ∀ t ∈ T, ∀ v ∈ K, J t v = M v * F t v), XNorm00 θ J) ≤
      XNorm00 θ (fun t v => M v * G t v) :=
    iInf_le_of_le (fun t v => M v * G t v)
      (iInf_le_of_le (fun t ht v hv => by
        change M v * G t v = M v * F t v
        rw [hG t ht v hv]) le_rfl)
  exact h0.trans (XNorm00_mul_momentum_le θ M hM G)

theorem XNorm00Restr_le_weighted {r d : ℕ} (θ : ℝ) (B : ℕ)
    (T : Set (Fin r → ℝ)) (K : Set (Mom d)) (F : (Fin r → ℝ) → Mom d → ℂ) :
    XNorm00Restr θ T K F ≤ XNorm00Restr θ T K
      (fun t k => ((jbr k ^ B : ℝ) : ℂ) * F t k) := by
  let M : Mom d → ℂ := fun k => (((jbr k ^ B)⁻¹ : ℝ) : ℂ)
  have hm : ∀ k, ‖M k‖ ≤ 1 := by
    intro k
    change ‖(((jbr k ^ B)⁻¹ : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg (jbr_pos k).le _))]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (one_le_jbr k))
  have h := XNorm00Restr_mul_momentum_le θ T K M hm
    (fun t k => ((jbr k ^ B : ℝ) : ℂ) * F t k)
  have he : (fun t k => M k * (((jbr k ^ B : ℝ) : ℂ) * F t k)) = F := by
    funext t k
    dsimp only [M]
    rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (pow_ne_zero _ (jbr_pos k).ne'),
      Complex.ofReal_one, one_mul]
  rw [he] at h
  exact h

/-- Closed-box pointwise control uses only the measurable order-zero Fourier norm. -/
theorem enorm_le_weighted_XNorm00Restr_of_continuous {r d : ℕ} {θ : ℝ}
    (hθ : 0 ≤ θ) (B : ℕ) (T : Set (Fin r → ℝ)) (K : Set (Mom d))
    (F : (Fin r → ℝ) → Mom d → ℂ) (t : Fin r → ℝ) (k : Mom d)
    (ht : t ∈ closure (interior T)) (hk : k ∈ K)
    (hc : Continuous (fun s => F s k)) :
    ‖F t k‖ₑ ≤ XNorm00Restr θ T K
      (fun s k => ((jbr k ^ B : ℝ) : ℂ) * F s k) := by
  have h := enorm_le_mixedRestrictionNorm00_closure_interior hθ T K F t k ht hk hc
  rw [← NormBridgeScratch.XNorm00Restr_eq_mixedRestrictionNorm00] at h
  exact h.trans (XNorm00Restr_le_weighted θ B T K F)

end WaveTurbulence.LGSpine
