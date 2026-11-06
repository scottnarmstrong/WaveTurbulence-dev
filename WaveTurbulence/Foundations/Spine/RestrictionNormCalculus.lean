/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Fourier.Norm00VBasic
public import WaveTurbulence.Foundations.Fourier.Norm00VRestriction
public import WaveTurbulence.Foundations.Fourier.TimeProduct
/-! Finite sums and separated factors in the literal extension-infimum Fourier norm. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

theorem mixedRestrictionNorm00_add_le_ambient {r : ℕ} {V : Type*} (θ : ℝ)
    (B : Set (Fin r → ℝ)) (K : Set V) (F G : (Fin r → ℝ) → V → ℂ) :
    mixedRestrictionNorm00 θ B K (fun t v => F t v + G t v) ≤
      mixedRestrictionNorm00 θ B K (fun t v => F t v) +
      mixedRestrictionNorm00 θ B K (fun t v => G t v) := by
  unfold mixedRestrictionNorm00
  apply ENNReal.le_iInf₂_add_iInf₂
  intro H hH I hI
  have h := mixedRestrictionNorm00_le_extension (θ := θ) (fun t v => H t v + I t v)
    (B := B) (K := K) (F := fun t v => F t v + G t v)
    (fun t v => by rw [hH t v, hI t v])
  exact h.trans (mixedFourierNorm00_add_le θ H I)

theorem mixedRestrictionNorm00_finsetSum_le {r : ℕ} {V ι : Type*} (θ : ℝ)
    (B : Set (Fin r → ℝ)) (K : Set V) (s : Finset ι)
    (F : ι → (Fin r → ℝ) → V → ℂ) :
    mixedRestrictionNorm00 θ B K (fun t v => ∑ i ∈ s, F i t v) ≤
      ∑ i ∈ s, mixedRestrictionNorm00 θ B K (fun t v => F i t v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty, mixedRestrictionNorm00_zero, le_refl]
  | @insert i s hi ih =>
    simp only [sum_insert hi]
    exact (mixedRestrictionNorm00_add_le_ambient θ B K (F i)
      (fun t v => ∑ j ∈ s, F j t v)).trans (add_le_add_right ih _)

/-- A bounded factor independent of time pulls out of the Fourier integral and the vector supremum. -/
theorem mixedFourierNorm00_separated_le {r : ℕ} {V : Type*} (θ : ℝ)
    (J : (Fin r → ℝ) → ℂ) (M : V → ℂ) {C : ℝ} (hC : 0 < C)
    (hM : ∀ v, ‖M v‖ ≤ C) :
    mixedFourierNorm00 θ (fun t v => M v * J t) ≤ ENNReal.ofReal C * timeFourierNorm θ J := by
  classical
  by_cases hi : Integrable J
  · have hprod : ∀ v, Integrable (fun t => M v * J t) := fun v => hi.const_mul (M v)
    rw [mixedFourierNorm00_eq_lintegral hprod, timeFourierNorm_eq_lintegral hi]
    calc
      _ ≤ ∫⁻ ξ, ENNReal.ofReal C * (timeWeight θ ξ * ‖timeFourier J ξ‖ₑ) := by
        apply lintegral_mono
        intro ξ
        have hb : mixedFourierEnvelope00 (fun t v => M v * J t) ξ ≤
            ENNReal.ofReal C * ‖timeFourier J ξ‖ₑ := by
          apply iSup_le
          intro v
          have he := congrFun (timeFourier_smul (M v) J) ξ
          simp only [smul_eq_mul] at he
          rw [he, enorm_mul]
          apply mul_le_mul_left
          simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal (hM v)
        exact (mul_le_mul_right hb (timeWeight θ ξ)).trans_eq (by ring)
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  · rw [timeFourierNorm_of_not_integrable hi, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hC))]
    exact le_top

theorem mixedRestrictionNorm00_congr_ambient {r : ℕ} {V : Type*} (θ : ℝ)
    (B : Set (Fin r → ℝ)) (K : Set V) (F G : (Fin r → ℝ) → V → ℂ)
    (h : ∀ t ∈ B, ∀ v ∈ K, F t v = G t v) :
    mixedRestrictionNorm00 θ B K (fun t v => F t v) =
      mixedRestrictionNorm00 θ B K (fun t v => G t v) := by
  have he : (fun (t : B) (v : K) => F t v) = (fun (t : B) (v : K) => G t v) :=
    funext fun t => funext fun v => h t t.2 v v.2
  rw [he]

theorem mixedRestrictionNorm00_mono_time {r : ℕ} {V : Type*} {θ θ' : ℝ}
    (hθ : θ ≤ θ') (B : Set (Fin r → ℝ)) (K : Set V) (F : (Fin r → ℝ) → V → ℂ) :
    mixedRestrictionNorm00 θ B K (fun t v => F t v) ≤
      mixedRestrictionNorm00 θ' B K (fun t v => F t v) := by
  unfold mixedRestrictionNorm00
  apply le_iInf
  intro G
  apply le_iInf
  intro hG
  exact (mixedRestrictionNorm00_le_extension G hG).trans (mixedFourierNorm00_mono hθ G)

/-- A separated approximation term is estimated directly through agreeing extensions.
No temporal continuity of J or of the chosen representative is postulated. -/
theorem mixedRestrictionNorm00_separated_le {r : ℕ} {V : Type*} (θ : ℝ)
    (B : Set (Fin r → ℝ)) (K : Set V) (J : (Fin r → ℝ) → ℂ) (M : V → ℂ)
    {C : ℝ} (hC : 0 < C) (hM : ∀ v, ‖M v‖ ≤ C) :
    mixedRestrictionNorm00 θ B K (fun t v => J t * M v) ≤
      ENNReal.ofReal C * mixedRestrictionNorm00 (V := Unit) θ B Set.univ (fun t _ => J t) := by
  have hC0 : ENNReal.ofReal C ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hC)
  unfold mixedRestrictionNorm00
  rw [ENNReal.mul_iInf_of_ne hC0 ENNReal.ofReal_ne_top]
  apply le_iInf
  intro G
  rw [ENNReal.mul_iInf_of_ne hC0 ENNReal.ofReal_ne_top]
  apply le_iInf
  intro hG
  have h := mixedRestrictionNorm00_le_extension (θ := θ) (fun t v => M v * G t ())
    (B := B) (K := K) (F := fun t v => J t * M v)
    (fun t v => by rw [hG t ⟨(), Set.mem_univ ()⟩]; exact mul_comm _ _)
  exact h.trans ((mixedFourierNorm00_separated_le θ (fun t => G t ()) M hC hM).trans
    (mul_le_mul_right (timeFourierNorm_slice_le_mixedFourierNorm00 θ G ()) _))

end WaveTurbulence.LGSpine
