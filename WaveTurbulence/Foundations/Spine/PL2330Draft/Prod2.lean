/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL2330Draft.Prod

/-!
# Time products: differentiation under the convolution and the estimate (PL23-30D)

* `conv_deriv`: where the operator envelopes convolve to a finite value, `convΨ` is `C^Λ` and its derivatives
  are the integrals of the derivatives of the integrand;
* `momentumSupNorm_conv_le`: the weighted envelope of `convΨ`;
* **`mixedFourierNorm_mul_le`**: `𝔛^{θ,Λ,a+b}(FG) ≤ 2^θ (2d)^Λ 𝔛^{θ,Λ,a}(F) 𝔛^{θ,Λ,b}(G)` for `G` continuous in time.
-/

@[expose] public section

open MeasureTheory Set Filter Finset
open scoped ENNReal ContDiff

namespace WaveTurbulence.PL2330

open WaveTurbulence.Fourier WaveTurbulence.Regref

variable {r d : ℕ} {Λ : ℕ} {F G : (Fin r → ℝ) → Mom d → ℂ}

section Deriv

variable (GF : Good Λ F) (GG : Good Λ G)

/-- The Leibniz majorant `∑_i C(n,i) E_i(ξ-η) E'_{n-i}(η)` with weights `a`, `b`. -/
noncomputable def levMaj (a b n : ℕ) (ξ η : Fin r → ℝ) : ℝ≥0∞ :=
  ∑ i ∈ range (n + 1), (n.choose i : ℝ≥0∞) * dsup a i (GF.Φ (ξ - η)) * dsup b (n - i) (GG.Φ η)

theorem measurable_levMaj (a b : ℕ) {n : ℕ} (hn : n ≤ Λ) (ξ : Fin r → ℝ) :
    Measurable (levMaj GF GG a b n ξ) := by
  unfold levMaj
  refine Finset.measurable_sum _ fun i hi => ?_
  have hi' : i ≤ Λ := (Nat.lt_succ_iff.mp (mem_range.mp hi)).trans hn
  have hni : n - i ≤ Λ := (Nat.sub_le _ _).trans hn
  exact (measurable_const.mul
    ((measurable_dsup a GF.smooth GF.meas hi').comp (measurable_const.sub measurable_id))).mul
    ((measurable_dsup b GG.smooth GG.meas hni))

theorem lintegral_levMaj_lt_top {ξ : Fin r → ℝ} (hξ : EnvFinite GF GG ξ) {n : ℕ} (hn : n ≤ Λ) :
    ∫⁻ η, levMaj GF GG 0 0 n ξ η < ⊤ := by
  unfold levMaj
  rw [lintegral_finsetSum _ (fun i hi => ?_)]
  swap
  · have hi' : i ≤ Λ := (Nat.lt_succ_iff.mp (mem_range.mp hi)).trans hn
    have hni : n - i ≤ Λ := (Nat.sub_le _ _).trans hn
    exact (measurable_const.mul
      ((measurable_dsup 0 GF.smooth GF.meas hi').comp (measurable_const.sub measurable_id))).mul
      ((measurable_dsup 0 GG.smooth GG.meas hni))
  refine ENNReal.sum_lt_top.2 fun i hi => ?_
  have hi' : i ≤ Λ := (Nat.lt_succ_iff.mp (mem_range.mp hi)).trans hn
  have hni : n - i ≤ Λ := (Nat.sub_le _ _).trans hn
  have := hξ i (n - i) hi' hni
  have e : (fun η => (n.choose i : ℝ≥0∞) * dsup 0 i (GF.Φ (ξ - η)) * dsup 0 (n - i) (GG.Φ η)) =
      fun η => (n.choose i : ℝ≥0∞) * (dsup 0 i (GF.Φ (ξ - η)) * dsup 0 (n - i) (GG.Φ η)) := by
    funext η; ring
  rw [e, lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)]
  exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) this

theorem enorm_le_dsup_zero (i : ℕ) (f : Mom d → ℂ) (k : Mom d) :
    ‖iteratedFDeriv ℝ i f k‖ₑ ≤ dsup 0 i f := by
  unfold dsup
  have := le_iSup (fun k => ENNReal.ofReal (momentumBracket k ^ 0) * ‖iteratedFDeriv ℝ i f k‖ₑ) k
  simpa using this

theorem enorm_convF_le {ξ : Fin r → ℝ} (η : Fin r → ℝ) {n : ℕ} (hn : n ≤ Λ) (k : Mom d) :
    ‖iteratedFDeriv ℝ n (convF GF GG ξ η) k‖ₑ ≤ levMaj GF GG 0 0 n ξ η := by
  have h := enorm_iteratedFDeriv_mul_le (GF.smooth (ξ - η)) (GG.smooth η) k hn
  refine h.trans (Finset.sum_le_sum fun i _ => ?_)
  gcongr
  · exact enorm_le_dsup_zero i _ k
  · exact enorm_le_dsup_zero (n - i) _ k

/-- **Differentiation under the convolution.** -/
theorem conv_deriv {ξ : Fin r → ℝ} (hξ : EnvFinite GF GG ξ) :
    ContDiff ℝ Λ (convΨ GF GG ξ) ∧ ∀ n, n ≤ Λ →
      iteratedFDeriv ℝ n (convΨ GF GG ξ) = fun k => ∫ η, iteratedFDeriv ℝ n (convF GF GG ξ η) k := by
  have hf : ∀ η, ContDiff ℝ Λ (fun k => convF GF GG ξ η k) := fun η => convF_smooth GF GG ξ η
  have hm : ∀ n : ℕ, n ≤ Λ → ∀ e, AEStronglyMeasurable
      (fun η => iteratedFDeriv ℝ n (fun k => convF GF GG ξ η k) e) volume := fun n hn e =>
    (stronglyMeasurable_iteratedFDeriv_param_of_le (f := fun k η => convF GF GG ξ η k) hf
      (fun k => convF_meas GF GG ξ k) n hn e).aestronglyMeasurable
  have hb : ∀ n : ℕ, n ≤ Λ → ∃ B : (Fin r → ℝ) → ℝ, Integrable B volume ∧
      ∀ᵐ η, ∀ e, ‖iteratedFDeriv ℝ n (fun k => convF GF GG ξ η k) e‖ ≤ B η := by
    intro n hn
    have hfin := lintegral_levMaj_lt_top GF GG hξ hn
    refine ⟨fun η => (levMaj GF GG 0 0 n ξ η).toReal,
      integrable_toReal_of_lintegral_ne_top (measurable_levMaj GF GG 0 0 hn ξ).aemeasurable hfin.ne, ?_⟩
    filter_upwards [ae_lt_top (measurable_levMaj GF GG 0 0 hn ξ) hfin.ne] with η hη e
    have h1 := enorm_convF_le GF GG (ξ := ξ) η hn e
    rw [← ofReal_norm] at h1
    exact (ENNReal.ofReal_le_iff_le_toReal hη.ne).1 h1
  have hconv : convΨ GF GG ξ = fun k => ∫ η, convF GF GG ξ η k := rfl
  refine ⟨?_, fun n hn => ?_⟩
  · rw [hconv]
    exact contDiff_integral_param_of_le hf hm hb
  · rw [hconv]
    exact iteratedFDeriv_integral_param_of_le hf hm hb n hn

/-- **The weighted envelope of the convolution.** -/
theorem momentumSupNorm_conv_le {ξ : Fin r → ℝ} (hξ : EnvFinite GF GG ξ) (a b : ℕ) {n : ℕ} (hn : n ≤ Λ)
    (ρ : Fin n → Fin d) :
    momentumSupNorm (a + b) (momentumDerivative ρ (convΨ GF GG ξ)) ≤ ∫⁻ η, levMaj GF GG a b n ξ η := by
  obtain ⟨-, hd⟩ := conv_deriv GF GG hξ
  refine (momentumSupNorm_le_dsup (a + b) ρ _).trans ?_
  unfold dsup
  refine iSup_le fun k => ?_
  rw [hd n hn]
  have hint : ‖∫ η, iteratedFDeriv ℝ n (convF GF GG ξ η) k‖ₑ ≤
      ∫⁻ η, ‖iteratedFDeriv ℝ n (convF GF GG ξ η) k‖ₑ := enorm_integral_le_lintegral_enorm _
  calc ENNReal.ofReal (momentumBracket k ^ (a + b)) * ‖∫ η, iteratedFDeriv ℝ n (convF GF GG ξ η) k‖ₑ
      ≤ ENNReal.ofReal (momentumBracket k ^ (a + b)) * ∫⁻ η, ‖iteratedFDeriv ℝ n (convF GF GG ξ η) k‖ₑ :=
        mul_le_mul_right hint _
    _ = ∫⁻ η, ENNReal.ofReal (momentumBracket k ^ (a + b)) * ‖iteratedFDeriv ℝ n (convF GF GG ξ η) k‖ₑ := by
        rw [lintegral_const_mul']
        exact ENNReal.ofReal_ne_top
    _ ≤ ∫⁻ η, levMaj GF GG a b n ξ η := by
        refine lintegral_mono fun η => ?_
        have h1 : ENNReal.ofReal (momentumBracket k ^ (a + b)) * ‖iteratedFDeriv ℝ n (convF GF GG ξ η) k‖ₑ ≤
            dsup (a + b) n (convF GF GG ξ η) :=
          le_iSup (fun k => ENNReal.ofReal (momentumBracket k ^ (a + b)) *
            ‖iteratedFDeriv ℝ n (convF GF GG ξ η) k‖ₑ) k
        exact h1.trans (dsup_mul_le (GF.smooth (ξ - η)) (GG.smooth η) a b hn)

end Deriv

end WaveTurbulence.PL2330
