/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL2330Draft.Mult

/-!
# `𝔛^{θ,Λ,a+b}(c F) ≤ (2d)^Λ ‖c‖_{𝔖^{Λ,a}} 𝔛^{θ,Λ,b}(F)` (PL23-30D)

* `mixedFourierNorm_mul_momentum_le`: `c(k)` independent of time, smooth of order `Λ ≥ 1`;
* `restr_mul_momentum_le`: the restriction norm version with real bounds.
-/

@[expose] public section

open MeasureTheory Set Filter Finset
open scoped ENNReal ContDiff

namespace WaveTurbulence.PL2330

open WaveTurbulence.Fourier WaveTurbulence.Regref

variable {r d : ℕ}

/-- The Leibniz constant `(2d)^Λ`. -/
noncomputable def cLeib (d Λ : ℕ) : ℝ := ((2 : ℝ) * d) ^ Λ

theorem one_le_cLeib {d : ℕ} (hd : 1 ≤ d) (Λ : ℕ) : 1 ≤ cLeib d Λ := by
  unfold cLeib
  have : (1 : ℝ) ≤ 2 * d := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  exact one_le_pow₀ this

theorem cLeib_nonneg (d Λ : ℕ) : 0 ≤ cLeib d Λ := by
  unfold cLeib
  positivity

theorem pow_le_ofReal_cLeib {d : ℕ} (hd : 1 ≤ d) {n Λ : ℕ} (hn : n ≤ Λ) :
    ((d : ℝ≥0∞) + d) ^ n ≤ ENNReal.ofReal (cLeib d Λ) := by
  have h2 : (d : ℝ≥0∞) + d = ENNReal.ofReal (2 * d) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast]
    simp [two_mul]
  have h1 : 1 ≤ (d : ℝ≥0∞) + d := by
    have : (1 : ℝ≥0∞) ≤ d := by exact_mod_cast hd
    exact this.trans le_self_add
  unfold cLeib
  rw [ENNReal.ofReal_pow (by positivity), ← h2]
  exact pow_right_mono₀ h1 hn

/-- The sum of the weighted envelopes over the words of length `m`, integrated. -/
theorem lintegral_envSum_le {θ : ℝ} {Λ Λ₂ : ℕ} {F : (Fin r → ℝ) → Mom d → ℂ} (G : Good Λ F)
    (hadm : MixedFourierAdmissible Λ F) {m : ℕ} (hm : m ≤ Λ) :
    ∫⁻ ξ, timeWeight θ ξ * ∑ w : Fin m → Fin d, momentumSupNorm Λ₂ (momentumDerivative w (G.Φ ξ)) ≤
      (d : ℝ≥0∞) ^ m * mixedFourierNorm θ Λ Λ₂ F := by
  simp only [Finset.mul_sum]
  rw [lintegral_finsetSum _ (f := fun (w : Fin m → Fin d) ξ => timeWeight θ ξ *
    momentumSupNorm Λ₂ (momentumDerivative w (G.Φ ξ)))
    (fun w _ => (timeWeight_measurable θ).mul (G.env_meas Λ₂ hm w))]
  calc ∑ w : Fin m → Fin d, ∫⁻ ξ, timeWeight θ ξ * momentumSupNorm Λ₂ (momentumDerivative w (G.Φ ξ))
      ≤ ∑ _w : Fin m → Fin d, mixedFourierNorm θ Λ Λ₂ F := Finset.sum_le_sum fun w _ => G.nInt_le hadm hm w
    _ = (d : ℝ≥0∞) ^ m * mixedFourierNorm θ Λ Λ₂ F := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
          nsmul_eq_mul]
        simp

/-- **Momentum multipliers**, for a finite-norm family. -/
theorem mixedFourierNorm_mul_momentum_le {Λ : ℕ} (hΛ : Λ ≠ 0) (hd : 1 ≤ d) (θ : ℝ) (a b : ℕ)
    {c : Mom d → ℂ} (hc : ContDiff ℝ Λ c) {F : (Fin r → ℝ) → Mom d → ℂ}
    (hF : mixedFourierNorm θ Λ b F < ⊤) :
    mixedFourierNorm θ Λ (a + b) (fun t k => c k * F t k) ≤
      ENNReal.ofReal (cLeib d Λ) * spatialNorm Λ a c * mixedFourierNorm θ Λ b F := by
  obtain ⟨G⟩ := exists_good hΛ hF
  have hadF := admissible_of_lt_top hF
  have hsmF := hadF.2.resolve_left hΛ
  have hFT : ∀ ξ, mixedTimeFourier (fun t k => c k * F t k) ξ = fun k => c k * mixedTimeFourier F ξ k := by
    intro ξ
    funext k
    unfold mixedTimeFourier
    have := congrFun (timeFourier_smul (c k) (fun t => F t k)) ξ
    simpa [smul_eq_mul] using this
  have hadS : MixedFourierAdmissible Λ (fun t k => c k * F t k) := by
    refine ⟨fun k => (hadF.1 k).const_mul (c k), Or.inr ?_⟩
    filter_upwards [hsmF] with ξ h1
    rw [hFT ξ]
    exact hc.mul h1
  set S := spatialNorm Λ a c with hS
  refine mixedFourierNorm_le_of_bound (θ := θ) (Λ₂ := a + b) hadS
    (fun n ρ ξ => ∑ i ∈ range (n + 1), (n.choose i : ℝ≥0∞) * ((d : ℝ≥0∞) ^ i * S) *
      ∑ w : Fin (n - i) → Fin d, momentumSupNorm b (momentumDerivative w (G.Φ ξ))) ?_ ?_
  · intro n hn ρ
    filter_upwards [hsmF, G.ae] with ξ h1 h2
    rw [hFT ξ]
    have h2' : mixedTimeFourier F ξ = G.Φ ξ := h2.symm
    rw [h2'] at h1 ⊢
    refine (momentumSupNorm_le_dsup (a + b) ρ _).trans ((dsup_mul_le hc h1 a b hn).trans ?_)
    refine Finset.sum_le_sum fun i hi => ?_
    have hiΛ : i ≤ Λ := (Nat.lt_succ_iff.mp (mem_range.mp hi)).trans hn
    have hniΛ : n - i ≤ Λ := (Nat.sub_le _ _).trans hn
    have h3 := dsup_le_spatialNorm (a := a) hc hiΛ
    have h4 := dsup_le_sum_words b (n - i) (G.Φ ξ)
    exact mul_le_mul' (mul_le_mul_right h3 _) h4
  · intro n hn ρ
    set T : ℕ → (Fin r → ℝ) → ℝ≥0∞ := fun i ξ => (n.choose i : ℝ≥0∞) * ((d : ℝ≥0∞) ^ i * S) *
      ∑ w : Fin (n - i) → Fin d, momentumSupNorm b (momentumDerivative w (G.Φ ξ)) with hT
    have hTm : ∀ i ∈ range (n + 1), Measurable fun ξ => timeWeight θ ξ * T i ξ := by
      intro i hi
      have hniΛ : n - i ≤ Λ := (Nat.sub_le _ _).trans hn
      refine (timeWeight_measurable θ).mul (Measurable.const_mul ?_ _)
      exact Finset.measurable_sum _ fun w _ => G.env_meas b hniΛ w
    have hterm : ∀ i ∈ range (n + 1), ∫⁻ ξ, timeWeight θ ξ * T i ξ ≤
        (n.choose i : ℝ≥0∞) * ((d : ℝ≥0∞) ^ i * S) * ((d : ℝ≥0∞) ^ (n - i) *
          mixedFourierNorm θ Λ b F) := by
      intro i hi
      have hniΛ : n - i ≤ Λ := (Nat.sub_le _ _).trans hn
      have hm := lintegral_envSum_le (θ := θ) (Λ₂ := b) G hadF hniΛ
      have hmeas : Measurable fun ξ => timeWeight θ ξ *
          ∑ w : Fin (n - i) → Fin d, momentumSupNorm b (momentumDerivative w (G.Φ ξ)) :=
        (timeWeight_measurable θ).mul (Finset.measurable_sum _ fun w _ => G.env_meas b hniΛ w)
      calc ∫⁻ ξ, timeWeight θ ξ * T i ξ
          = (n.choose i : ℝ≥0∞) * ((d : ℝ≥0∞) ^ i * S) * ∫⁻ ξ, timeWeight θ ξ *
            ∑ w : Fin (n - i) → Fin d, momentumSupNorm b (momentumDerivative w (G.Φ ξ)) := by
            rw [← lintegral_const_mul _ hmeas]
            refine lintegral_congr fun ξ => ?_
            simp only [hT]
            ring
        _ ≤ _ := mul_le_mul_right hm _
    have hsplit : ∫⁻ ξ, timeWeight θ ξ * ∑ i ∈ range (n + 1), T i ξ =
        ∑ i ∈ range (n + 1), ∫⁻ ξ, timeWeight θ ξ * T i ξ := by
      simp only [Finset.mul_sum]
      exact lintegral_finsetSum _ hTm
    rw [hsplit]
    refine (Finset.sum_le_sum hterm).trans ?_
    have hbin : ∑ i ∈ range (n + 1), (n.choose i : ℝ≥0∞) * ((d : ℝ≥0∞) ^ i * S) * ((d : ℝ≥0∞) ^ (n - i) *
          mixedFourierNorm θ Λ b F) = ((d : ℝ≥0∞) + d) ^ n * S * mixedFourierNorm θ Λ b F := by
      rw [add_pow, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hbin]
    gcongr
    exact pow_le_ofReal_cLeib hd hn

/-- If the spatial norm of `c` vanishes then `c = 0`. -/
theorem eq_zero_of_spatialNorm_eq_zero {Λ a : ℕ} {c : Mom d → ℂ} (hc : ContDiff ℝ Λ c)
    (h : spatialNorm Λ a c = 0) : c = 0 := by
  funext k
  have h0 : momentumSupNorm a (momentumDerivative (Fin.elim0 : Fin 0 → Fin d) c) ≤ spatialNorm Λ a c := by
    unfold spatialNorm
    simp only [hc, or_true, ↓reduceIte]
    exact le_iSup₂_of_le 0 (Nat.zero_le _) (le_iSup (fun ρ : Fin 0 → Fin d =>
      momentumSupNorm a (momentumDerivative ρ c)) Fin.elim0)
  rw [h, nonpos_iff_eq_zero, momentumDerivative_zero] at h0
  have hk : ENNReal.ofReal (momentumBracket k ^ a) * ‖c k‖ₑ ≤ 0 := h0 ▸
    le_iSup (fun k => ENNReal.ofReal (momentumBracket k ^ a) * ‖c k‖ₑ) k
  rw [nonpos_iff_eq_zero, mul_eq_zero] at hk
  rcases hk with hk | hk
  · exfalso
    have hpos : 0 < momentumBracket k ^ a := pow_pos (Real.sqrt_pos.2 (by positivity)) _
    exact (ENNReal.ofReal_pos.2 hpos).ne' hk
  · simpa using hk

/-- **Restriction norms of momentum multiples**, with real bounds. -/
theorem restr_mul_momentum_le {Λ : ℕ} (hΛ : Λ ≠ 0) (hd : 1 ≤ d) {θ : ℝ} (a b : ℕ) (B : Set (Fin r → ℝ))
    (K : Set (Mom d)) {c : Mom d → ℂ} (hc : ContDiff ℝ Λ c) (F : (Fin r → ℝ) → Mom d → ℂ) {S e : ℝ}
    (hS0 : 0 ≤ S) (hS : spatialNorm Λ a c ≤ ENNReal.ofReal S)
    (hF : mixedRestrictionNorm θ Λ b B K (fun t k => F t k) ≤ ENNReal.ofReal e) :
    mixedRestrictionNorm θ Λ (a + b) B K (fun t k => c k * F t k) ≤
      ENNReal.ofReal (cLeib d Λ * S * e) := by
  by_cases h0 : spatialNorm Λ a c = 0
  · have hc0 := eq_zero_of_spatialNorm_eq_zero hc h0
    have : mixedRestrictionNorm θ Λ (a + b) B K (fun t k => c k * F t k) =
        mixedRestrictionNorm θ Λ (a + b) B K (fun t k => (fun (_ : Fin r → ℝ) (_ : Mom d) => (0 : ℂ)) t k) :=
      restr_congr B K (F := fun t k => c k * F t k) (G := fun (_ : Fin r → ℝ) (_ : Mom d) => (0 : ℂ))
        fun t _ k _ => by rw [hc0]; simp
    rw [this]
    exact (restr_zero B K).le.trans zero_le
  have hAne0 : ENNReal.ofReal (cLeib d Λ) * spatialNorm Λ a c ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.2 (lt_of_lt_of_le one_pos (one_le_cLeib hd Λ))).ne' h0
  have hAneT : ENNReal.ofReal (cLeib d Λ) * spatialNorm Λ a c ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hS)
  have key : mixedRestrictionNorm θ Λ (a + b) B K (fun t k => c k * F t k) ≤
      ENNReal.ofReal (cLeib d Λ) * spatialNorm Λ a c * mixedRestrictionNorm θ Λ b B K (fun t k => F t k) := by
    rw [mixedRestrictionNorm_eq_agreement B K (fun t k => c k * F t k),
      mixedRestrictionNorm_eq_agreement B K F,
      ENNReal.mul_iInf_of_ne hAne0 hAneT]
    refine le_iInf fun G => ?_
    rw [ENNReal.mul_iInf_of_ne hAne0 hAneT]
    refine le_iInf fun hG => ?_
    refine (iInf₂_le (fun t k => c k * G t k) fun t ht k hk => by
      show c k * G t k = c k * F t k
      rw [hG t ht k hk]).trans ?_
    by_cases hGt : mixedFourierNorm θ Λ b G = ⊤
    · rw [hGt, ENNReal.mul_top hAne0]
      exact le_top
    · exact mixedFourierNorm_mul_momentum_le hΛ hd θ a b hc (lt_top_iff_ne_top.2 hGt)
  refine key.trans ?_
  calc ENNReal.ofReal (cLeib d Λ) * spatialNorm Λ a c *
        mixedRestrictionNorm θ Λ b B K (fun t k => F t k)
      ≤ ENNReal.ofReal (cLeib d Λ) * ENNReal.ofReal S * ENNReal.ofReal e := by gcongr
    _ = ENNReal.ofReal (cLeib d Λ * S * e) := by
        rw [← ENNReal.ofReal_mul (cLeib_nonneg d Λ), ← ENNReal.ofReal_mul (mul_nonneg (cLeib_nonneg d Λ) hS0)]

end WaveTurbulence.PL2330
