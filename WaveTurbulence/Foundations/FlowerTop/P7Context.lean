/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FlowerTop.P7Inputs
public import WaveTurbulence.Foundations.Spine.NonregularPrefix

/-! Construct P7's LG context and discharge GardenNum/CoupleNum at one late threshold. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerTop
open LGSpine Filter Set

theorem eventually_p7_context (C₀ : ℕ → ℝ → ℕ) (hC₀ : ∀ d γ, 2 ≤ C₀ d γ) (P : WTParams)
    (hQ : ∀ L : ℝ, P.L ≤ L → NonregularHyp C₀ {P with L := L})
    (Cφ : ℝ) (hCφ : 0 ≤ Cφ)
    (hφ : ∀ τ ∈ Set.Icc (0 : ℝ) P.τstar,
      SNormR (P.Lambda 0) (P.Lambda 0) (P.φ τ) ≤ ENNReal.ofReal Cφ) :
    ∀ᶠ L : ℝ in atTop, ∃ G : FlowerP7.LGContext (C₀ P.d P.γ) {P with L := L},
      G.Cφ = Cφ ∧ ∀ p, p < P.D →
        GardenNum {P with L := L} Cφ p ∧ CoupleNum {P with L := L} Cφ p := by
  have h0 : NonregularHyp C₀ P := hQ P.L le_rfl
  obtain ⟨⟨_, _⟩, hps0, hη8, hd3, _⟩ := h0
  have hd1 : 1 ≤ P.d := by omega
  have hη := hps0.eta_pos
  set X : ℕ := 4 * (40 * P.d) ^ (2 * P.D + 2) with hX
  -- the eventual thresholds
  have E1 : ∀ᶠ L : ℝ in atTop, ∀ p ∈ Finset.range P.D,
      gardenC P Cφ p * (1 + Real.log L) ^ (24 * logExp P * P.Lambda (p + 1)) ≤ L ^ ((1 : ℝ) / 140) := by
    refine (Filter.eventually_all_finset (Finset.range P.D)).2 ?_
    intro p _
    have hg0 : 0 ≤ gardenC P Cφ p := by
      unfold gardenC
      have hC1 := hps0.c1_ge
      have : 0 ≤ max (Cφ + 1) P.C₁ := le_trans (by linarith) (le_max_right _ _)
      have : 0 < P.C₁ := by linarith
      positivity
    have := CountLemmas.eventually_monomial_log_le (a := 0) (b := (1 : ℝ) / 140) (C := gardenC P Cφ p)
      (by norm_num) hg0 (24 * logExp P * P.Lambda (p + 1))
    filter_upwards [this] with L hL
    simpa only [Real.rpow_zero, mul_one] using hL
  have E2 : ∀ᶠ L : ℝ in atTop, ∀ p ∈ Finset.range P.D,
      coupleC P Cφ p * (1 + Real.log L) ^ (16 * logExp P * P.Lambda (p + 1)) ≤
      L ^ (P.η ^ 7 - (3 * P.theta (p + 1) + 2 * P.theta p) / 5) := by
    refine (Filter.eventually_all_finset (Finset.range P.D)).2 ?_
    intro p _
    have hθ : (3 * P.theta (p + 1) + 2 * P.theta p) / 5 < P.η ^ 7 := by
      have h1 := theta_le_two P hη.le (p + 1)
      have h2 := theta_le_two P hη.le p
      have h3 := eta_gap_pos hη hη8
      linarith
    have hg0 : 0 ≤ coupleC P Cφ p := by
      unfold coupleC
      have hC1 := hps0.c1_ge
      have : 0 ≤ max (Cφ + 1) P.C₁ := le_trans (by linarith) (le_max_right _ _)
      have : 0 < P.C₁ := by linarith
      positivity
    have := CountLemmas.eventually_monomial_log_le (a := 0)
      (b := P.η ^ 7 - (3 * P.theta (p + 1) + 2 * P.theta p) / 5)
      (C := coupleC P Cφ p) (by linarith) hg0 (16 * logExp P * P.Lambda (p + 1))
    filter_upwards [this] with L hL
    simpa only [Real.rpow_zero, mul_one] using hL
  have E3 : ∀ᶠ L : ℝ in atTop, 1 ≤ Real.log L := Real.tendsto_log_atTop.eventually_ge_atTop 1
  have E4 : ∀ᶠ L : ℝ in atTop, P.L ≤ L := eventually_ge_atTop _
  filter_upwards [E1, E2, E3, E4] with L hE1 hE2 hlog hLP
  have hQL := hQ L hLP
  obtain ⟨⟨⟨hgate, hcoarse, hfourier, hcount, hlowP⟩, hctxL⟩, hs, hη8L, hd3L, habs⟩ := hQL
  obtain ⟨_, htimeL, _, _⟩ := hctxL
  have hL1 : 1 ≤ L := by have := hs.L_ge; change 2 ≤ L at this; linarith
  have hδ0 := hs.delta_pos
  have hδ1 := hs.delta_le
  have hC₀2 : (2 : ℝ) ≤ ((6 * C₀ P.d P.γ : ℕ) : ℝ) := by
    have := hC₀ P.d P.γ
    exact_mod_cast (by omega : 2 ≤ 6 * C₀ P.d P.γ)
  have hδsmall : 2 * P.C₁ * P.δ ^ (6 * P.ν) ≤ 1 := by
    have h1 := habs.1
    have hν0 := hs.nu_pos
    have hC1 := hs.c1_ge
    have e : P.δ ^ (6 * P.ν) = P.δ ^ (2 * P.ν) * P.δ ^ (4 * P.ν) := by
      rw [← Real.rpow_add hδ0]; ring_nf
    have hle : P.δ ^ (4 * P.ν) ≤ 1 := Real.rpow_le_one hδ0.le hδ1 (by positivity)
    have hp0 : 0 ≤ P.δ ^ (2 * P.ν) := Real.rpow_nonneg hδ0.le _
    have hp1 : 0 ≤ P.δ ^ (4 * P.ν) := Real.rpow_nonneg hδ0.le _
    calc 2 * P.C₁ * P.δ ^ (6 * P.ν) = (2 * P.C₁ * P.δ ^ (2 * P.ν)) * P.δ ^ (4 * P.ν) := by rw [e]; ring
      _ ≤ (2 * P.C₁ * P.δ ^ (2 * P.ν)) * 1 := mul_le_mul_of_nonneg_left hle (by positivity)
      _ ≤ (((6 * C₀ P.d P.γ : ℕ) : ℝ) * P.C₁ ^ 6 * P.δ ^ (2 * P.ν)) := by
          rw [mul_one]
          apply mul_le_mul_of_nonneg_right _ hp0
          calc 2 * P.C₁ ≤ 2 * P.C₁ ^ 6 := by
                have h1 := hs.c1_ge
                nlinarith [pow_le_pow_right₀ h1 (by norm_num : 1 ≤ 6)]
            _ ≤ ((6 * C₀ P.d P.γ : ℕ) : ℝ) * P.C₁ ^ 6 :=
              mul_le_mul_of_nonneg_right hC₀2 (by have := hs.c1_ge; positivity)
      _ ≤ 1 := h1
  have hd1 : 1 ≤ P.d := by omega
  refine ⟨⟨hs, hcoarse, hfourier, hcount, habs, hlog, hgate, hd1,
    hlowP, htimeL, Cφ, hCφ, hφ⟩, rfl, ?_⟩
  intro p hp
  constructor
  · exact gardenNum_of_numerics {P with L := L} Cφ p hd1 hlog hs.c1_ge hCφ hδ0 hη.le hL1 hδsmall
      (hE1 p (Finset.mem_range.mpr hp))
  · exact coupleNum_of_numerics {P with L := L} Cφ p hd1 hlog hs.c1_ge hCφ hδ0 hL1 hδsmall
      (hE2 p (Finset.mem_range.mpr hp))

end WaveTurbulence.FlowerTop
