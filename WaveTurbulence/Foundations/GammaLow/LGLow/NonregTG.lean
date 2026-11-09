/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.LGLow.Garden
public import WaveTurbulence.Foundations.GammaLow.LGLow.Couple
public import WaveTurbulence.Foundations.Spine.NonregularPrefix

/-! # LG-low (packet L07): TARGET terms (a), (b) through the waist

`nonregular_of_typeGate` and `nonregular_late_of_typeGate` are main's `LGSpine.nonregular_of_data`
(`Spine/NonregularAssembly.lean`) and `LGSpine.nonregular_late` (`Spine/NonregularPrefix.lean`), copied by source: the
gate bundle is replaced by `TypeGateAt` (in the late theorem, `hTG` at each large `L` with `1 ≤ log L`), and
`NonregularHyp` by `NonregularNumHyp` (its non-gate conjuncts). -/

public section
set_option autoImplicit false

namespace WaveTurbulence.GammaLow.LGLow
open WaveTurbulence.Induct WaveTurbulence.LGSpine
open MeasureTheory Set Finset Filter
open scoped Classical ENNReal

/-- Main's `nonregular_of_data` through the waist. -/
theorem nonregular_of_typeGate (P : WTParams) (hs : PieceSmall P) (hTG : TypeGateAt P)
    (hd : 1 ≤ P.d) (hlowP : LowProfileAt P) (htime : P.τstar = (P.D : ℝ) * P.δ)
    {Cφ : ℝ} (hCφ : 0 ≤ Cφ)
    (hφ : ∀ τ ∈ Icc (0 : ℝ) P.τstar,
      SNormR (P.Lambda 0) (P.Lambda 0) (P.φ τ) ≤ ENNReal.ofReal Cφ)
    (hR1 : ∀ p, 1 ≤ P.R (p + 1))
    (hG : ∀ p, p < P.D → GardenNum P Cφ p) (hC : ∀ p, p < P.D → CoupleNum P Cφ p) :
    NonregularEstimateAt P := by
  intro p hp Rr hRr N hN t ht
  refine ⟨?_, ?_⟩
  · intro m hm2 hmmax ζ hζ n
    exact garden_estimate_of_typeGate P hs hTG hd hlowP htime hCφ hφ
      hp Rr hRr hm2 hmmax ζ hζ n hN ht (twistClosed_gardenSet P hd hp hm2 ζ hN) (hG p hp m N hm2 hmmax hN)
  · exact couple_estimate_of_typeGate P hs hTG hd hlowP htime hCφ hφ
      hp Rr hRr (hR1 p) hN ht (twistClosed_coupleSet P hd hp hN) (hC p hp N hN)

/-- The numerical and context hypotheses of main's `NonregularHyp`, without the source gates (which enter through
`TypeGateAt`, given per `L` in `nonregular_late_of_typeGate`). -/
abbrev NonregularNumHyp (C₀ : ℕ → ℝ → ℕ) (P : WTParams) : Prop :=
  (LowProfileAt P ∧ WKEContext P) ∧
    PieceSmall P ∧ P.η ≤ 1 / 8 ∧ 3 ≤ P.d ∧ FinalAbsorptionAt (6 * C₀ P.d P.γ) P

/-- Main's `nonregular_late` through the waist. -/
theorem nonregular_late_of_typeGate (C₀ : ℕ → ℝ → ℕ) (hC₀ : ∀ d γ, 2 ≤ C₀ d γ) (P : WTParams)
    (hQ : ∀ L : ℝ, P.L ≤ L → NonregularNumHyp C₀ {P with L := L})
    (hTG : ∀ L : ℝ, P.L ≤ L → 1 ≤ Real.log L → TypeGateAt {P with L := L}) :
    ∀ᶠ L : ℝ in atTop, NonregularEstimateAt {P with L := L} := by
  have h0 : NonregularNumHyp C₀ P := hQ P.L le_rfl
  obtain ⟨⟨_, hctx0⟩, hps0, hη8, hd3, _⟩ := h0
  obtain ⟨hsol, htime, hD, hφin⟩ := hctx0
  have hd1 : 1 ≤ P.d := by omega
  obtain ⟨Cφ, hCφ1, hφ⟩ := exists_uniform_SNormR hsol.1 (P.Lambda 0) (P.Lambda 0)
  have hCφ : 0 ≤ Cφ := by linarith
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
  obtain ⟨⟨hlowP, hctxL⟩, hs, hη8L, hd3L, habs⟩ := hQL
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
  refine nonregular_of_typeGate {P with L := L} hs (hTG L hLP hlog) hd1
    hlowP htimeL hCφ hφ (fun p => one_le_R {P with L := L} hlog hd1 (p + 1)) ?_ ?_
  · intro p hp
    exact gardenNum_of_numerics {P with L := L} Cφ p hd1 hlog hs.c1_ge hCφ hδ0 hη.le hL1 hδsmall
      (hE1 p (Finset.mem_range.mpr hp))
  · intro p hp
    exact coupleNum_of_numerics {P with L := L} Cφ p hd1 hlog hs.c1_ge hCφ hδ0 hL1 hδsmall
      (hE2 p (Finset.mem_range.mpr hp))

end WaveTurbulence.GammaLow.LGLow
