/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-! # The analytic absorption of logarithmic losses in the accounting bound

If `2n ≤ 48000 (kf + kg)` then `(log L)^(8n) L^(-η kf/2) L^(-κ kg)` is at most
`L^(-(η/2-θ) kf-(κ-θ) kg)` for every `θ > 0` and large `L`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open scoped ENNReal
open Filter

theorem log_pow_le_rpow_eventually (θ : ℝ) (hθ : 0 < θ) :
    ∀ᶠ L : ℝ in atTop,(Real.log L)^(192000 : ℕ) ≤ L^θ ∧ 1 ≤ Real.log L := by
  have h1 := (isLittleO_log_rpow_rpow_atTop (192000 : ℝ) hθ).bound one_pos
  filter_upwards [h1,eventually_ge_atTop (Real.exp 1),eventually_gt_atTop (0 : ℝ)] with L hL hexp hpos
  refine ⟨?_,(Real.le_log_iff_exp_le hpos).mpr hexp⟩
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hpos).mpr hexp
  have hl0 : 0 ≤ Real.log L := by linarith only [hlog]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hl0 _),Real.norm_of_nonneg (Real.rpow_nonneg hpos.le _),one_mul] at hL
  simpa [Real.rpow_natCast] using hL

/-- Real form of the budget estimate. -/
theorem budget_real_bound (θ : ℝ) (hθ : 0 < θ) :
    ∀ᶠ L : ℝ in atTop,∀ (n kf kg : ℕ) (a b : ℝ),2*n ≤ 48000*(kf+kg) →
      ((Real.log L)^8)^n * (L^(-a))^kf * (L^(-b))^kg ≤ L^((θ-a)*kf+(θ-b)*kg) := by
  filter_upwards [log_pow_le_rpow_eventually θ hθ,eventually_gt_atTop (1 : ℝ)] with L hL hL1
  obtain ⟨hpow,hlog⟩ := hL
  intro n kf kg a b hn
  have hLp : 0 < L := by linarith only [hL1]
  have hA : 1 ≤ ((Real.log L)^8) := one_le_pow₀ hlog
  have hn' : n ≤ 24000*(kf+kg) := by omega
  calc ((Real.log L)^8)^n * (L^(-a))^kf * (L^(-b))^kg
      ≤ (((Real.log L)^8)^24000)^(kf+kg) * (L^(-a))^kf * (L^(-b))^kg := by
        gcongr
        calc ((Real.log L)^8)^n ≤ ((Real.log L)^8)^(24000*(kf+kg)) := pow_le_pow_right₀ hA hn'
          _ = _ := by rw [pow_mul]
    _ ≤ (L^θ)^(kf+kg) * (L^(-a))^kf * (L^(-b))^kg := by
        gcongr
        calc (((Real.log L)^8)^24000) = (Real.log L)^(192000 : ℕ) := by rw [← pow_mul]
          _ ≤ L^θ := hpow
    _ = L^((θ-a)*kf+(θ-b)*kg) := by
        rw [← Real.rpow_natCast,← Real.rpow_natCast (L^(-a)),← Real.rpow_natCast (L^(-b)),
          ← Real.rpow_mul hLp.le,← Real.rpow_mul hLp.le,← Real.rpow_mul hLp.le,
          ← Real.rpow_add hLp,← Real.rpow_add hLp]
        congr 1
        push_cast
        ring

/-- The ENNReal form, with the three source factors, and the two conclusions of
Proposition 10.2 as explicit exponents. -/
theorem budget_final (γ η : ℝ) (hγ : 0 < γ ∧ γ < 1) (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) :
    ∃ L₁ : ℝ,1 < L₁ ∧ ∀ L ≥ L₁,∀ n kf kg : ℕ,2*n ≤ 48000*(kf+kg) →
      (ENNReal.ofReal (Real.log L^8))^n*(ENNReal.ofReal (L^(-η/2)))^kf*
        (ENNReal.ofReal (L^(-5*min γ (1-γ)/8)))^kg ≤
        (if 1 ≤ kg then ENNReal.ofReal (L^(-3*min γ (1-γ)/5)) else 1) ∧
      (1 ≤ kf+kg → (ENNReal.ofReal (Real.log L^8))^n*(ENNReal.ofReal (L^(-η/2)))^kf*
        (ENNReal.ofReal (L^(-5*min γ (1-γ)/8)))^kg ≤ ENNReal.ofReal (L^(-η/3))) := by
  have hγ0 : 0 < min γ (1-γ) := lt_min hγ.1 (by linarith only [hγ.2])
  set γ0 := min γ (1-γ) with hγ0def
  set θ := min (η/12) (γ0/40) with hθdef
  have hθ : 0 < θ := lt_min (by linarith only [hη]) (by linarith only [hγ0])
  have hθ1 : θ ≤ η/12 := min_le_left _ _
  have hθ2 : θ ≤ γ0/40 := min_le_right _ _
  obtain ⟨L₁,hL₁⟩ := eventually_atTop.mp ((budget_real_bound θ hθ).and (eventually_gt_atTop (1 : ℝ)))
  refine ⟨max L₁ 2,by simp,?_⟩
  intro L hL n kf kg hn
  obtain ⟨hb,hL1⟩ := hL₁ L ((le_max_left _ _).trans hL)
  have hLp : 0 < L := by linarith only [hL1]
  have hlog : 0 ≤ Real.log L := (Real.log_pos hL1).le
  have hreal := hb n kf kg (η/2) (5*γ0/8) hn
  have hconv : (ENNReal.ofReal (Real.log L^8))^n*(ENNReal.ofReal (L^(-η/2)))^kf*
      (ENNReal.ofReal (L^(-5*γ0/8)))^kg =
      ENNReal.ofReal (((Real.log L)^8)^n*(L^(-(η/2)))^kf*(L^(-(5*γ0/8)))^kg) := by
    have e1 : -η/2 = -(η/2) := by ring
    have e2 : -5*γ0/8 = -(5*γ0/8) := by ring
    have h1 : ENNReal.ofReal (((Real.log L)^8)^n) = ENNReal.ofReal ((Real.log L)^8)^n :=
      ENNReal.ofReal_pow (by positivity) n
    have h2 : ENNReal.ofReal ((L^(-(η/2)))^kf) = ENNReal.ofReal (L^(-(η/2)))^kf :=
      ENNReal.ofReal_pow (by positivity) kf
    have h3 : ENNReal.ofReal ((L^(-(5*γ0/8)))^kg) = ENNReal.ofReal (L^(-(5*γ0/8)))^kg :=
      ENNReal.ofReal_pow (by positivity) kg
    rw [e1,e2,ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by positivity),h1,h2,h3]
  rw [hconv]
  constructor
  · split_ifs with hkg
    · refine ENNReal.ofReal_le_ofReal (hreal.trans ?_)
      apply Real.rpow_le_rpow_of_exponent_le hL1.le
      have hkf0 : (0 : ℝ) ≤ kf := Nat.cast_nonneg _
      have hkg1 : (1 : ℝ) ≤ kg := by exact_mod_cast hkg
      nlinarith only [hkf0,hkg1,hθ1,hθ2,hη,hγ0]
    · rw [ENNReal.ofReal_le_one]
      refine hreal.trans ?_
      apply Real.rpow_le_one_of_one_le_of_nonpos hL1.le
      have hkf0 : (0 : ℝ) ≤ kf := Nat.cast_nonneg _
      have hkg0 : (0 : ℝ) ≤ kg := Nat.cast_nonneg _
      nlinarith only [hkf0,hkg0,hθ1,hθ2,hη,hγ0]
  · intro hk
    refine ENNReal.ofReal_le_ofReal (hreal.trans ?_)
    apply Real.rpow_le_rpow_of_exponent_le hL1.le
    have hk1 : (1 : ℝ) ≤ (kf : ℝ)+kg := by exact_mod_cast hk
    have hkf0 : (0 : ℝ) ≤ kf := Nat.cast_nonneg _
    have hkg0 : (0 : ℝ) ≤ kg := Nat.cast_nonneg _
    have c1 : θ-η/2 ≤ -5*η/12 := by linarith only [hθ1]
    have c2 : θ-5*γ0/8 ≤ -5*η/12 := by linarith only [hθ2,hηγ,hη]
    nlinarith only [mul_le_mul_of_nonneg_right c1 hkf0,mul_le_mul_of_nonneg_right c2 hkg0,
      mul_le_mul_of_nonneg_left hk1 hη.le,hη]

end WaveTurbulence.Mole.AppbAlgorithm
