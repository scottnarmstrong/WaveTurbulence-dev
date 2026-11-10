/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic
/-! TARGET L2253-L2255 (finalprooffin -> finalprooffin2): the factorial and polynomial losses are absorbed
by the gain `L^{-eta^6/4}` and the slack `1/60 - 1/70` per extra root pair, once `L` is large and the orders
are at most a power of `log L`. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Filter Asymptotics

theorem eventually_log_le_mul {ε : ℝ} (hε : 0 < ε) : ∀ᶠ x : ℝ in atTop, Real.log x ≤ ε * x := by
  have h := (Real.isLittleO_log_id_atTop.def hε)
  filter_upwards [h, eventually_gt_atTop 0] with x hx hx0
  have := (le_abs_self (Real.log x)).trans hx
  simpa [abs_of_pos hx0] using this

/-- The three absorptions needed after the class sum, for `L` large. `X = C0 (log L)^kappa`. -/
theorem eventually_final_absorption (C₀ κ : ℕ) (hC₀ : 1 ≤ C₀) (c₂ η ν : ℝ) (hc₂ : 1 ≤ c₂)
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hν : 0 < ν) :
    ∃ L₀ : ℝ, 2 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∀ n R : ℕ, 1 ≤ R → R ≤ 2 * n →
      (n : ℝ) ≤ Real.log L ^ κ →
      (c₂ * L ^ (-(ν * η)) ≤ 1 / 2) ∧
      (((C₀ * n : ℕ) : ℝ) ^ C₀ * c₂ * L ^ (-η ^ 6 / 4) ≤ 1 / 2) ∧
      (4 * (c₂ * (((C₀ * R).factorial : ℕ) : ℝ) * (((C₀ * n : ℕ) : ℝ) ^ C₀ * c₂ * L ^ (-η ^ 6 / 4)) *
        L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60))) ≤
        L ^ (-η ^ 7) * L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 70))) := by
  have hC₀r : (1 : ℝ) ≤ C₀ := by exact_mod_cast hC₀
  have hc₂0 : 0 < c₂ := by linarith
  set ε : ℝ := η ^ 6 / (128 * C₀ * ((κ : ℝ) + 1)) with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨ℓ₁, hℓ₁⟩ := eventually_atTop.mp (eventually_log_le_mul hε0)
  set q : ℝ := min (η ^ 6) (ν * η) with hq
  have hq0 : 0 < q := lt_min (by positivity) (by positivity)
  have hq1 : q ≤ η ^ 6 := min_le_left _ _
  have hq2 : q ≤ ν * η := min_le_right _ _
  set A : ℝ := |Real.log (4 * c₂ ^ 2)| + |Real.log (2 * c₂)| + C₀ * |Real.log C₀| + C₀ + 1 with hA
  have hA0 : 0 < A := by positivity
  set ℓ₀ : ℝ := max ℓ₁ 1 + 1000 * (C₀ + 1) * A / q with hℓ₀
  refine ⟨Real.exp ℓ₀, ?_, ?_⟩
  · have : 0 ≤ 1000 * ((C₀ : ℝ) + 1) * A / q := by positivity
    have h1 : (1 : ℝ) ≤ max ℓ₁ 1 := le_max_right _ _
    calc (2 : ℝ) ≤ Real.exp 1 := by
          have := Real.add_one_le_exp (1 : ℝ); linarith
      _ ≤ Real.exp ℓ₀ := Real.exp_le_exp.mpr (by linarith)
  intro L hL n R hR hRn hnL
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hL
  have hℓ : ℓ₀ ≤ Real.log L := by
    have := Real.log_le_log (Real.exp_pos _) hL
    rwa [Real.log_exp] at this
  set ℓ : ℝ := Real.log L with hℓdef
  have hℓ1 : 1 ≤ ℓ := by
    have : (1 : ℝ) ≤ max ℓ₁ 1 := le_max_right _ _
    have : 0 ≤ 1000 * ((C₀ : ℝ) + 1) * A / q := by positivity
    linarith
  have hlogl : Real.log ℓ ≤ ε * ℓ := hℓ₁ ℓ ((le_max_left _ _).trans (by
    have : 0 ≤ 1000 * ((C₀ : ℝ) + 1) * A / q := by positivity
    linarith))
  have hLexp : ∀ x : ℝ, L ^ x = Real.exp (x * ℓ) := fun x => by
    rw [Real.rpow_def_of_pos hL0, mul_comm]
  -- the key size inequality: A <= q * ell / (1000 (C0+1))
  have hAℓ : 1000 * ((C₀ : ℝ) + 1) * A ≤ q * ℓ := by
    have h1 : 1000 * ((C₀ : ℝ) + 1) * A / q ≤ ℓ := by
      have : (0 : ℝ) ≤ max ℓ₁ 1 := by have := le_max_right ℓ₁ 1; linarith
      linarith
    have h2 := (div_le_iff₀ hq0).mp h1
    linarith [mul_comm ℓ q]
  -- X = C0 * ell^kappa bounds n and R
  set X : ℝ := 2 * (C₀ : ℝ) * ℓ ^ κ with hX
  have hXpos : 1 ≤ X := by
    have h1 : 1 ≤ ℓ ^ κ := one_le_pow₀ hℓ1
    have h2 : (1 : ℝ) ≤ 2 * C₀ := by linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (2 * C₀) * ℓ ^ κ := mul_le_mul h2 h1 (by norm_num) (by linarith)
  have hn1 : 1 ≤ n := by omega
  have hCn : (((C₀ * n : ℕ)) : ℝ) ≤ X := by
    push_cast
    have h1 : (C₀ : ℝ) * n ≤ C₀ * ℓ ^ κ := mul_le_mul_of_nonneg_left hnL (by positivity)
    have h2 : (0 : ℝ) ≤ C₀ * ℓ ^ κ := by positivity
    rw [hX]; linarith
  have hCR : (((C₀ * R : ℕ)) : ℝ) ≤ X := by
    have h1 : C₀ * R ≤ C₀ * (2 * n) := Nat.mul_le_mul_left C₀ hRn
    have h2 : (((C₀ * R : ℕ)) : ℝ) ≤ ((C₀ * (2 * n) : ℕ) : ℝ) := by exact_mod_cast h1
    refine h2.trans ?_
    push_cast
    have h3 : (C₀ : ℝ) * (2 * n) ≤ C₀ * (2 * ℓ ^ κ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
    rw [hX]; linarith
  have hlogX : Real.log X = Real.log 2 + Real.log C₀ + κ * Real.log ℓ := by
    rw [hX, Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_pow]
  -- coefficient bounds
  have hκε : (κ : ℝ) * Real.log ℓ ≤ κ * (ε * ℓ) := mul_le_mul_of_nonneg_left hlogl (Nat.cast_nonneg _)
  have h128 : (C₀ : ℝ) * (((κ : ℝ) + 1) * ε) = η ^ 6 / 128 := by
    rw [hε]; field_simp
  have hCκε' : (C₀ : ℝ) * ((κ : ℝ) * Real.log ℓ) ≤ η ^ 6 * ℓ / 128 := by
    have h1 : (C₀ : ℝ) * ((κ : ℝ) * Real.log ℓ) ≤ (C₀ : ℝ) * ((κ : ℝ) * (ε * ℓ)) :=
      mul_le_mul_of_nonneg_left hκε (by positivity)
    have h2 : (C₀ : ℝ) * ((κ : ℝ) * (ε * ℓ)) ≤ (C₀ : ℝ) * (((κ : ℝ) + 1) * ε) * ℓ := by
      have : (C₀ : ℝ) * ((κ : ℝ) * (ε * ℓ)) = (C₀ : ℝ) * ((κ : ℝ) * ε) * ℓ := by ring
      rw [this]
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right (by linarith) hε0.le
    rw [h128] at h2
    linarith
  have hη6 : η ^ 6 ≤ 1 := pow_le_one₀ hη.le (by linarith)
  have hη7 : η ^ 7 ≤ η ^ 6 / 8 := by
    have : η ^ 7 = η ^ 6 * η := by ring
    have h := mul_le_mul_of_nonneg_left hη8 (pow_pos hη 6).le
    rw [this]; linarith only [h]
  have habs : Real.log (4 * c₂ ^ 2) ≤ |Real.log (4 * c₂ ^ 2)| := le_abs_self _
  have habs2 : Real.log (2 * c₂) ≤ |Real.log (2 * c₂)| := le_abs_self _
  have habs3 : Real.log (C₀ : ℝ) ≤ |Real.log C₀| := le_abs_self _
  have hCl : (C₀ : ℝ) * Real.log C₀ ≤ C₀ * |Real.log C₀| := mul_le_mul_of_nonneg_left habs3 (by positivity)
  have habsnn1 := abs_nonneg (Real.log (4 * c₂ ^ 2))
  have habsnn2 := abs_nonneg (Real.log (2 * c₂))
  have habsnn3 : 0 ≤ (C₀ : ℝ) * |Real.log C₀| := by positivity
  -- small facts: A * 1000 (C0+1) <= q ℓ
  have hA1 : A ≤ ((C₀ : ℝ) + 1) * A := by
    have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ C₀ + 1 by linarith) hA0.le
    linarith
  have hAq : A ≤ q * ℓ / 1000 := by linarith [hAℓ, hA1]
  have hnn : 0 ≤ η ^ 6 * ℓ := by positivity
  have hqℓ : q * ℓ ≤ η ^ 6 * ℓ := mul_le_mul_of_nonneg_right hq1 (by linarith only [hℓ1])
  have hη6s : η ^ 6 ≤ 1 / 8 := by
    have : η ^ 6 ≤ η := by
      calc η ^ 6 ≤ η ^ 1 := pow_le_pow_of_le_one hη.le (by linarith only [hη8]) (by norm_num)
        _ = η := pow_one η
    linarith only [this, hη8]
  have hη6ℓ : η ^ 6 * ℓ ≤ ℓ / 8 := by
    have := mul_le_mul_of_nonneg_right hη6s (by linarith only [hℓ1] : (0 : ℝ) ≤ ℓ)
    linarith only [this]
  -- bounds on the logarithms
  have hAℓ' : A ≤ η ^ 6 * ℓ / 1000 := by linarith only [hAq, hqℓ]
  have hlogA2 : Real.log (2 * c₂) ≤ A := by
    rw [hA]; linarith only [habs2, habsnn1, habsnn3]
  have hlogA4 : Real.log (4 * c₂ ^ 2) ≤ A := by
    rw [hA]; linarith only [habs, habsnn2, habsnn3]
  have hCX1 : (C₀ : ℝ) * Real.log X ≤ η ^ 6 * ℓ / 100 := by
    rw [hlogX, mul_add, mul_add]
    have hl2le : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    have h0 : (C₀ : ℝ) * Real.log 2 ≤ C₀ := by
      have := mul_le_mul_of_nonneg_left hl2le (by positivity : (0 : ℝ) ≤ C₀)
      linarith only [this]
    have h1 : (C₀ : ℝ) * Real.log C₀ + C₀ ≤ A := by
      have : (C₀ : ℝ) * |Real.log C₀| ≤ A - C₀ := by rw [hA]; linarith only [habsnn1, habsnn2]
      linarith only [hCl, this]
    linarith only [h0, h1, hCκε', hAℓ', hnn]
  have hCX2 : (C₀ : ℝ) * Real.log X ≤ ℓ / 420 := by
    linarith only [hCX1, hη6ℓ, hℓ1]
  refine ⟨?_, ?_, ?_⟩
  · -- c2 L^(-(nu eta)) <= 1/2
    rw [hLexp]
    have e : Real.exp (Real.log (2 * c₂) - ν * η * ℓ) = 2 * c₂ * Real.exp (-(ν * η) * ℓ) := by
      rw [show Real.log (2 * c₂) - ν * η * ℓ = Real.log (2 * c₂) + (-(ν * η) * ℓ) by ring,
        Real.exp_add, Real.exp_log (by positivity)]
    have h1 : Real.exp (Real.log (2 * c₂) - ν * η * ℓ) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have h2 : q * ℓ ≤ ν * η * ℓ := mul_le_mul_of_nonneg_right hq2 (by linarith only [hℓ1])
      have hq0ℓ : 0 ≤ q * ℓ := mul_nonneg hq0.le (by linarith only [hℓ1])
      linarith only [hlogA2, hAq, h2, hq0ℓ]
    linarith only [e, h1]
  · -- (C0 n)^C0 c2 L^(-eta^6/4) <= 1/2
    rw [hLexp]
    have hXe : X ^ C₀ = Real.exp (C₀ * Real.log X) := by
      rw [Real.exp_nat_mul, Real.exp_log (by linarith only [hXpos])]
    have hexp : Real.exp (Real.log (2 * c₂) + C₀ * Real.log X + (-η ^ 6 / 4) * ℓ) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith only [hlogA2, hAℓ', hCX1, hnn]
    rw [Real.exp_add, Real.exp_add, Real.exp_log (by positivity), ← hXe] at hexp
    calc ((C₀ * n : ℕ) : ℝ) ^ C₀ * c₂ * Real.exp (-η ^ 6 / 4 * ℓ)
        ≤ X ^ C₀ * c₂ * Real.exp (-η ^ 6 / 4 * ℓ) := by gcongr
      _ ≤ 1 / 2 := by linarith only [hexp]
  · -- the main absorption
    simp only [hLexp]
    have hXlog : Real.exp (Real.log X) = X := Real.exp_log (by linarith only [hXpos])
    have hf : (((C₀ * R).factorial : ℕ) : ℝ) ≤ Real.exp (((C₀ * R : ℕ) : ℝ) * Real.log X) := by
      have h1 : ((C₀ * R).factorial : ℕ) ≤ (C₀ * R) ^ (C₀ * R) := Nat.factorial_le_pow _
      have h2 : (((C₀ * R).factorial : ℕ) : ℝ) ≤ (((C₀ * R : ℕ) : ℝ)) ^ (C₀ * R) := by exact_mod_cast h1
      refine h2.trans ?_
      rw [Real.exp_nat_mul, hXlog]
      exact pow_le_pow_left₀ (by positivity) hCR _
    have ha : ((C₀ * n : ℕ) : ℝ) ^ C₀ ≤ Real.exp ((C₀ : ℝ) * Real.log X) := by
      rw [Real.exp_nat_mul, hXlog]
      exact pow_le_pow_left₀ (by positivity) hCn _
    have hmain : 4 * (c₂ * (((C₀ * R).factorial : ℕ) : ℝ) *
        (((C₀ * n : ℕ) : ℝ) ^ C₀ * c₂ * Real.exp (-η ^ 6 / 4 * ℓ)) *
        Real.exp (-((R : ℝ) - 1) * (1 / 4 + 1 / 60) * ℓ)) ≤
        4 * (c₂ * Real.exp (((C₀ * R : ℕ) : ℝ) * Real.log X) *
        (Real.exp ((C₀ : ℝ) * Real.log X) * c₂ * Real.exp (-η ^ 6 / 4 * ℓ)) *
        Real.exp (-((R : ℝ) - 1) * (1 / 4 + 1 / 60) * ℓ)) := by gcongr
    refine hmain.trans ?_
    have e1 : 4 * (c₂ * Real.exp (((C₀ * R : ℕ) : ℝ) * Real.log X) *
        (Real.exp ((C₀ : ℝ) * Real.log X) * c₂ * Real.exp (-η ^ 6 / 4 * ℓ)) *
        Real.exp (-((R : ℝ) - 1) * (1 / 4 + 1 / 60) * ℓ)) =
        Real.exp (Real.log (4 * c₂ ^ 2) + (((C₀ * R : ℕ) : ℝ) * Real.log X +
          (C₀ : ℝ) * Real.log X + (-η ^ 6 / 4 * ℓ) + (-((R : ℝ) - 1) * (1 / 4 + 1 / 60) * ℓ))) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log (by positivity)]
      ring
    rw [e1, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hr1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
    have hprod : 0 ≤ ((R : ℝ) - 1) * (ℓ / 420 - (C₀ : ℝ) * Real.log X) :=
      mul_nonneg (by linarith only [hr1]) (by linarith only [hCX2])
    have hη7ℓ : η ^ 7 * ℓ ≤ η ^ 6 * ℓ / 8 := by
      have := mul_le_mul_of_nonneg_right hη7 (by linarith only [hℓ1] : (0 : ℝ) ≤ ℓ)
      linarith only [this]
    push_cast
    linarith only [hprod, hη7ℓ, hlogA4, hAℓ', hCX1, hnn, hCX2, hr1]

end WaveTurbulence.LGSpine
