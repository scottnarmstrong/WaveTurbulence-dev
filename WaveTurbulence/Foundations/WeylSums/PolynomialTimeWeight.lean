/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.DyadicTimeIntegral

/-! # Japanese-bracket weights with uniformly summable tails -/

public section
open MeasureTheory
namespace WaveTurbulence.WeylSums

/-- `⟨s/B⟩⁻ᴾ`, with the Euclidean Japanese bracket convention. -/
@[expose] noncomputable def japaneseTimeWeight (B P s : ℝ) : ℝ :=
  (1+(s/B)^2)^(-P/2)

theorem japaneseTimeWeight_nonneg (B P s : ℝ) : 0 ≤ japaneseTimeWeight B P s :=
  Real.rpow_nonneg (by positivity) _

@[fun_prop] theorem continuous_japaneseTimeWeight (B P : ℝ) :
    Continuous (japaneseTimeWeight B P) := by
  apply Continuous.rpow_const (by fun_prop)
  intro s
  left
  positivity

theorem japaneseTimeWeight_le_one (B s : ℝ) {P : ℝ} (hP : 0 ≤ P) :
    japaneseTimeWeight B P s ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith only [sq_nonneg (s/B)]) (by linarith)

/-- A fixed decay exponent below `P/2` controls every dyadic annulus. -/
theorem japaneseTimeWeight_dyadic {B k P : ℝ} (hB : 0 < B) (hk : 0 ≤ k)
    (hP : 2*k ≤ P) (n : ℕ) (s : ℝ) (hs : B*(2 : ℝ)^n ≤ |s|) :
    japaneseTimeWeight B P s ≤ ((2 : ℝ)^(-2*k))^n := by
  have hbase : 1 ≤ 1+(s/B)^2 := by nlinarith only [sq_nonneg (s/B)]
  have hsdiv : (2 : ℝ)^n ≤ |s/B| := by
    rw [abs_div, abs_of_pos hB, le_div_iff₀ hB]
    nlinarith only [hs]
  have hsq : ((2 : ℝ)^n)^2 ≤ 1+(s/B)^2 := by
    have hh := sq_le_sq₀ (by positivity : (0 : ℝ) ≤ 2^n) (abs_nonneg (s/B)) |>.mpr hsdiv
    rw [sq_abs] at hh
    linarith
  calc
    _ ≤ (1+(s/B)^2)^(-k) :=
      Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
    _ ≤ (((2 : ℝ)^n)^2)^(-k) := Real.rpow_le_rpow_of_nonpos (by positivity) hsq (by linarith)
    _ = ((2 : ℝ)^(-2*k))^n := by
      rw [← Real.rpow_two, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2^n),
        ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring

/-- Polynomially weighted integrals follow from cumulative power bounds,
uniformly over all `P≥2k`, provided `r<2k`. -/
theorem japanese_weighted_integral_bound (μ : Measure ℝ) (g : ℝ → ℝ)
    (hg : ∀ s, 0 ≤ g s) (B K r k P : ℝ) (hB : 0 < B) (hK : 0 ≤ K)
    (hk : 0 ≤ k) (hrk : r < 2*k) (hP : 2*k ≤ P)
    (hi : ∀ U : ℝ, 0 < U → IntegrableOn g {s : ℝ | |s| ≤ U} μ)
    (hb : ∀ U : ℝ, 0 < U → (∫ s in {s : ℝ | |s| ≤ U}, g s ∂μ) ≤ K*U^r) :
    Integrable (fun s => japaneseTimeWeight B P s*g s) μ ∧
      (∫ s, japaneseTimeWeight B P s*g s ∂μ) ≤
        K*B^r*(1+(2 : ℝ)^r/(1-(2 : ℝ)^(r-2*k))) := by
  have hqeq : (2 : ℝ)^(-2*k)*(2 : ℝ)^r = (2 : ℝ)^(r-2*k) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hq : (2 : ℝ)^(-2*k)*(2 : ℝ)^r < 1 := by
    rw [hqeq]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hh := dyadic_weighted_integral_bound μ g (japaneseTimeWeight B P) hg
    (japaneseTimeWeight_nonneg B P) (continuous_japaneseTimeWeight B P).measurable
    B K r ((2 : ℝ)^(-2*k)) hB hK (by positivity) hq hi hb
    (fun s => japaneseTimeWeight_le_one B s (by linarith))
    (fun n s hs => japaneseTimeWeight_dyadic hB hk hP n s hs)
  simpa only [hqeq] using hh

end WaveTurbulence.WeylSums
