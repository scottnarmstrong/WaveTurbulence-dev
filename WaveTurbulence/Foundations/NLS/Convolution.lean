/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NLS.AkSystem

/-!
# Weighted `ℓ¹` estimates for the cubic convolution of the `a`-system

On `ℤ^d` (indices `n : Fin d → ℤ`, sup norm) with weights `wt s n = (1 + ‖n‖)^s`, the weighted
`ℓ¹` norm `wnorm s f = ∑ₙ (1 + ‖n‖)^s |f n|` and the absolute cubic sum
`tripleAbs f g h n = ∑_{(n₁,n₂)} |f n₁| |g n₂| |h (n - n₁ + n₂)|` satisfy (all in `ℝ≥0∞`, so no
summability side conditions)

* `tsum_wt_mul_tripleAbs_le`: `∑ₙ wt s n · tripleAbs f g h n ≤ wnorm s f · wnorm s g · wnorm s h`;
* `tsum_wt_mul_tripleAbs_le_tame`: the tame bound
  `≤ 3^s (wnorm s f · wnorm 0 g · wnorm 0 h + wnorm 0 f · wnorm s g · wnorm 0 h +
  wnorm 0 f · wnorm 0 g · wnorm s h)`;

and the nonlinearity `𝒞_ζ` of (akeqn2) (TARGET L553–L554) is dominated by it:
`enorm_aNonlin_le : |𝒞_ζ(f,g,h)ₙ(t)| ≤ |δ/(2L^{d-γ})| · tripleAbs f g h n`.

These are the estimates behind the local theory of the `a`-system in the weighted `ℓ¹` (Wiener)
scale, used here in place of `H^s`, `s > d/2` (packet NLS goal 5).
-/

public section

noncomputable section

open MeasureTheory Complex Set
open scoped ENNReal

namespace WaveTurbulence.NLS

variable {d : ℕ}

/-- The weight `(1 + ‖n‖)^s` on `ℤ^d`. -/
@[expose] def wt (s : ℕ) (n : Fin d → ℤ) : ℝ≥0∞ := ENNReal.ofReal (1 + ‖n‖) ^ s

/-- The weighted `ℓ¹` norm `∑ₙ (1 + ‖n‖)^s |f n|`. -/
@[expose] def wnorm (s : ℕ) (f : (Fin d → ℤ) → ℂ) : ℝ≥0∞ := ∑' n, wt s n * ‖f n‖ₑ

/-- The absolute cubic sum `∑_{(n₁,n₂)} |f n₁| |g n₂| |h (n - n₁ + n₂)|`. -/
@[expose] def tripleAbs (f g h : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ) : ℝ≥0∞ :=
  ∑' p : (Fin d → ℤ) × (Fin d → ℤ), ‖f p.1‖ₑ * ‖g p.2‖ₑ * ‖h (n - p.1 + p.2)‖ₑ

/-! ### Weights -/

theorem one_add_norm_sub_add_le (n₁ n₂ n₃ : Fin d → ℤ) :
    1 + ‖n₁ - n₂ + n₃‖ ≤ 1 + ‖n₁‖ + ‖n₂‖ + ‖n₃‖ := by
  have h := norm_add_le (n₁ - n₂) n₃
  have h' := norm_sub_le n₁ n₂
  linarith

theorem wt_sub_add_le (s : ℕ) (n₁ n₂ n₃ : Fin d → ℤ) :
    wt s (n₁ - n₂ + n₃) ≤ wt s n₁ * wt s n₂ * wt s n₃ := by
  simp only [wt, ← mul_pow]
  gcongr
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h := one_add_norm_sub_add_le n₁ n₂ n₃
  have h1 := norm_nonneg n₁
  have h2 := norm_nonneg n₂
  have h3 := norm_nonneg n₃
  nlinarith [mul_nonneg h1 h2, mul_nonneg (mul_nonneg h1 h2) h3, mul_nonneg h1 h3,
    mul_nonneg h2 h3]

theorem wt_sub_add_le_tame (s : ℕ) (n₁ n₂ n₃ : Fin d → ℤ) :
    wt s (n₁ - n₂ + n₃) ≤ 3 ^ s * (wt s n₁ + wt s n₂ + wt s n₃) := by
  have hreal : (1 + ‖n₁ - n₂ + n₃‖) ^ s ≤
      3 ^ s * ((1 + ‖n₁‖) ^ s + (1 + ‖n₂‖) ^ s + (1 + ‖n₃‖) ^ s) := by
    set M := max (max (1 + ‖n₁‖) (1 + ‖n₂‖)) (1 + ‖n₃‖)
    have hM : 1 + ‖n₁ - n₂ + n₃‖ ≤ 3 * M := by
      have h := one_add_norm_sub_add_le n₁ n₂ n₃
      have h1 : 1 + ‖n₁‖ ≤ M := le_max_of_le_left (le_max_left _ _)
      have h2 : 1 + ‖n₂‖ ≤ M := le_max_of_le_left (le_max_right _ _)
      have h3 : 1 + ‖n₃‖ ≤ M := le_max_right _ _
      linarith [norm_nonneg n₁, norm_nonneg n₂, norm_nonneg n₃]
    have hMs : M ^ s ≤ (1 + ‖n₁‖) ^ s + (1 + ‖n₂‖) ^ s + (1 + ‖n₃‖) ^ s := by
      have p1 : 0 ≤ (1 + ‖n₁‖) ^ s := by positivity
      have p2 : 0 ≤ (1 + ‖n₂‖) ^ s := by positivity
      have p3 : 0 ≤ (1 + ‖n₃‖) ^ s := by positivity
      rcases max_cases (max (1 + ‖n₁‖) (1 + ‖n₂‖)) (1 + ‖n₃‖) with ⟨h, -⟩ | ⟨h, -⟩ <;>
        simp only [M, h]
      · rcases max_cases (1 + ‖n₁‖) (1 + ‖n₂‖) with ⟨h', -⟩ | ⟨h', -⟩ <;> rw [h'] <;> linarith
      · linarith
    calc (1 + ‖n₁ - n₂ + n₃‖) ^ s ≤ (3 * M) ^ s :=
          pow_le_pow_left₀ (by positivity) hM s
      _ = 3 ^ s * M ^ s := mul_pow _ _ _
      _ ≤ 3 ^ s * ((1 + ‖n₁‖) ^ s + (1 + ‖n₂‖) ^ s + (1 + ‖n₃‖) ^ s) := by gcongr
  have e : ∀ x : Fin d → ℤ, ENNReal.ofReal (1 + ‖x‖) ^ s = ENNReal.ofReal ((1 + ‖x‖) ^ s) :=
    fun x => (ENNReal.ofReal_pow (by positivity) s).symm
  simp only [wt, e]
  calc ENNReal.ofReal ((1 + ‖n₁ - n₂ + n₃‖) ^ s)
      ≤ ENNReal.ofReal (3 ^ s * ((1 + ‖n₁‖) ^ s + (1 + ‖n₂‖) ^ s + (1 + ‖n₃‖) ^ s)) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = 3 ^ s * (ENNReal.ofReal ((1 + ‖n₁‖) ^ s) + ENNReal.ofReal ((1 + ‖n₂‖) ^ s) +
          ENNReal.ofReal ((1 + ‖n₃‖) ^ s)) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_pow (by norm_num)]
        norm_num

/-! ### The weighted sum of `tripleAbs` -/

/-- Reindexing `n₃ = n - n₁ + n₂`. -/
theorem tsum_wt_mul_tripleAbs (s : ℕ) (f g h : (Fin d → ℤ) → ℂ) :
    ∑' n, wt s n * tripleAbs f g h n =
      ∑' n₁, ∑' n₂, ∑' n₃, wt s (n₁ - n₂ + n₃) * (‖f n₁‖ₑ * ‖g n₂‖ₑ * ‖h n₃‖ₑ) := by
  simp only [tripleAbs, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm, ENNReal.tsum_prod']
  refine tsum_congr fun n₁ => tsum_congr fun n₂ => ?_
  rw [← (Equiv.addRight (n₁ - n₂)).tsum_eq]
  refine tsum_congr fun n₃ => ?_
  simp only [Equiv.coe_addRight]
  have h1 : n₃ + (n₁ - n₂) - n₁ + n₂ = n₃ := by abel
  have h2 : n₃ + (n₁ - n₂) = n₁ - n₂ + n₃ := by abel
  rw [h1, h2]

theorem tsum_wt_mul_tripleAbs_le (s : ℕ) (f g h : (Fin d → ℤ) → ℂ) :
    ∑' n, wt s n * tripleAbs f g h n ≤ wnorm s f * wnorm s g * wnorm s h := by
  rw [tsum_wt_mul_tripleAbs]
  calc ∑' n₁, ∑' n₂, ∑' n₃, wt s (n₁ - n₂ + n₃) * (‖f n₁‖ₑ * ‖g n₂‖ₑ * ‖h n₃‖ₑ)
      ≤ ∑' n₁, ∑' n₂, ∑' n₃, (wt s n₁ * ‖f n₁‖ₑ) * (wt s n₂ * ‖g n₂‖ₑ) * (wt s n₃ * ‖h n₃‖ₑ) := by
        refine ENNReal.tsum_le_tsum fun n₁ => ENNReal.tsum_le_tsum fun n₂ =>
          ENNReal.tsum_le_tsum fun n₃ => ?_
        calc wt s (n₁ - n₂ + n₃) * (‖f n₁‖ₑ * ‖g n₂‖ₑ * ‖h n₃‖ₑ)
            ≤ (wt s n₁ * wt s n₂ * wt s n₃) * (‖f n₁‖ₑ * ‖g n₂‖ₑ * ‖h n₃‖ₑ) := by
              gcongr
              exact wt_sub_add_le s n₁ n₂ n₃
          _ = (wt s n₁ * ‖f n₁‖ₑ) * (wt s n₂ * ‖g n₂‖ₑ) * (wt s n₃ * ‖h n₃‖ₑ) := by ring
    _ = wnorm s f * wnorm s g * wnorm s h := by
        simp only [wnorm, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]

theorem tsum_wt_mul_tripleAbs_le_tame (s : ℕ) (f g h : (Fin d → ℤ) → ℂ) :
    ∑' n, wt s n * tripleAbs f g h n ≤
      3 ^ s * (wnorm s f * wnorm 0 g * wnorm 0 h + wnorm 0 f * wnorm s g * wnorm 0 h +
        wnorm 0 f * wnorm 0 g * wnorm s h) := by
  rw [tsum_wt_mul_tripleAbs]
  have hw0 : ∀ n : Fin d → ℤ, wt 0 n = 1 := fun n => by simp [wt]
  calc ∑' n₁, ∑' n₂, ∑' n₃, wt s (n₁ - n₂ + n₃) * (‖f n₁‖ₑ * ‖g n₂‖ₑ * ‖h n₃‖ₑ)
      ≤ ∑' n₁, ∑' n₂, ∑' n₃, 3 ^ s *
          ((wt s n₁ * ‖f n₁‖ₑ) * (wt 0 n₂ * ‖g n₂‖ₑ) * (wt 0 n₃ * ‖h n₃‖ₑ) +
            (wt 0 n₁ * ‖f n₁‖ₑ) * (wt s n₂ * ‖g n₂‖ₑ) * (wt 0 n₃ * ‖h n₃‖ₑ) +
            (wt 0 n₁ * ‖f n₁‖ₑ) * (wt 0 n₂ * ‖g n₂‖ₑ) * (wt s n₃ * ‖h n₃‖ₑ)) := by
        refine ENNReal.tsum_le_tsum fun n₁ => ENNReal.tsum_le_tsum fun n₂ =>
          ENNReal.tsum_le_tsum fun n₃ => ?_
        calc wt s (n₁ - n₂ + n₃) * (‖f n₁‖ₑ * ‖g n₂‖ₑ * ‖h n₃‖ₑ)
            ≤ (3 ^ s * (wt s n₁ + wt s n₂ + wt s n₃)) * (‖f n₁‖ₑ * ‖g n₂‖ₑ * ‖h n₃‖ₑ) := by
              gcongr
              exact wt_sub_add_le_tame s n₁ n₂ n₃
          _ = _ := by simp only [hw0]; ring
    _ = _ := by
        simp only [ENNReal.tsum_mul_left, ENNReal.tsum_add, ENNReal.tsum_mul_right, wnorm]

/-! ### The nonlinearity -/

theorem aNonlin_eq_tsum_pairs (L γ δ : ℝ) (ζ : ℤ) (t : ℝ) (f g h : (Fin d → ℤ) → ℂ)
    (n : Fin d → ℤ) :
    aNonlin L γ δ ζ t f g h n =
      ((δ / (2 * L ^ ((d : ℝ) - γ)) : ℝ) : ℂ) * (I * ζ) *
        ∑' q : (Fin d → ℤ) × (Fin d → ℤ),
          (epsCoef q.1 q.2 (n - q.1 + q.2) : ℂ) *
            exp (((ζ * Real.pi * δ * L ^ (2 * γ) * resonance L q.1 q.2 (n - q.1 + q.2) n * t :
              ℝ) : ℂ) * I) * f q.1 * g q.2 * h (n - q.1 + q.2) := by
  rw [aNonlin, ← (resonantEquiv n).tsum_eq]
  rfl

/-- The nonlinearity of (akeqn2) is dominated by the absolute cubic sum. -/
theorem enorm_aNonlin_le (L γ δ t : ℝ) (f g h : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ) :
    ‖aNonlin L γ δ 1 t f g h n‖ₑ ≤
      ENNReal.ofReal |δ / (2 * L ^ ((d : ℝ) - γ))| * tripleAbs f g h n := by
  rw [aNonlin_eq_tsum_pairs, enorm_mul, enorm_mul]
  have hI : ‖I * ((1 : ℤ) : ℂ)‖ₑ = 1 := by simp [← ofReal_norm]
  rw [hI, mul_one]
  gcongr
  · rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
  · refine enorm_tsum_le_tsum_enorm.trans (ENNReal.tsum_le_tsum fun q => ?_)
    simp only [enorm_mul]
    have he : ‖((epsCoef q.1 q.2 (n - q.1 + q.2) : ℝ) : ℂ)‖ₑ ≤ 1 := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
      exact ENNReal.ofReal_le_one.2 (abs_epsCoef_le _ _ _)
    have hp : ‖exp (((((1 : ℤ) : ℝ) * Real.pi * δ * L ^ (2 * γ) *
        resonance L q.1 q.2 (n - q.1 + q.2) n * t : ℝ) : ℂ) * I)‖ₑ = 1 := by
      rw [← ofReal_norm, Complex.norm_exp_ofReal_mul_I, ENNReal.ofReal_one]
    rw [hp, mul_one]
    calc ‖((epsCoef q.1 q.2 (n - q.1 + q.2) : ℝ) : ℂ)‖ₑ * ‖f q.1‖ₑ * ‖g q.2‖ₑ *
          ‖h (n - q.1 + q.2)‖ₑ
        ≤ 1 * ‖f q.1‖ₑ * ‖g q.2‖ₑ * ‖h (n - q.1 + q.2)‖ₑ := by gcongr
      _ = ‖f q.1‖ₑ * ‖g q.2‖ₑ * ‖h (n - q.1 + q.2)‖ₑ := by rw [one_mul]

end WaveTurbulence.NLS
