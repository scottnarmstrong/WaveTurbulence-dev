/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.CubeSobolev
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Weighted whole-space Sobolev estimates

A product integrable envelope for the mixed derivatives gives an explicit
pointwise bound. The standard envelope is `∏ i, (1 + x_i²)⁻¹`.
-/

public section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The mixed partial derivative selected by a Boolean vector. Each
coordinate is differentiated at most once, in increasing coordinate order. -/
@[expose] noncomputable def mixedPartial : (n : ℕ) → (Fin n → Bool) →
    ((Fin n → ℝ) → E) → (Fin n → ℝ) → E
  | 0, _, f, x => f x
  | n + 1, b, f, x =>
      if b 0 then
        mixedPartial n (Fin.tail b)
          (fun y => deriv (fun s => f (Fin.cons s y)) (x 0)) (Fin.tail x)
      else mixedPartial n (Fin.tail b) (fun y => f (Fin.cons (x 0) y)) (Fin.tail x)

/-- An integrable product envelope for all square-free mixed derivatives
bounds the whole-space Sobolev sum, with its constant displayed explicitly. -/
theorem wholeSobolevL1_le_of_mixedPartial_le {w : ℝ → ℝ≥0∞} (hw : Measurable w) :
    ∀ (n : ℕ) {f : (Fin n → ℝ) → E} {A : ℝ≥0∞},
    (∀ b x, ‖mixedPartial n b f x‖ₑ ≤ A * ∏ i, w (x i)) →
      wholeSobolevL1 n f ≤ (2 * ∫⁻ t, w t) ^ n * A := by
  intro n
  induction n with
  | zero =>
      intro f A h
      simpa only [wholeSobolevL1, mixedPartial, Fin.prod_univ_zero, mul_one,
        pow_zero, one_mul] using h (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  | succ n ih =>
      intro f A h
      have hslice (t : ℝ) :
          wholeSobolevL1 n (fun x => f (Fin.cons t x)) ≤
            (2 * ∫⁻ t, w t) ^ n * (A * w t) := by
        apply ih
        intro b x
        have hh := h (Fin.cons false b) (Fin.cons t x)
        simpa only [mixedPartial, Fin.cons_zero, Bool.false_eq_true, ↓reduceIte,
          Fin.tail_cons, Fin.prod_univ_succ, Fin.cons_succ, mul_assoc] using hh
      have hderiv (t : ℝ) :
          wholeSobolevL1 n (fun x => deriv (fun s => f (Fin.cons s x)) t) ≤
            (2 * ∫⁻ t, w t) ^ n * (A * w t) := by
        apply ih
        intro b x
        have hh := h (Fin.cons true b) (Fin.cons t x)
        simpa only [mixedPartial, Fin.cons_zero, ↓reduceIte,
          Fin.tail_cons, Fin.prod_univ_succ, Fin.cons_succ, mul_assoc] using hh
      calc
        wholeSobolevL1 (n + 1) f ≤
            (∫⁻ t, (2 * ∫⁻ s, w s) ^ n * (A * w t)) +
              ∫⁻ t, (2 * ∫⁻ s, w s) ^ n * (A * w t) :=
          add_le_add (lintegral_mono hslice) (lintegral_mono hderiv)
        _ = (2 * ∫⁻ t, w t) ^ (n + 1) * A := by
          rw [lintegral_const_mul _ (hw.const_mul A), lintegral_const_mul A hw,
            pow_succ]
          ring

/-- Weighted `W^{n,1} → L∞`, the form used in TARGET (incohproof4), L998.
The hypothesis supplies bounds on derivatives rather than an assumed
Sobolev inequality. The envelope is arbitrary and its integral is explicit. -/
theorem enorm_le_of_mixedPartial_le {n : ℕ} {f : (Fin n → ℝ) → E}
    (hf : ContDiff ℝ ∞ f) {w : ℝ → ℝ≥0∞} (hw : Measurable w) {A : ℝ≥0∞}
    (h : ∀ b x, ‖mixedPartial n b f x‖ₑ ≤ A * ∏ i, w (x i)) (x : Fin n → ℝ) :
    ‖f x‖ₑ ≤ (2 * ∫⁻ t, w t) ^ n * A :=
  (enorm_le_wholeSobolevL1 n hf x).trans (wholeSobolevL1_le_of_mixedPartial_le hw n h)

/-- Concrete weighted Sobolev estimate with product Cauchy weights.
In dimension `n` the constant is `(2π)^n`, independent of the function. -/
theorem norm_le_weighted_sobolev {n : ℕ} {f : (Fin n → ℝ) → E}
    (hf : ContDiff ℝ ∞ f) {A : ℝ} (hA : 0 ≤ A)
    (h : ∀ b x, ‖mixedPartial n b f x‖ ≤ A * ∏ i, (1 + (x i) ^ 2)⁻¹)
    (x : Fin n → ℝ) : ‖f x‖ ≤ (2 * Real.pi) ^ n * A := by
  let w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal ((1 + t ^ 2)⁻¹)
  have hw : Measurable w := by dsimp [w]; fun_prop
  have hi : ∫⁻ t, w t = ENNReal.ofReal Real.pi := by
    rw [← ofReal_integral_eq_lintegral_ofReal integrable_inv_one_add_sq
      (Filter.Eventually.of_forall fun t => by positivity), integral_univ_inv_one_add_sq]
  have hh (b : Fin n → Bool) (y : Fin n → ℝ) :
      ‖mixedPartial n b f y‖ₑ ≤ ENNReal.ofReal A * ∏ i, w (y i) := by
    have he := ENNReal.ofReal_le_ofReal (h b y)
    have hp : ENNReal.ofReal (∏ i : Fin n, (1 + (y i) ^ 2)⁻¹) =
        ∏ i : Fin n, w (y i) :=
      ENNReal.ofReal_prod_of_nonneg (fun _ _ => by positivity)
    rw [ofReal_norm, ENNReal.ofReal_mul hA, hp] at he
    exact he
  have he := enorm_le_of_mixedPartial_le hf hw hh x
  rw [hi] at he
  have hc : (2 * ENNReal.ofReal Real.pi) ^ n * ENNReal.ofReal A =
      ENNReal.ofReal ((2 * Real.pi) ^ n * A) := by
    rw [ENNReal.ofReal_mul (pow_nonneg (by positivity) n), ENNReal.ofReal_pow
      (by positivity), ENNReal.ofReal_mul (by norm_num)]
    norm_num
  rw [hc, ← ofReal_norm] at he
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 he

/-- The radial weight `⟨x⟩^{-2n}` is bounded by the integrable product
weight. Squared Euclidean length is written as a coordinate sum. -/
theorem radialWeight_le_productWeight (n : ℕ) (x : Fin n → ℝ) :
    ((1 + ∑ i, (x i) ^ 2) ^ n)⁻¹ ≤ ∏ i, (1 + (x i) ^ 2)⁻¹ := by
  have hprod : ∏ i : Fin n, (1 + (x i) ^ 2) ≤
      (1 + ∑ i, (x i) ^ 2) ^ n := by
    calc
      ∏ i : Fin n, (1 + (x i) ^ 2) ≤
          ∏ _i : Fin n, (1 + ∑ j, (x j) ^ 2) := by
        apply Finset.prod_le_prod₀
        · intro i _
          positivity
        · intro i hi
          have hh := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) hi
          linarith only [hh]
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hp : 0 < ∏ i : Fin n, (1 + (x i) ^ 2) :=
    Finset.prod_pos fun i _ => by positivity
  simpa only [Finset.prod_inv_distrib] using (inv_anti₀ hp hprod)

/-- TARGET (incohproof4), L998: radial weighted derivative bounds give a
uniform bound. The weight is `⟨x⟩^{2n} = (1 + ∑ x_i²)^n`, and all mixed
derivatives used have total order at most `n`. -/
theorem norm_le_radial_weighted_sobolev {n : ℕ} {f : (Fin n → ℝ) → E}
    (hf : ContDiff ℝ ∞ f) {A : ℝ} (hA : 0 ≤ A)
    (h : ∀ b x, ‖mixedPartial n b f x‖ ≤ A * ((1 + ∑ i, (x i) ^ 2) ^ n)⁻¹)
    (x : Fin n → ℝ) : ‖f x‖ ≤ (2 * Real.pi) ^ n * A := by
  apply norm_le_weighted_sobolev hf hA
  intro b y
  exact (h b y).trans (mul_le_mul_of_nonneg_left (radialWeight_le_productWeight n y) hA)

end WaveTurbulence.Analysis
