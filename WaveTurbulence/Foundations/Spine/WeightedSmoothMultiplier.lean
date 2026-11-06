/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoordinateDerivativeBound
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Data.Nat.Choose.Sum
/-! A finite-order weighted multiplier bound for the individually modified input profiles. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset

theorem norm_momentumDerivative_le_frechet {d n : ℕ} (f : Mom d → ℂ)
    (ρ : Fin n → Fin d) (x : Mom d) :
    ‖Fourier.momentumDerivative ρ f x‖ ≤ ‖iteratedFDeriv ℝ n f x‖ := by
  unfold Fourier.momentumDerivative
  have h := (iteratedFDeriv ℝ n f x).le_opNorm (fun i => EuclideanSpace.single (ρ i) (1 : ℝ))
  simpa using h

/-- A smooth multiplier whose derivatives grow like the M-th power of the momentum bracket
maps the source (A,B+M) norm to (A,B). All constants are independent of the leaf identity. -/
theorem SNorm_mul_of_polynomial_jet_bound {d A B M : ℕ} (hd : 1 ≤ d)
    (P f : Mom d → ℂ) (hP : ContDiff ℝ A P) (hf : ContDiff ℝ A f)
    (CP CF : ℝ) (hCP : 0 ≤ CP) (hCF : 0 ≤ CF)
    (hjet : ∀ r ≤ A, ∀ x, ‖iteratedFDeriv ℝ r P x‖ ≤ CP * jbr x ^ M)
    (hF : SNorm A (B + M) f ≤ ENNReal.ofReal CF) :
    SNorm A B (fun x => P x * f x) ≤ ENNReal.ofReal ((2 : ℝ) ^ A * (d : ℝ) ^ A * CP * CF) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  apply WaveTurbulence.Induct.SNorm_le_of_momentum_bounds _ (hP.mul hf)
  intro n hn ρ x
  apply (mul_le_mul_of_nonneg_left (norm_momentumDerivative_le_frechet _ ρ x)
    (pow_nonneg (WaveTurbulence.Induct.jbr_pos x).le B)).trans
  apply (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_mul_le hP hf x
    (by exact_mod_cast hn)) (pow_nonneg (WaveTurbulence.Induct.jbr_pos x).le B)).trans
  rw [mul_sum]
  have hterm (i : ℕ) (hi : i ∈ range (n + 1)) :
      jbr x ^ B * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i P x‖ *
        ‖iteratedFDeriv ℝ (n - i) f x‖) ≤
      (n.choose i : ℝ) * ((d : ℝ) ^ A * CP * CF) := by
    have hiA : i ≤ A := (Nat.lt_succ_iff.mp (mem_range.mp hi)).trans hn
    have hni : n - i ≤ A := (Nat.sub_le _ _).trans hn
    have hf0 := SNorm_frechet_pointwise f hf CF hCF hF hni x
    have hf1 : jbr x ^ (B + M) * ‖iteratedFDeriv ℝ (n - i) f x‖ ≤ (d : ℝ) ^ A * CF :=
      hf0.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hd1 hni) hCF)
    have hp0 := mul_le_mul_of_nonneg_left (hjet i hiA x) (pow_nonneg (WaveTurbulence.Induct.jbr_pos x).le B)
    have hp1 := mul_le_mul_of_nonneg_right hp0 (norm_nonneg (iteratedFDeriv ℝ (n - i) f x))
    have heq : (jbr x ^ B * (CP * jbr x ^ M)) * ‖iteratedFDeriv ℝ (n - i) f x‖ =
        CP * (jbr x ^ (B + M) * ‖iteratedFDeriv ℝ (n - i) f x‖) := by rw [pow_add]; ring
    rw [heq] at hp1
    have hb := hp1.trans (mul_le_mul_of_nonneg_left hf1 hCP)
    have hc := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (n.choose i) : 0 ≤ (n.choose i : ℝ))
    calc
      _ = (n.choose i : ℝ) * (jbr x ^ B * ‖iteratedFDeriv ℝ i P x‖ *
          ‖iteratedFDeriv ℝ (n - i) f x‖) := by ring
      _ ≤ _ := by simpa only [mul_assoc, mul_left_comm, mul_comm] using hc
  apply (sum_le_sum hterm).trans
  rw [← sum_mul]
  have hsum : (∑ i ∈ range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
    simpa only [one_pow, one_mul, one_add_one_eq_two] using (add_pow (1 : ℝ) 1 n).symm
  rw [hsum]
  have hc : 0 ≤ (d : ℝ) ^ A * CP * CF := by positivity
  have hh := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn) hc
  simpa only [mul_assoc] using hh

end WaveTurbulence.LGSpine
