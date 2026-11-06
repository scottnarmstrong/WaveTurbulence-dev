/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoordinateDerivativeBound
public import WaveTurbulence.Foundations.RegularAsymptotics.CosetSummability
/-! Local lattice majorants for all Fréchet derivatives controlled by a source spatial norm. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set

theorem jbr_le_one_add_norm {d : ℕ} (k : Mom d) : jbr k ≤ 1 + ‖k‖ := by
  unfold jbr
  apply (Real.sqrt_le_iff).mpr
  exact ⟨by positivity, by nlinarith [norm_nonneg k]⟩

theorem jbr_le_of_closedBall {d : ℕ} (k k₀ : Mom d) (hk : k ∈ Metric.closedBall k₀ 1) :
    jbr k ≤ 2 + ‖k₀‖ := by
  have hh : ‖k - k₀‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hk
  have hn : ‖k‖ ≤ 1 + ‖k₀‖ := by
    calc
      _ = ‖(k - k₀) + k₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖k - k₀‖ + ‖k₀‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hh (le_refl ‖k₀‖)
  exact (jbr_le_one_add_norm k).trans (by linarith)

theorem norm_iteratedFDeriv_le_jbr_neg {d A B n : ℕ} (f : Mom d → ℂ)
    (hf : ContDiff ℝ A f) (C : ℝ) (hC : 0 ≤ C)
    (h : SNorm A B f ≤ ENNReal.ofReal C) (hn : n ≤ A) (x : Mom d) :
    ‖iteratedFDeriv ℝ n f x‖ ≤ (d : ℝ) ^ n * C * jbr x ^ (-(B : ℝ)) := by
  have hp := SNorm_frechet_pointwise f hf C hC h hn x
  have hh : ‖iteratedFDeriv ℝ n f x‖ ≤ (d : ℝ) ^ n * C / jbr x ^ B :=
    (le_div_iff₀ (pow_pos (jbr_pos x) B)).mpr (by simpa only [mul_comm] using hp)
  simpa only [Real.rpow_neg (jbr_pos x).le, Real.rpow_natCast, div_eq_mul_inv] using hh

theorem local_frechet_coset_bound {d A B r : ℕ} (hd : 1 ≤ d) (hB : d + 1 ≤ B)
    (f : Mom d → ℂ) (hf : ContDiff ℝ A f) (C : ℝ) (hC : 0 ≤ C)
    (h : SNorm A B f ≤ ENNReal.ofReal C) (hr : r ≤ A) (L : ℝ)
    (k k₀ : Mom d) (hk : k ∈ Metric.closedBall k₀ 1) (z : Fin d → ℤ) :
    ‖iteratedFDeriv ℝ r f (k + latticePoint L z)‖ ≤
      ((d : ℝ) ^ A * C * (Real.sqrt 2 * (2 + ‖k₀‖)) ^ (d + 1)) *
        jbr (latticePoint L z) ^ (-((d : ℝ) + 1)) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hp := norm_iteratedFDeriv_le_jbr_neg f hf C hC h hr (k + latticePoint L z)
  have hpow : (d : ℝ) ^ r ≤ (d : ℝ) ^ A := pow_le_pow_right₀ hd1 hr
  have hb : jbr (k + latticePoint L z) ^ (-(B : ℝ)) ≤
      jbr (k + latticePoint L z) ^ (-((d : ℝ) + 1)) := by
    apply Real.rpow_le_rpow_of_exponent_le (one_le_jbr _)
    have hb' : (d : ℝ) + 1 ≤ B := by exact_mod_cast hB
    exact neg_le_neg hb'
  have hs : (Real.sqrt 2 * jbr k) ^ (d + 1) ≤ (Real.sqrt 2 * (2 + ‖k₀‖)) ^ (d + 1) :=
    pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (jbr_pos k).le)
      (mul_le_mul_of_nonneg_left (jbr_le_of_closedBall k k₀ hk) (Real.sqrt_nonneg _)) _
  have hbr := hb.trans ((jbr_coset_neg_le L k z).trans
    (mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg (jbr_pos _).le _)))
  calc
    _ ≤ ((d : ℝ) ^ r * C) *
        ((Real.sqrt 2 * (2 + ‖k₀‖)) ^ (d + 1) * jbr (latticePoint L z) ^ (-((d : ℝ) + 1))) :=
      hp.trans (mul_le_mul_of_nonneg_left hbr (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hC))
    _ ≤ _ := by
      let K : ℝ := (Real.sqrt 2 * (2 + ‖k₀‖)) ^ (d + 1) *
        jbr (latticePoint L z) ^ (-((d : ℝ) + 1))
      have hK : 0 ≤ K := mul_nonneg (pow_nonneg (by positivity) _)
        (Real.rpow_nonneg (jbr_pos _).le _)
      have he := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hC) hK
      simpa only [K, mul_assoc] using he

end WaveTurbulence.LGSpine
