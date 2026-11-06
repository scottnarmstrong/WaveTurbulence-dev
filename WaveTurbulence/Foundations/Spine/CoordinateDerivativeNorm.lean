/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.WeightedSmoothMultiplier
public import WaveTurbulence.Foundations.Sumint.Words
/-! Coordinate differentiation preserves quantitative finite-order spatial decay bounds. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open NormBridgeScratch
open scoped ContDiff

theorem norm_frechet_partialMom_le {d n : ℕ} (j : Fin d) (f : Mom d → ℂ)
    (hf : ContDiff ℝ (n + 1 : ℕ) f) (x : Mom d) :
    ‖iteratedFDeriv ℝ n (partialMom j f) x‖ ≤ ‖iteratedFDeriv ℝ (n + 1) f x‖ := by
  have hc := (hf.fderiv_right (m := n) (by simp)).contDiffAt (x := x)
  have h := norm_iteratedFDeriv_clm_apply_const (c := EuclideanSpace.single j (1 : ℝ))
    hc (le_refl (n : ℕ∞ω))
  have he : partialMom j f = fun y => fderiv ℝ f y (EuclideanSpace.single j 1) := rfl
  rw [he]
  simpa only [PiLp.norm_single, norm_one, one_mul, norm_iteratedFDeriv_fderiv] using h

theorem norm_frechet_wordD_le {d n : ℕ} (word : List (Fin d)) (f : Mom d → ℂ)
    (hf : ContDiff ℝ (n + word.length : ℕ) f) (x : Mom d) :
    ‖iteratedFDeriv ℝ n (wordD word f) x‖ ≤ ‖iteratedFDeriv ℝ (n + word.length) f x‖ := by
  induction word generalizing n with
  | nil => exact le_rfl
  | cons j word ih =>
    have hf' : ContDiff ℝ ((n + 1) + word.length : ℕ) f := by
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hf
    have hc := wordD_contDiff word (n + 1) hf'
    have h := (norm_frechet_partialMom_le j (wordD word f) hc x).trans (ih hf')
    have he : n + 1 + word.length = n + (j :: word).length := by
      simp only [List.length_cons]
      omega
    rw [he] at h
    exact h

/-- An input modified by a fixed coordinate derivative word remains controlled by its
higher-order source seminorm, with a constant independent of all other inputs. -/
theorem SNorm_wordD_bound {d A B : ℕ} (hd : 1 ≤ d) (word : List (Fin d))
    (f : Mom d → ℂ) (hf : ContDiff ℝ (A + word.length : ℕ) f)
    (C : ℝ) (hC : 0 ≤ C) (hF : SNorm (A + word.length) B f ≤ ENNReal.ofReal C) :
    SNorm A B (wordD word f) ≤ ENNReal.ofReal ((d : ℝ) ^ (A + word.length) * C) := by
  apply SNorm_le_of_momentum_bounds _ (wordD_contDiff word A hf)
  intro n hn ρ x
  have hfn : ContDiff ℝ (n + word.length : ℕ) f :=
    hf.of_le (by exact_mod_cast Nat.add_le_add_right hn word.length)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  calc
    _ ≤ jbr x ^ B * ‖iteratedFDeriv ℝ n (wordD word f) x‖ :=
      mul_le_mul_of_nonneg_left (norm_momentumDerivative_le_frechet _ ρ x) (pow_nonneg (jbr_pos x).le _)
    _ ≤ jbr x ^ B * ‖iteratedFDeriv ℝ (n + word.length) f x‖ :=
      mul_le_mul_of_nonneg_left (norm_frechet_wordD_le word f hfn x) (pow_nonneg (jbr_pos x).le _)
    _ ≤ (d : ℝ) ^ (n + word.length) * C :=
      SNorm_frechet_pointwise f hf C hC hF (Nat.add_le_add_right hn _) x
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hd1 (Nat.add_le_add_right hn _)) hC

end WaveTurbulence.LGSpine
