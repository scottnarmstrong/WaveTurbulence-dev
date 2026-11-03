/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.TimeEuclidean
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Tactic

/-!
# Finiteness of weighted Fourier norms for smooth cutoffs

Schwartz functions have finite time Fourier norms at every real regularity
exponent. Smooth compactly supported cutoffs are a special case.
-/

public section

open MeasureTheory WithLp
open scoped FourierTransform ENNReal ContDiff SchwartzMap

namespace WaveTurbulence.Fourier

private theorem timeBracket_le_euclidean {r : ℕ} (ξ : EuclideanSpace ℝ (Fin r)) :
    timeBracket (ofLp ξ) ≤ 1 + ‖ξ‖ := by
  apply timeBracket_le (by linarith [norm_nonneg ξ])
  intro j
  have hj : |ξ j| ≤ ‖ξ‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le ξ j
  have hs := Real.sq_sqrt (show 0 ≤ 1 + ξ j ^ 2 by positivity)
  have hsp := Real.sqrt_nonneg (1 + ξ j ^ 2)
  have hn := norm_nonneg ξ
  have ha := sq_abs (ξ j)
  have hja := abs_nonneg (ξ j)
  change Real.sqrt (1 + ξ j ^ 2) ≤ 1 + ‖ξ‖
  nlinarith

private theorem schwartz_integrable_one_add_pow {r : ℕ}
    (s : 𝓢(EuclideanSpace ℝ (Fin r), ℂ)) (M : ℕ) :
    Integrable (fun ξ => (1 + ‖ξ‖) ^ M * ‖s ξ‖) := by
  have he : (fun ξ => (1 + ‖ξ‖) ^ M * ‖s ξ‖) =
      fun ξ => ∑ j ∈ Finset.range (M + 1), (M.choose j : ℝ) * (‖ξ‖ ^ j * ‖s ξ‖) := by
    funext ξ
    rw [add_comm, add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    simp only [one_pow]
    ring
  rw [he]
  apply integrable_finsetSum
  intro j _
  exact (s.integrable_pow_mul volume j).const_mul _

/-- Every Schwartz function has finite weighted time Fourier norm. -/
theorem timeFourierNorm_schwartz_lt_top {r : ℕ} (θ : ℝ)
    (s : 𝓢(EuclideanSpace ℝ (Fin r), ℂ)) :
    timeFourierNorm θ (fun t => s (toLp 2 t)) < ⊤ := by
  have hp := PiLp.volume_preserving_toLp (Fin r)
  have hfi : Integrable (fun t => s (toLp 2 t)) :=
    hp.integrable_comp_of_integrable s.integrable
  rw [timeFourierNorm_eq_lintegral hfi]
  rw [← (PiLp.volume_preserving_ofLp (Fin r)).lintegral_comp_emb
    (MeasurableEquiv.toLp 2 (Fin r → ℝ)).symm.measurableEmbedding]
  simp_rw [timeFourier_eq_euclidean, toLp_ofLp]
  let M : ℕ := ⌈max θ 0⌉₊
  have hθM : θ ≤ (M : ℝ) := (le_max_left θ 0).trans (Nat.le_ceil _)
  have he : Integrable (fun ξ => (1 + ‖ξ‖) ^ M * ‖(𝓕 s) ξ‖) :=
    schwartz_integrable_one_add_pow (𝓕 s) M
  have hb (ξ : EuclideanSpace ℝ (Fin r)) :
      timeWeight θ (ofLp ξ) * ‖(𝓕 s) ξ‖ₑ ≤
        ENNReal.ofReal ((1 + ‖ξ‖) ^ M * ‖(𝓕 s) ξ‖) := by
    rw [ENNReal.ofReal_mul (by positivity), ofReal_norm]
    apply mul_le_mul_left _ _
    apply (timeWeight_mono hθM _).trans
    unfold timeWeight
    rw [Real.rpow_natCast]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (timeBracket_pos _).le
      (timeBracket_le_euclidean ξ) M)
  apply lt_of_le_of_lt (lintegral_mono hb)
  rw [← ofReal_integral_eq_lintegral_ofReal he (ae_of_all _ (fun ξ => by positivity))]
  exact ENNReal.ofReal_lt_top

/-- Smooth compactly supported functions have finite time Fourier norm at
all real regularity exponents. -/
theorem timeFourierNorm_lt_top_of_smooth_compact {r : ℕ} (θ : ℝ)
    {f : (Fin r → ℝ) → ℂ} (hf : HasCompactSupport f) (hs : ContDiff ℝ ∞ f) :
    timeFourierNorm θ f < ⊤ := by
  have hc : HasCompactSupport (fun x : EuclideanSpace ℝ (Fin r) => f (ofLp x)) :=
    hf.comp_homeomorph (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r => ℝ)).toHomeomorph
  have hd : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin r) => f (ofLp x)) :=
    hs.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r => ℝ)).contDiff
  let s := hc.toSchwartzMap hd
  have he : (fun t => s (toLp 2 t)) = f := by
    funext t
    change f (ofLp (toLp 2 t)) = f t
    rw [ofLp_toLp]
  simpa only [he] using timeFourierNorm_schwartz_lt_top θ s

end WaveTurbulence.Fourier
