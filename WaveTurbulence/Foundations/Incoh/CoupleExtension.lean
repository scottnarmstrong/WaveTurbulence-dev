/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.LocalRootDensity
public import WaveTurbulence.Foundations.Incoh.LinkCounting
public import WaveTurbulence.Foundations.Fourier.TimeIntegralBounds

/-!
# The positive Fourier bound for the actual couple density

TARGET (incohproof17)–(incohproof20). Form the cutoff double integral of
the actual local-clock root marginal, translate back to physical clocks,
and apply the landed time-integration theorem. No endpoint estimate is assumed.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Incoh

/-- The canonical cutoff double integral in the original root clocks. -/
@[expose] def RootCoordinates.coupleExtension {d n : ℕ} (R : RootCoordinates n)
    (χ : ℝ → ℝ) (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (t : Fin 2 → ℝ) : ℂ :=
  Fourier.cutoffDoubleIntegral χ (R.localLinkDensity L γ δ Q I) (t - R.baseRootTimes Q)

/-- Returning from local clocks preserves the weighted Fourier norm exactly. -/
theorem RootCoordinates.timeFourierNorm_coupleExtension {d n : ℕ} (R : RootCoordinates n)
    (χ : ℝ → ℝ) (L γ δ θ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ)) :
    Fourier.timeFourierNorm θ (R.coupleExtension χ L γ δ Q I) =
      Fourier.timeFourierNorm θ (Fourier.cutoffDoubleIntegral χ (R.localLinkDensity L γ δ Q I)) := by
  have heq : R.coupleExtension χ L γ δ Q I =
      fun t => Fourier.cutoffDoubleIntegral χ (R.localLinkDensity L γ δ Q I) (t + -(R.baseRootTimes Q)) := by
    funext t
    rw [coupleExtension, sub_eq_add_neg]
  rw [heq, Fourier.timeFourierNorm_translate]

/-- TARGET (incohproof20), with the actual localized couple extension and a single base constant. -/
theorem exists_coupleExtension_timeFourier_bound (d : ℕ) (hd : 3 ≤ d)
    (η : ℝ) (hη : 0 < η) (hη₁ : η ≤ 1 / 3)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        1 ≤ incoherenceCount Q →
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I → I ⊆ univ.pi (fun i => linkBox (Q i)) →
        ∀ R : RootCoordinates n,
        Fourier.timeFourierNorm η (R.coupleExtension χ L γ δ Q I) ≤
          ENNReal.ofReal ((C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q)) := by
  obtain ⟨C, hC, hb⟩ := exists_rootDensity_Lp_bound d hd
  obtain ⟨Cₜ, hCₜ, htime, _⟩ := Fourier.exists_cutoff_timeIntegral_bounds hη hη₁ hχ hcχ
  let C₀ : ℝ := (Cₜ + 1) * C
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ hηg δ hδ hδ₁ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb γ hγ η hη hηg δ hδ hδ₁ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n Q hg hspan I hI hbox R
  have hLone := hL₀.trans hL
  have hLp := zero_lt_one.trans_le hLone
  have hn : n ≠ 0 := by have h := one_le_linkCount_of_incoherent Q hg; omega
  have hCpow : Cₜ ≤ (Cₜ + 1) ^ n :=
    (by linarith : Cₜ ≤ Cₜ + 1).trans (le_self_pow₀ (by linarith : 1 ≤ Cₜ + 1) hn)
  have hcoef : Cₜ * (C * δ) ^ n ≤ (C₀ * δ) ^ n := by
    calc
      _ ≤ (Cₜ + 1) ^ n * (C * δ) ^ n := mul_le_mul_of_nonneg_right hCpow (by positivity)
      _ = _ := by rw [← mul_pow]; congr 1; dsimp [C₀]; ring
  have hexp : -(incoherenceExponent d γ - 8 * (d : ℝ) * η) * incoherenceCount Q ≤
      -(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q := by
    have h := mul_nonneg (Nat.cast_nonneg d) hη.le
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg (incoherenceCount Q))
    nlinarith only [h]
  rw [R.timeFourierNorm_coupleExtension]
  apply (htime (R.localLinkDensity L γ δ Q I)).trans
  calc
    _ ≤ ENNReal.ofReal Cₜ * ENNReal.ofReal ((C * δ) ^ n *
        L ^ (-(incoherenceExponent d γ - 8 * (d : ℝ) * η) * incoherenceCount Q)) := by
      apply mul_le_mul' le_rfl
      rw [R.eLpNorm_localLinkDensity hLp γ δ Q hI hbox]
      exact hb L hL n Q hg hspan I hI hbox R
    _ = ENNReal.ofReal ((Cₜ * (C * δ) ^ n) *
        L ^ (-(incoherenceExponent d γ - 8 * (d : ℝ) * η) * incoherenceCount Q)) := by
      rw [← ENNReal.ofReal_mul hCₜ.le]
      congr 1
      ring
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul (hcoef) (Real.rpow_le_rpow_of_exponent_le hLone hexp)
        (Real.rpow_nonneg hLp.le _) (by positivity)

end WaveTurbulence.Incoh
