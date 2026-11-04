/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.CoupleExtension
public import WaveTurbulence.Foundations.Incoh.ConstantAbsorption

/-!
# Couple decay with the exponential constant independent of the clock cutoff

TARGET Proposition 5.1 permits external boxes above the root layers. Enlarging the clock
cutoff must change only the lattice threshold, since the parameter prefix fixes C₁ before
choosing the total number of layers. Keep the time-integration cost outside the order power
and absorb it into the existing exponent slack.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff ENNReal

namespace WaveTurbulence.Incoh

/-- TARGET (incohproof20), with the dimensional exponential constant chosen before the cutoff. -/
theorem exists_coupleExtension_cutoffUniform_decay (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 3 →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        1 ≤ incoherenceCount Q →
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I → I ⊆ univ.pi (fun i => linkBox (Q i)) →
        ∀ R : RootCoordinates n,
        Fourier.timeFourierNorm η (R.coupleExtension χ L γ δ Q I) ≤
          ENNReal.ofReal ((C * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q)) := by
  obtain ⟨C, hC, hb⟩ := exists_rootDensity_Lp_bound d hd
  refine ⟨C, hC, ?_⟩
  intro η hη hη₁ χ hχ hcχ
  obtain ⟨Cₜ, hCₜ, htime, _⟩ := Fourier.exists_cutoff_timeIntegral_bounds hη hη₁ hχ hcχ
  obtain ⟨Lₐ, hLₐ, ha⟩ := exists_constant_absorption_threshold Cₜ hη
  intro γ hγ hηg δ hδ hδ₁ D hD
  obtain ⟨Lᵦ, hLᵦ, hb⟩ := hb γ hγ η hη hηg δ hδ hδ₁ D hD
  refine ⟨max Lₐ Lᵦ, hLₐ.trans (le_max_left _ _), ?_⟩
  intro L hL n Q hg hspan I hI hbox R
  have hLa := (le_max_left Lₐ Lᵦ).trans hL
  have hLb := (le_max_right Lₐ Lᵦ).trans hL
  have hLone := hLₐ.trans hLa
  have hLp := zero_lt_one.trans_le hLone
  have hCt : Cₜ ≤ L ^ (η * incoherenceCount Q) := (ha L hLa).trans
    (Real.rpow_le_rpow_of_exponent_le hLone (by
      have hgR : 1 ≤ (incoherenceCount Q : ℝ) := by exact_mod_cast hg
      nlinarith only [hgR, hη.le]))
  rw [R.timeFourierNorm_coupleExtension]
  apply (htime (R.localLinkDensity L γ δ Q I)).trans
  have hroot := hb L hLb n Q hg hspan I hI hbox R
  rw [← R.eLpNorm_localLinkDensity hLp γ δ Q hI hbox] at hroot
  apply (mul_le_mul' (ENNReal.ofReal_le_ofReal hCt) hroot).trans
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hLp.le _)]
  apply ENNReal.ofReal_le_ofReal
  have hexp : η * incoherenceCount Q +
      (-(incoherenceExponent d γ - 8 * (d : ℝ) * η) * incoherenceCount Q) ≤
      -(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q := by
    have hgR : 0 ≤ (incoherenceCount Q : ℝ) := Nat.cast_nonneg _
    have hdR : 3 ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith only [mul_nonneg hη.le hgR, mul_nonneg (sub_nonneg.mpr hdR) (mul_nonneg hη.le hgR)]
  calc
    _ = (C * δ) ^ n * L ^ (η * incoherenceCount Q +
        (-(incoherenceExponent d γ - 8 * (d : ℝ) * η) * incoherenceCount Q)) := by
      rw [Real.rpow_add hLp]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hLone hexp)
      (pow_nonneg (mul_nonneg hC.le hδ.le) _)

end WaveTurbulence.Incoh
