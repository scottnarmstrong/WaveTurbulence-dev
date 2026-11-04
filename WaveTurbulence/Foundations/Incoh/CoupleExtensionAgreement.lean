/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.CoupleExtension
public import WaveTurbulence.Foundations.Incoh.RootCutoff
public import WaveTurbulence.Foundations.Incoh.RootCumulativeLocal
public import WaveTurbulence.Foundations.Incoh.TwoTimeBoxIntegral

/-!
# The cutoff extension agrees with the literal couple kernel

TARGET (incohproof17)–(incohproof20). The fixed smooth cutoff equals one
on all local root intervals. Fubini and the local-clock identity therefore
show that the estimated extension agrees with the actual source integral
on its full physical root box.
-/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

/-- The cutoff double integral is the unmodified cumulative integral on the unit root box. -/
theorem cutoffDoubleIntegral_rootCutoff_eq (F : (Fin 2 → ℝ) → ℂ) (t : Fin 2 → ℝ)
    (ht : t ∈ Icc (0 : Fin 2 → ℝ) 1) :
    Fourier.cutoffDoubleIntegral rootCutoff F t = ∫ u in (0 : ℝ)..t 0, ∫ v in (0 : ℝ)..t 1, F ![u, v] := by
  have ht₀ : t 0 ∈ Icc (0 : ℝ) 1 := ⟨ht.1 0, ht.2 0⟩
  have ht₁ : t 1 ∈ Icc (0 : ℝ) 1 := ⟨ht.1 1, ht.2 1⟩
  rw [Fourier.cutoffDoubleIntegral, rootCutoff_eq_one_on_unitInterval ht₀,
    rootCutoff_eq_one_on_unitInterval ht₁]
  simp only [Complex.ofReal_one, one_mul]
  apply intervalIntegral.integral_congr
  intro u hu
  have hu' : u ∈ Icc (0 : ℝ) (t 0) := by simpa only [uIcc_of_le ht₀.1] using hu
  apply intervalIntegral.integral_congr
  intro v hv
  have hv' : v ∈ Icc (0 : ℝ) (t 1) := by simpa only [uIcc_of_le ht₁.1] using hv
  dsimp only
  simp only [rootCutoff_eq_one_on_unitInterval ⟨hu'.1, hu'.2.trans ht₀.2⟩,
    rootCutoff_eq_one_on_unitInterval ⟨hv'.1, hv'.2.trans ht₁.2⟩, Complex.ofReal_one, one_mul]

/-- TARGET (incohproof19): the estimated cutoff is an actual extension of the literal source kernel. -/
theorem RootCoordinates.coupleExtension_agrees {d n : ℕ} (R : RootCoordinates n)
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I)
    (hbox : I ⊆ univ.pi (fun i => linkBox (Q i))) {t : Fin 2 → ℝ} (ht : t ∈ R.rootBox Q) :
    R.coupleExtension rootCutoff L γ δ Q I t = R.cumulativeKernel L γ δ Q I t := by
  let τ := t - R.baseRootTimes Q
  have hτ : τ ∈ Icc (0 : Fin 2 → ℝ) 1 := (R.local_mem_rootBox_iff Q τ).mp (by
    simpa only [τ, sub_add_cancel] using ht)
  have hF := R.integrable_localLinkDensity hL γ δ Q hI hbox
  have hrect := integral_twoTimeBox_eq_doubleInterval hF 0 (τ 0) 0 (τ 1) (hτ.1 0) (hτ.1 1)
  have hvec : ![τ 0, τ 1] = τ := by ext i; fin_cases i <;> rfl
  have hzero : ![(0 : ℝ), 0] = (0 : Fin 2 → ℝ) := by ext i; fin_cases i <;> rfl
  rw [hvec, hzero] at hrect
  change Fourier.cutoffDoubleIntegral rootCutoff (R.localLinkDensity L γ δ Q I) τ = _
  rw [cutoffDoubleIntegral_rootCutoff_eq _ τ hτ, ← hrect]
  exact (R.cumulativeKernel_eq_localBoxIntegral hL γ δ Q hI hbox t).symm

/-- TARGET (incohproof20), as a restriction-norm bound for the literal cumulative source kernel. -/
theorem exists_cumulativeKernel_timeRestriction_bound (d : ℕ) (hd : 3 ≤ d)
    (η : ℝ) (hη : 0 < η) (hη₁ : η ≤ 1 / 3) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        1 ≤ incoherenceCount Q →
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I → I ⊆ univ.pi (fun i => linkBox (Q i)) →
        ∀ R : RootCoordinates n,
        Fourier.timeRestrictionNorm η (R.rootBox Q) (fun t => R.cumulativeKernel L γ δ Q I t) ≤
          ENNReal.ofReal ((C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_coupleExtension_timeFourier_bound d hd η hη hη₁
    contDiff_rootCutoff hasCompactSupport_rootCutoff
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ hηg δ hδ hδ₁ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb γ hγ hηg δ hδ hδ₁ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n Q hg hspan I hI hbox R
  have hLp := zero_lt_one.trans_le (hL₀.trans hL)
  exact (Fourier.timeRestrictionNorm_le_extension (R.coupleExtension rootCutoff L γ δ Q I)
    (fun t => R.coupleExtension_agrees hLp γ δ Q hI hbox t.property)).trans
      (hb L hL n Q hg hspan I hI hbox R)

end WaveTurbulence.Incoh
