/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.EnvelopeConvolution

/-!
# Certified spectral packets

The certificate is attached to an actual integrable density. The operations
below construct new certificates by the proved Fourier estimates, so tree
induction does not need to assume a spectral representation or a decay bound.
-/

public section

open MeasureTheory
open scoped ENNReal Convolution ContDiff

namespace WaveTurbulence.Analysis

/-- An actual integrable spectral density with a finite Cauchy envelope. -/
structure SpectralPacket where
  Index : Type
  fintypeIndex : Fintype Index
  centre : Index → ℝ
  weight : Index → ℝ≥0∞
  density : ℝ → ℂ
  integrable_density : Integrable density
  bound : ∀ t, ‖density t‖ₑ ≤ frequencyEnvelope centre weight t

attribute [instance] SpectralPacket.fintypeIndex

namespace SpectralPacket

/-- The function represented by a certified packet. -/
@[expose] noncomputable def synthesis (P : SpectralPacket) : ℝ → ℂ :=
  spectralSynthesis P.density

/-- A time translation changes only the unimodular part of the density. -/
@[expose] noncomputable def shift (P : SpectralPacket) (a : ℝ) : SpectralPacket where
  Index := P.Index
  fintypeIndex := P.fintypeIndex
  centre := P.centre
  weight := P.weight
  density := fun s => timePhase (-a) s * P.density s
  integrable_density := integrable_timeShiftDensity P.integrable_density a
  bound t := by
    rw [enorm_mul, ← ofReal_norm, norm_timePhase, ENNReal.ofReal_one, one_mul]
    exact P.bound t

theorem synthesis_shift (P : SpectralPacket) (a t : ℝ) :
    (P.shift a).synthesis t = P.synthesis (t - a) :=
  (spectralSynthesis_sub P.density t a).symm

/-- Frequency translation, corresponding to modulation in time. -/
@[expose] noncomputable def modulate (P : SpectralPacket) (a : ℝ) : SpectralPacket where
  Index := P.Index
  fintypeIndex := P.fintypeIndex
  centre := fun i => P.centre i + a
  weight := P.weight
  density := fun s => P.density (s - a)
  integrable_density := P.integrable_density.comp_sub_right a
  bound t := by
    convert P.bound (t - a) using 1
    unfold frequencyEnvelope
    apply Finset.sum_congr rfl
    intro i hi
    rw [show t - a - P.centre i = t - (P.centre i + a) by ring]

private theorem timePhase_swap (q t : ℝ) : timePhase q t = timePhase t q := by
  unfold timePhase
  congr 1
  push_cast
  ring

theorem synthesis_modulate (P : SpectralPacket) (a t : ℝ) :
    (P.modulate a).synthesis t = timePhase a t * P.synthesis t := by
  change spectralSynthesis (fun s => P.density (s - a)) t = _
  rw [spectralSynthesis_eq_integral]
  rw [← integral_add_right_eq_self (fun s : ℝ => timePhase t s * P.density (s - a)) a]
  simp only [add_sub_cancel_right]
  have heq (s : ℝ) : timePhase t (s + a) * P.density s =
      timePhase a t * (timePhase t s * P.density s) := by
    rw [timePhase_swap t (s + a), ← timePhase_add, timePhase_swap s t]
    ring
  simp_rw [heq]
  rw [integral_const_mul, ← spectralSynthesis_eq_integral]
  rfl

/-- Multiplication of functions is implemented by the actual convolution
of the densities, with the explicit Cauchy convolution loss. -/
@[expose] noncomputable def multiply (P Q : SpectralPacket) : SpectralPacket where
  Index := P.Index × Q.Index
  fintypeIndex := inferInstance
  centre := fun p => P.centre p.1 + Q.centre p.2
  weight := fun p => ENNReal.ofReal (4 * Real.pi) * (P.weight p.1 * Q.weight p.2)
  density := P.density ⋆[ContinuousLinearMap.mul ℂ ℂ] Q.density
  integrable_density := P.integrable_density.integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) Q.integrable_density
  bound t := by
    have hh := enorm_convolution_le_frequencyEnvelope P.centre P.weight Q.centre Q.weight P.bound Q.bound t
    convert hh using 1
    unfold frequencyEnvelope
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

theorem synthesis_multiply (P Q : SpectralPacket) (t : ℝ) :
    (P.multiply Q).synthesis t = P.synthesis t * Q.synthesis t :=
  spectralSynthesis_convolution P.integrable_density Q.integrable_density t

/-- Cutoff time integration duplicates every input centre into the lower
endpoint centre zero and the upper endpoint centre itself. -/
@[expose] noncomputable def integrate (P : SpectralPacket) {χ : ℝ → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hs : HasCompactSupport χ) {a : ℝ} (ha : a ∈ Set.Icc 0 1) : SpectralPacket where
  Index := Bool × P.Index
  fintypeIndex := inferInstance
  centre := fun p => if p.1 then P.centre p.2 else 0
  weight := fun p => ENNReal.ofReal (cutoffKernelConstant χ) * ENNReal.ofReal (12 * Real.pi) *
    (P.weight p.2 * ENNReal.ofReal (oscillatoryWeight (P.centre p.2)))
  density := cutoffSpectralOperator χ a P.density
  integrable_density := integrable_cutoffSpectralOperator hχ hs ha P.integrable_density
  bound t := by
    have hh := enorm_cutoffSpectralOperator_le_frequencyEnvelope hχ hs ha P.centre P.weight P.bound t
    convert hh using 1
    unfold frequencyEnvelope
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte, sub_zero]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring

theorem synthesis_integrate (P : SpectralPacket) {χ : ℝ → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hs : HasCompactSupport χ) {a : ℝ} (ha : a ∈ Set.Icc 0 1) (t : ℝ) :
    (P.integrate hχ hs ha).synthesis t = χ t * ∫ s in a..t, P.synthesis s :=
  spectralSynthesis_cutoffSpectralOperator_eq_integral hχ hs ha P.integrable_density t

/-- The mass estimate applies to the actual represented function. -/
theorem enorm_synthesis_le (P : SpectralPacket) (t : ℝ) :
    ‖P.synthesis t‖ₑ ≤ (∑ i, P.weight i) * ENNReal.ofReal Real.pi :=
  enorm_spectralSynthesis_le_frequencyEnvelope P.centre P.weight P.bound t

end SpectralPacket
end WaveTurbulence.Analysis
