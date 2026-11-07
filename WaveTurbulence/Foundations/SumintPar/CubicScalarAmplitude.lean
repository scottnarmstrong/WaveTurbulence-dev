/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.PoissonMajorant
public import WaveTurbulence.Foundations.LemLin.ScalarLattice
import Mathlib.Tactic

/-!
# Translated and modulated scalar cubic amplitudes

The source's two cubic phases share the same compact three-coordinate
cutoff. Their Fourier transforms are exactly the translated scalar
integrals controlled by the landed cubic estimate.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory
open scoped ContDiff

namespace WaveTurbulence.SumintPar

/-- The translated three-coordinate amplitude with all linear modulations. -/
@[expose] noncomputable def translatedCubicAmplitude (kind : LemLin.CubicPhase)
    (f : Fin 3 → LemLin.ScalarCutoff) (s t : ℝ) (a ν : Fin 3 → ℝ) (p : Fin 3 → ℝ) : ℂ :=
  LemLin.cubicProduct f (p-a) *
    (Real.fourierChar ((∑ i, ν i * p i) + LemLin.scalarQuadratic kind s t p) : ℂ)

/-- Translation and modulation preserve smoothness. -/
theorem translatedCubicAmplitude_contDiff (kind : LemLin.CubicPhase)
    (f : Fin 3 → LemLin.ScalarCutoff) (s t : ℝ) (a ν : Fin 3 → ℝ) :
    ContDiff ℝ ∞ (translatedCubicAmplitude kind f s t a ν) := by
  unfold translatedCubicAmplitude
  apply ContDiff.mul
  · exact (LemLin.cubicProduct_contDiff f).comp (contDiff_id.sub contDiff_const)
  · simp only [Real.fourierChar_apply]
    apply ContDiff.cexp
    apply ContDiff.mul _ contDiff_const
    apply Complex.ofRealCLM.contDiff.comp
    apply ContDiff.mul contDiff_const
    apply ContDiff.add
    · exact ContDiff.sum (fun i _ => contDiff_const.mul (contDiff_apply ℝ (fun _ : Fin 3 => ℝ) i))
    · exact LemLin.scalarQuadratic_contDiff kind s t

/-- The translated cutoff supplies actual compact support. -/
theorem translatedCubicAmplitude_hasCompactSupport (kind : LemLin.CubicPhase)
    (f : Fin 3 → LemLin.ScalarCutoff) (s t : ℝ) (a ν : Fin 3 → ℝ) :
    HasCompactSupport (translatedCubicAmplitude kind f s t a ν) := by
  have hc := (LemLin.cubicProduct_hasCompactSupport f).comp_homeomorph (Homeomorph.addRight (-a))
  rw [hasCompactSupport_iff_eventuallyEq] at hc ⊢
  filter_upwards [hc] with p hp
  change translatedCubicAmplitude kind f s t a ν p = 0
  unfold translatedCubicAmplitude
  have hz : LemLin.cubicProduct f (p-a) = 0 := by simpa only [sub_eq_add_neg, Pi.zero_apply, Function.comp_def, Homeomorph.coe_addRight] using hp
  rw [hz, zero_mul]

/-- The negative Fourier character subtracts the dual frequency from the source modulation. -/
theorem timeFourier_translatedCubicAmplitude (kind : LemLin.CubicPhase)
    (f : Fin 3 → LemLin.ScalarCutoff) (s t : ℝ) (a ν κ : Fin 3 → ℝ) :
    Fourier.timeFourier (translatedCubicAmplitude kind f s t a ν) κ =
      LemLin.translatedScalarCubicIntegral kind f s t a (ν-κ) := by
  unfold Fourier.timeFourier VectorFourier.fourierIntegral
    translatedCubicAmplitude LemLin.translatedScalarCubicIntegral
  apply integral_congr_ae
  apply ae_of_all
  intro p
  have he : -Fourier.timePairing 3 p κ +
      ((∑ i, ν i*p i)+LemLin.scalarQuadratic kind s t p) =
      (∑ i, (ν-κ) i*p i)+LemLin.scalarQuadratic kind s t p := by
    change -(∑ i, p i * κ i) + ((∑ i, ν i*p i) + LemLin.scalarQuadratic kind s t p) =
      (∑ i, (ν i-κ i)*p i) + LemLin.scalarQuadratic kind s t p
    simp only [sub_mul, Finset.sum_sub_distrib]
    have hh : (∑ i, p i * κ i) = ∑ i, κ i * p i :=
      Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    rw [hh]
    ring
  simp only [Circle.smul_def, smul_eq_mul]
  rw [mul_left_comm, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, he]

end WaveTurbulence.SumintPar
