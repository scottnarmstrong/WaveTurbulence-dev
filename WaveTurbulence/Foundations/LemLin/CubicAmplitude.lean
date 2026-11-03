/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LemLin.ScalarCutoff
public import WaveTurbulence.Foundations.Fourier.TimeEuclidean

/-!
# The two quadratic phases in TARGET `lemcubic0`

The scalar formulation uses three real coordinates with ordinary product
Lebesgue measure. Tensor products recover the source's vector formulation.
-/

public section

namespace WaveTurbulence.LemLin
open MeasureTheory Set
open scoped ContDiff

/-- The two choices of Λ in TARGET `lemcubic0`. -/
inductive CubicPhase
  | cross
  | collision
  deriving DecidableEq

/-- The scalar quadratic phase, with the source normalization of `s,t`. -/
@[expose] def scalarQuadratic (kind : CubicPhase) (s t : ℝ) (p : Fin 3 → ℝ) : ℝ :=
  t * p 0 * p 1 + match kind with
    | .cross => s * p 0 * p 2
    | .collision => s * p 2 * (p 0 + p 1 - p 2)

/-- A product of three fixed compact scalar amplitudes. -/
@[expose] noncomputable def cubicProduct (f : Fin 3 → ScalarCutoff) (p : Fin 3 → ℝ) : ℂ :=
  ∏ i, f i (p i)

/-- The compact quadratic modulation whose Fourier transform is estimated. -/
@[expose] noncomputable def scalarCubicAmplitude (kind : CubicPhase)
    (f : Fin 3 → ScalarCutoff) (s t : ℝ) (p : Fin 3 → ℝ) : ℂ :=
  cubicProduct f p * (Real.fourierChar (scalarQuadratic kind s t p) : ℂ)

/-- The actual scalar oscillatory integral, with a positive linear phase. -/
@[expose] noncomputable def scalarCubicIntegral (kind : CubicPhase)
    (f : Fin 3 → ScalarCutoff) (s t : ℝ) (ν : Fin 3 → ℝ) : ℂ :=
  ∫ p : Fin 3 → ℝ, scalarCubicAmplitude kind f s t p *
    (Real.fourierChar (∑ i, ν i * p i) : ℂ)

/-- The positive source convention is the negative Fourier frequency. -/
theorem scalarCubicIntegral_eq_timeFourier (kind : CubicPhase)
    (f : Fin 3 → ScalarCutoff) (s t : ℝ) (ν : Fin 3 → ℝ) :
    scalarCubicIntegral kind f s t ν =
      Fourier.timeFourier (scalarCubicAmplitude kind f s t) (-ν) := by
  unfold scalarCubicIntegral Fourier.timeFourier VectorFourier.fourierIntegral
  apply integral_congr_ae
  apply ae_of_all
  intro p
  have he : -(Fourier.timePairing 3 p (-ν)) = ∑ i, ν i * p i := by
    change -(∑ i, p i * -ν i) = ∑ i, ν i * p i
    simp only [mul_neg, Finset.sum_neg_distrib, neg_neg]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  simp only [Circle.smul_def, smul_eq_mul]
  change scalarCubicAmplitude kind f s t p * (Real.fourierChar (∑ i, ν i * p i) : ℂ) =
    (Real.fourierChar (-(Fourier.timePairing 3 p (-ν))) : ℂ) * scalarCubicAmplitude kind f s t p
  rw [he, mul_comm]

theorem cubicProduct_hasCompactSupport (f : Fin 3 → ScalarCutoff) :
    HasCompactSupport (cubicProduct f) := by
  have hK : IsCompact (Set.pi univ (fun _ : Fin 3 => Icc (-1 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hK.isClosed
  intro p hp i _
  have hn : f i (p i) ≠ 0 := by
    intro hz
    exact hp (Finset.prod_eq_zero (Finset.mem_univ i) hz)
  exact (f i).support_subset (subset_closure hn)

theorem scalarCubicAmplitude_hasCompactSupport (kind : CubicPhase)
    (f : Fin 3 → ScalarCutoff) (s t : ℝ) :
    HasCompactSupport (scalarCubicAmplitude kind f s t) :=
  (cubicProduct_hasCompactSupport f).mul_right

@[fun_prop] theorem cubicProduct_contDiff (f : Fin 3 → ScalarCutoff) :
    ContDiff ℝ ∞ (cubicProduct f) := by
  unfold cubicProduct
  apply contDiff_prod
  intro i _
  exact (f i).smooth.comp (contDiff_apply ℝ (fun _ : Fin 3 => ℝ) i)

@[fun_prop] theorem scalarQuadratic_contDiff (kind : CubicPhase) (s t : ℝ) :
    ContDiff ℝ ∞ (scalarQuadratic kind s t) := by
  cases kind <;> unfold scalarQuadratic <;> fun_prop

@[fun_prop] theorem scalarCubicAmplitude_contDiff (kind : CubicPhase)
    (f : Fin 3 → ScalarCutoff) (s t : ℝ) :
    ContDiff ℝ ∞ (scalarCubicAmplitude kind f s t) := by
  unfold scalarCubicAmplitude
  apply (cubicProduct_contDiff f).mul
  simp only [Real.fourierChar_apply]
  apply (Complex.contDiff_exp : ContDiff ℝ ∞ Complex.exp).comp
  apply ContDiff.mul _ contDiff_const
  exact Complex.ofRealCLM.contDiff.comp
    (contDiff_const.mul (scalarQuadratic_contDiff kind s t))

theorem scalarCubicAmplitude_integrable (kind : CubicPhase)
    (f : Fin 3 → ScalarCutoff) (s t : ℝ) :
    Integrable (scalarCubicAmplitude kind f s t) :=
  (scalarCubicAmplitude_contDiff kind f s t).continuous.integrable_of_hasCompactSupport
    (scalarCubicAmplitude_hasCompactSupport kind f s t)

end WaveTurbulence.LemLin
