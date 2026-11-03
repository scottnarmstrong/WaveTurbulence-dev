/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.FiniteInterpolation
public import WaveTurbulence.Foundations.Fourier.FiniteStepFunctions
public import WaveTurbulence.Foundations.Fourier.FourierPairing
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Tactic

/-!
# Fourier interpolation on finite step functions

Finite step functions realize the weighted finite bilinear interpolation
theorem inside the Fourier pairing. The endpoint estimates are proved
from the integral transform and Plancherel, rather than supplied as
hypotheses of the source-facing estimate.
-/

public section

open MeasureTheory
open scoped FourierTransform ENNReal

namespace WaveTurbulence.Fourier

/-- A finite coefficient vector as an `L²` step function. -/
@[expose] noncomputable def finiteStepToL2 {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {n : ℕ} (A : Fin n → Set α)
    (hA : ∀ i, MeasurableSet (A i)) (hμ : ∀ i, μ (A i) ≠ ∞) :
    (Fin n → ℂ) →L[ℂ] Lp ℂ 2 μ :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (indicatorConstLp 2 (hA i) (hμ i) (1 : ℂ))

/-- The `L²` realization agrees almost everywhere with the literal step function. -/
theorem finiteStepToL2_coeFn {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {n : ℕ} (A : Fin n → Set α)
    (hA : ∀ i, MeasurableSet (A i)) (hμ : ∀ i, μ (A i) ≠ ∞) (a : Fin n → ℂ) :
    (finiteStepToL2 A hA hμ a : α → ℂ) =ᵐ[μ] finiteStepFunction A a := by
  classical
  have hi (i : Fin n) :
      ((a i • indicatorConstLp 2 (hA i) (hμ i) (1 : ℂ) : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ]
        (A i).indicator (fun _ => a i) := by
    filter_upwards [Lp.coeFn_smul (a i) (indicatorConstLp 2 (hA i) (hμ i) (1 : ℂ)),
      indicatorConstLp_coeFn (p := 2) (hs := hA i) (hμs := hμ i) (c := (1 : ℂ))] with x hx hy
    rw [hx]
    change a i • (indicatorConstLp 2 (hA i) (hμ i) (1 : ℂ) x) = _
    rw [hy]
    by_cases hxi : x ∈ A i <;> simp [hxi]
  simp only [finiteStepToL2, sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]
  refine (Lp.coeFn_fun_finsetSum Finset.univ _).trans ?_
  filter_upwards [ae_all_iff.mpr hi] with x hx
  exact Finset.sum_congr rfl fun i _ => hx i

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The continuous bilinear Fourier pairing on `L² × L²`. -/
@[expose] noncomputable def fourierL2Pairing :
    Lp (α := V) ℂ 2 (volume : Measure V) →L[ℂ]
      Lp (α := V) ℂ 2 (volume : Measure V) →L[ℂ] ℂ :=
  ((ContinuousLinearMap.mul ℂ ℂ).lpPairing (volume : Measure V) 2 2).comp
    (Lp.fourierTransformₗᵢ V ℂ).toContinuousLinearEquiv.toContinuousLinearMap

/-- The Fourier pairing restricted to two finite coefficient spaces. -/
@[expose] noncomputable def finiteStepFourierPairing {n m : ℕ}
    (A : Fin n → Set V) (hA : ∀ i, MeasurableSet (A i))
    (hμA : ∀ i, volume (A i) ≠ ∞)
    (B : Fin m → Set V) (hB : ∀ j, MeasurableSet (B j))
    (hμB : ∀ j, volume (B j) ≠ ∞) :
    (Fin n → ℂ) →L[ℂ] (Fin m → ℂ) →L[ℂ] ℂ :=
  ((ContinuousLinearMap.compL ℂ (Fin m → ℂ)
    (Lp (α := V) ℂ 2 (volume : Measure V)) ℂ).flip (finiteStepToL2 B hB hμB)).comp
      ((fourierL2Pairing (V := V)).comp (finiteStepToL2 A hA hμA))

/-- The restricted continuous bilinear map is the literal Fourier integral pairing. -/
theorem finiteStepFourierPairing_eq_integral {n m : ℕ}
    (A : Fin n → Set V) (hA : ∀ i, MeasurableSet (A i))
    (hμA : ∀ i, volume (A i) ≠ ∞)
    (B : Fin m → Set V) (hB : ∀ j, MeasurableSet (B j))
    (hμB : ∀ j, volume (B j) ≠ ∞) (a : Fin n → ℂ) (b : Fin m → ℂ) :
    finiteStepFourierPairing A hA hμA B hB hμB a b =
      ∫ ξ, 𝓕 (finiteStepFunction A a) ξ * finiteStepFunction B b ξ := by
  let ha := finiteStepFunction_memLp A hA hμA a 2
  let hb := finiteStepFunction_memLp B hB hμB b 2
  have hSa : finiteStepToL2 A hA hμA a = ha.toLp (finiteStepFunction A a) :=
    Lp.ext ((finiteStepToL2_coeFn A hA hμA a).trans ha.coeFn_toLp.symm)
  have hSb : finiteStepToL2 B hB hμB b = hb.toLp (finiteStepFunction B b) :=
    Lp.ext ((finiteStepToL2_coeFn B hB hμB b).trans hb.coeFn_toLp.symm)
  change (ContinuousLinearMap.mul ℂ ℂ).lpPairing volume 2 2
    (𝓕 (finiteStepToL2 A hA hμA a)) (finiteStepToL2 B hB hμB b) = _
  rw [hSa, hSb, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [integral_fourier_ae_eq_L2
    (finiteStepFunction_integrable A hA hμA a) ha, hb.coeFn_toLp] with ξ hξ hξ'
  rw [← hξ, hξ']
  rfl

/-- TARGET L2370, bilinear form for finite step functions. The endpoint
bounds are obtained from Fourier analysis inside the proof. -/
theorem fourier_pairing_finite_steps {n m : ℕ}
    (A : Fin n → Set V) (hA : ∀ i, MeasurableSet (A i))
    (hμA : ∀ i, volume (A i) ≠ ∞) (hdA : Pairwise (fun i j => Disjoint (A i) (A j)))
    (B : Fin m → Set V) (hB : ∀ j, MeasurableSet (B j))
    (hμB : ∀ j, volume (B j) ≠ ∞) (hdB : Pairwise (fun i j => Disjoint (B i) (B j)))
    {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (a : Fin n → ℂ) (b : Fin m → ℂ) :
    ‖∫ ξ, 𝓕 (finiteStepFunction A a) ξ * finiteStepFunction B b ξ‖ ≤
      lpNorm (finiteStepFunction A a) (ENNReal.ofReal p) volume *
        lpNorm (finiteStepFunction B b) (ENNReal.ofReal p) volume := by
  have hp : 0 < p := zero_lt_one.trans_le hp1
  have hnorm1 {k : ℕ} (C : Fin k → Set V) (hC : ∀ i, MeasurableSet (C i))
      (hμC : ∀ i, volume (C i) ≠ ∞) (hdC : Pairwise (fun i j => Disjoint (C i) (C j))) (c : Fin k → ℂ) :
      (∫ x, ‖finiteStepFunction C c x‖) = ∑ i, volume.real (C i) * ‖c i‖ := by
    simpa only [Real.rpow_one] using finiteStepFunction_integral_norm_rpow C hC hμC hdC c
      (by norm_num : (0 : ℝ) < 1)
  have hnorm2 {k : ℕ} (C : Fin k → Set V) (hC : ∀ i, MeasurableSet (C i))
      (hμC : ∀ i, volume (C i) ≠ ∞) (hdC : Pairwise (fun i j => Disjoint (C i) (C j))) (c : Fin k → ℂ) :
      lpNorm (finiteStepFunction C c) 2 volume = Real.sqrt (∑ i, volume.real (C i) * ‖c i‖ ^ 2) := by
    have h := finiteStepFunction_lpNorm C hC hμC hdC c (by norm_num : (0 : ℝ) < 2)
    simpa [Real.sqrt_eq_rpow, Real.rpow_two] using h
  let T := finiteStepFourierPairing A hA hμA B hB hμB
  have h1 (u : Fin n → ℂ) (v : Fin m → ℂ) :
      ‖T u v‖ ≤ (∑ i, volume.real (A i) * ‖u i‖) * (∑ j, volume.real (B j) * ‖v j‖) := by
    rw [show T u v = _ from finiteStepFourierPairing_eq_integral A hA hμA B hB hμB u v]
    simpa only [hnorm1 A hA hμA hdA u, hnorm1 B hB hμB hdB v] using
      fourier_pairing_L1 (f := finiteStepFunction A u) (finiteStepFunction_integrable B hB hμB v)
  have h2 (u : Fin n → ℂ) (v : Fin m → ℂ) :
      ‖T u v‖ ≤ Real.sqrt (∑ i, volume.real (A i) * ‖u i‖ ^ 2) *
        Real.sqrt (∑ j, volume.real (B j) * ‖v j‖ ^ 2) := by
    rw [show T u v = _ from finiteStepFourierPairing_eq_integral A hA hμA B hB hμB u v]
    simpa only [hnorm2 A hA hμA hdA u, hnorm2 B hB hμB hdB v] using
      fourier_pairing_L2_real (finiteStepFunction_integrable A hA hμA u)
        (finiteStepFunction_memLp A hA hμA u 2) (finiteStepFunction_memLp B hB hμB v 2)
  rw [finiteStepFunction_lpNorm A hA hμA hdA a hp,
    finiteStepFunction_lpNorm B hB hμB hdB b hp,
    ← finiteStepFourierPairing_eq_integral A hA hμA B hB hμB a b]
  exact finite_bilinear_interpolation_bound T (fun i => volume.real (A i))
    (fun j => volume.real (B j)) (fun _ => ENNReal.toReal_nonneg)
    (fun _ => ENNReal.toReal_nonneg) h1 h2 hp1 hp2 a b

end WaveTurbulence.Fourier
