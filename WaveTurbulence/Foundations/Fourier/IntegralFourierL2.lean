/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Tactic

/-!
# Compatibility of the integral and L² Fourier transforms

For an `L¹ ∩ L²` function, the ordinary Fourier integral agrees almost
everywhere with Mathlib's Plancherel extension. The proof compares their
tempered distributions against compact smooth test functions.
-/

public section

open MeasureTheory
open scoped FourierTransform SchwartzMap ENNReal ContDiff

namespace WaveTurbulence.Fourier

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The Fourier integral and the Plancherel transform agree on `L¹ ∩ L²`. -/
theorem integral_fourier_ae_eq_L2 {f : V → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) :
    (𝓕 f) =ᵐ[volume] (𝓕 (hf2.toLp f) : Lp (α := V) ℂ 2 (volume : Measure V)) := by
  let u := hf2.toLp f
  let U := (𝓕 u : Lp (α := V) ℂ 2 (volume : Measure V))
  have hcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf
  apply ae_eq_of_integral_contDiff_smul_eq hcont.locallyIntegrable
    ((Lp.memLp (μ := (volume : Measure V)) U).locallyIntegrable (by norm_num))
  intro g hgs hgc
  have hgc' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  have hgs' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let ψ := hgc'.toSchwartzMap hgs'
  have hψ (x : V) : ψ x = (g x : ℂ) := rfl
  have hd := congrArg (fun T : 𝓢'(V, ℂ) => T ψ) (Lp.fourier_toTemperedDistribution_eq u)
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at hd
  have hflip : (innerₗ V).flip = innerₗ V := by
    ext x y
    change inner ℝ y x = inner ℝ x y
    exact real_inner_comm x y
  have hp := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (L := innerₗ V) (μ := volume) (ν := volume) (ContinuousLinearMap.mul ℂ ℂ)
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf ψ.integrable
  rw [hflip] at hp
  change (∫ x, 𝓕 f x * ψ x) = ∫ x, f x * 𝓕 (ψ : V → ℂ) x at hp
  have hsource : (∫ x, (𝓕 ψ) x • u x) = ∫ x, (𝓕 ψ) x • f x := by
    apply integral_congr_ae
    filter_upwards [hf2.coeFn_toLp] with x hx
    rw [hx]
  calc
    (∫ x, g x • 𝓕 f x) = ∫ x, 𝓕 f x * ψ x := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by dsimp only; rw [hψ, Complex.real_smul]; ring
    _ = ∫ x, f x * 𝓕 (ψ : V → ℂ) x := hp
    _ = ∫ x, (𝓕 ψ) x • f x := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by simp only [SchwartzMap.fourier_coe, smul_eq_mul, mul_comm]
    _ = ∫ x, (𝓕 ψ) x • u x := hsource.symm
    _ = ∫ x, ψ x • U x := hd
    _ = ∫ x, g x • U x := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by dsimp only; rw [hψ, Complex.real_smul, smul_eq_mul]

/-- Plancherel membership for the ordinary Fourier integral. -/
theorem integral_fourier_memLp_two {f : V → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) :
    MemLp (𝓕 f) 2 :=
  (Lp.memLp (𝓕 (hf2.toLp f) : Lp (α := V) ℂ 2 (volume : Measure V))).ae_eq
    (integral_fourier_ae_eq_L2 hf hf2).symm

/-- Plancherel equality for the ordinary Fourier integral on `L¹ ∩ L²`. -/
theorem integral_fourier_eLpNorm_two {f : V → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) :
    eLpNorm (𝓕 f) 2 = eLpNorm f 2 := by
  calc
    eLpNorm (𝓕 f) 2 = ‖(𝓕 (hf2.toLp f) : Lp (α := V) ℂ 2 (volume : Measure V))‖ₑ := by
      rw [eLpNorm_congr_ae (integral_fourier_ae_eq_L2 hf hf2), Lp.enorm_def]
    _ = ‖hf2.toLp f‖ₑ := by
      simp only [← ofReal_norm, Lp.norm_fourier_eq]
    _ = eLpNorm f 2 := Lp.enorm_toLp hf2

end WaveTurbulence.Fourier
