/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtTa.AtomSmall
public import WaveTurbulence.Foundations.Regref.FourierAE

/-! # PROT-TA, Lemma 12.1: Fourier reconstruction of the consumed-modulation operator

For `h` on `ℝ³` with `h, ĥ ∈ L¹` (`ĥ = timeFourier h`): `h = ∫ ĥ(l) e^{2πi l·x} dl` a.e.; slicing through `u`
(`ae_slice`); and the atomwise identity (12.3): `∫_s^t e^{πiA(u-s)} e^{2πi l·(t,u,s)} du =
e^{2πi (l₀ t + (l₁+l₂) s)} h_{A/2+l₁}(t-s)`. Consequently `op_agree`: for a.e. `(t,s)` with `s < t`,
`T_A h (t,s) = ∫ ĥ(l) · atom` (before the cutoff `Φ`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.ProtTa

/-- The frequency `(l₀, l₁ + l₂)` of the output `(t,s)` for the input frequency `l = (l₀, l₁, l₂)`. -/
def nu (l : Fin 3 → ℝ) : Fin 2 → ℝ := ![l 0, l 1 + l 2]

/-- Inversion formula, written with the positive character. -/
def recon (h : (Fin 3 → ℝ) → ℂ) (x : Fin 3 → ℝ) : ℂ :=
  ∫ l, Real.fourierChar (timePairing 3 l x) • timeFourier h l

theorem recon_ae {h : (Fin 3 → ℝ) → ℂ} (hint : Integrable h) (hhat : Integrable (timeFourier h)) :
    recon h =ᵐ[volume] h := by
  have := Regref.timeFourier_inversion_ae hint hhat
  refine Filter.EventuallyEq.trans (ae_of_all _ fun x => ?_) this
  simp only [recon, timeFourier, VectorFourier.fourierIntegral, map_neg, LinearMap.neg_apply, neg_neg]

/-- Slice a null set of `ℝ³` through the middle coordinate. -/
theorem ae_slice {P : (Fin 3 → ℝ) → Prop} (h : ∀ᵐ x : Fin 3 → ℝ, P x) :
    ∀ᵐ y : Fin 2 → ℝ, ∀ᵐ u : ℝ, P ![y 0, u, y 1] := by
  have hmp : MeasurePreserving (fun p : ℝ × (Fin 2 → ℝ) => (![p.2 0, p.1, p.2 1] : Fin 3 → ℝ))
      (volume.prod volume) volume := by
    have h1 := (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 1).symm
    convert h1 using 1
    funext p
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply]
    ext j
    fin_cases j <;> simp [Fin.insertNth, Fin.succAboveCases]
  have h2 := hmp.quasiMeasurePreserving.ae h
  have h3 := (Measure.measurePreserving_swap (μ := (volume : Measure (Fin 2 → ℝ)))
    (ν := (volume : Measure ℝ))).quasiMeasurePreserving.ae h2
  exact Measure.ae_ae_of_ae_prod h3

theorem pairing_apply (r : ℕ) (t ξ : Fin r → ℝ) : timePairing r t ξ = ∑ i, t i * ξ i := rfl

/-- The atomwise identity (12.3). -/
theorem inner_eq (A : ℝ) (l : Fin 3 → ℝ) (y : Fin 2 → ℝ) :
    ∫ u in y 1..y 0, Complex.exp (((Real.pi * A * (u - y 1) : ℝ) : ℂ) * Complex.I) *
        (Real.fourierChar (timePairing 3 l ![y 0, u, y 1]) : ℂ) =
      (Real.fourierChar (timePairing 2 y (nu l)) : ℂ) * hz (A / 2 + l 1) (y 0 - y 1) := by
  have hsub := intervalIntegral.integral_comp_add_left (a := 0) (b := y 0 - y 1)
    (fun u : ℝ => Complex.exp (((Real.pi * A * (u - y 1) : ℝ) : ℂ) * Complex.I) *
        (Real.fourierChar (timePairing 3 l ![y 0, u, y 1]) : ℂ)) (y 1)
  simp only [add_zero, add_sub_cancel] at hsub
  rw [← hsub]
  unfold hz
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun w _ => ?_)
  rw [Real.fourierChar_apply, Real.fourierChar_apply, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [pairing_apply, Fin.sum_univ_three, Fin.sum_univ_two, nu]
  simp
  push_cast
  ring

theorem op_agree {h : (Fin 3 → ℝ) → ℂ} (hint : Integrable h) (hhat : Integrable (timeFourier h)) (A : ℝ) :
    ∀ᵐ y : Fin 2 → ℝ, y 1 < y 0 →
      (∫ u in y 1..y 0, Complex.exp (((Real.pi * A * (u - y 1) : ℝ) : ℂ) * Complex.I) *
          h ![y 0, u, y 1]) =
        ∫ l, timeFourier h l * ((Real.fourierChar (timePairing 2 y (nu l)) : ℂ) *
          hz (A / 2 + l 1) (y 0 - y 1)) := by
  have hae := ae_slice (P := fun x => recon h x = h x) (recon_ae hint hhat)
  filter_upwards [hae] with y hy hlt
  have hcongr : (∫ u in y 1..y 0, Complex.exp (((Real.pi * A * (u - y 1) : ℝ) : ℂ) * Complex.I) *
          h ![y 0, u, y 1]) = ∫ u in y 1..y 0,
          Complex.exp (((Real.pi * A * (u - y 1) : ℝ) : ℂ) * Complex.I) * recon h ![y 0, u, y 1] := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hy] with u hu _
    rw [hu]
  rw [hcongr]
  have hc : Continuous (timeFourier h) := timeFourier_continuous hint
  have hint2 : Integrable (Function.uncurry fun (u : ℝ) (l : Fin 3 → ℝ) =>
      Complex.exp (((Real.pi * A * (u - y 1) : ℝ) : ℂ) * Complex.I) *
        ((Real.fourierChar (timePairing 3 l ![y 0, u, y 1]) : ℂ) * timeFourier h l))
      ((volume.restrict (Set.Ioc (y 1) (y 0))).prod volume) := by
    have h1 : Integrable (fun p : ℝ × (Fin 3 → ℝ) => (1 : ℝ) * ‖timeFourier h p.2‖)
        ((volume.restrict (Set.Ioc (y 1) (y 0))).prod volume) :=
      Integrable.mul_prod (f := fun _ : ℝ => (1 : ℝ)) (g := fun l => ‖timeFourier h l‖)
        (integrable_const _) hhat.norm
    refine h1.mono' ?_ (ae_of_all _ fun p => ?_)
    · have : Continuous (Function.uncurry fun (u : ℝ) (l : Fin 3 → ℝ) =>
          Complex.exp (((Real.pi * A * (u - y 1) : ℝ) : ℂ) * Complex.I) *
            ((Real.fourierChar (timePairing 3 l ![y 0, u, y 1]) : ℂ) * timeFourier h l)) := by
        simp only [Real.fourierChar_apply, pairing_apply, Fin.sum_univ_three]
        have := hc
        fun_prop
      exact this.aestronglyMeasurable
    · simp only [Function.uncurry, norm_mul, Complex.norm_exp_ofReal_mul_I, Circle.norm_coe, one_mul]
      exact le_rfl
  simp only [recon, Circle.smul_def, smul_eq_mul]
  rw [intervalIntegral.integral_of_le hlt.le]
  simp_rw [← integral_const_mul]
  rw [integral_integral_swap hint2]
  refine integral_congr_ae (ae_of_all _ fun l => ?_)
  dsimp only
  rw [← intervalIntegral.integral_of_le hlt.le]
  have := inner_eq A l y
  calc (∫ u in y 1..y 0, Complex.exp (((Real.pi * A * (u - y 1) : ℝ) : ℂ) * Complex.I) *
        ((Real.fourierChar (timePairing 3 l ![y 0, u, y 1]) : ℂ) * timeFourier h l))
      = (∫ u in y 1..y 0, Complex.exp (((Real.pi * A * (u - y 1) : ℝ) : ℂ) * Complex.I) *
        (Real.fourierChar (timePairing 3 l ![y 0, u, y 1]) : ℂ)) * timeFourier h l := by
        rw [← intervalIntegral.integral_mul_const]
        refine intervalIntegral.integral_congr (fun u _ => ?_)
        ring
    _ = _ := by rw [this]; ring

end WaveTurbulence.Flower.ProtTa
