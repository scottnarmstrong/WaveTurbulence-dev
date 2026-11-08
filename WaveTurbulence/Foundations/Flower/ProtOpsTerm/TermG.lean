/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtOpsTerm.ReconId

/-! # PROT-OPS-TERM: the cutoff operator `G = Φ(t,s) · T_A H`, its integrability, and `Ĝ = û`

* `Tf A h ts = ∫_s^t e^{πiA(u-s)} h(spectators, t, u, s) du`, `Gf A h ts = Φ(t,s) Tf A h ts`;
* `uniq_ft`: if `G, u ∈ L¹` and `G` is a.e. the inverse transform of `u`, then `Ĝ = u` a.e.;
* `ft_Gf`: `timeFourier (Gf A h) = uHat A h` a.e. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory WaveTurbulence.Fourier WaveTurbulence.Flower.ProtTa
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.ProtOpsTerm

variable {r : ℕ}

def Tf (A : ℝ) (h : (Fin (r + 3) → ℝ) → ℂ) (ts : Fin (r + 2) → ℝ) : ℂ :=
  ∫ u in tl ts 1..tl ts 0, Complex.exp (((Real.pi * A * (u - tl ts 1) : ℝ) : ℂ) * Complex.I) *
    h (Fin.append (hd ts) ![tl ts 0, u, tl ts 1])

def Gf (A : ℝ) (h : (Fin (r + 3) → ℝ) → ℂ) (ts : Fin (r + 2) → ℝ) : ℂ :=
  Phi (tl ts) * Tf A h ts

theorem norm_Phi_le (y : Fin 2 → ℝ) : ‖Phi y‖ ≤ 1 := by
  unfold Phi
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg bump.nonneg]
  exact bump.le_one

theorem Gf_ae (A : ℝ) {h : (Fin (r + 3) → ℝ) → ℂ} (hint : Integrable h)
    (hhat : Integrable (timeFourier h)) :
    Gf A h =ᵐ[volume] invN (uHat A h) := by
  filter_upwards [op_agree_r hint hhat A] with ts hts
  rw [recon_uHat A hint hhat ts]
  unfold Gf Tf
  rw [hts, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun l => ?_)
  simp only [atom, psi, Circle.smul_def, smul_eq_mul]
  ring

theorem uniq_ft {n : ℕ} {G u : (Fin n → ℝ) → ℂ} (hG : Integrable G) (hu : Integrable u)
    (h : invN u =ᵐ[volume] G) : timeFourier G =ᵐ[volume] u := by
  set v : (Fin n → ℝ) → ℂ := fun ξ => u (-ξ) with hv
  have hvi : Integrable v := hu.comp_neg
  have hft : timeFourier v = invN u := by
    funext x
    simp only [timeFourier, VectorFourier.fourierIntegral, invN, hv]
    rw [← integral_neg_eq_self (fun ξ => Real.fourierChar (-(timePairing n ξ x)) • u (-ξ))]
    refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
    simp
  have hvhat : Integrable (timeFourier v) := by
    rw [hft]; exact (integrable_congr h).2 hG
  have hinv := Regref.timeFourier_inversion_ae hvi hvhat
  have hcong : timeFourier (timeFourier v) = timeFourier G := by
    rw [hft]; exact timeFourier_congr_ae h
  rw [hcong] at hinv
  have h2 := (Measure.measurePreserving_neg (volume : Measure (Fin n → ℝ))).quasiMeasurePreserving.ae hinv
  filter_upwards [h2] with t ht
  simpa [hv] using ht

theorem measurable_tl {n m : ℕ} (j : Fin m) :
    Measurable (fun p : ℝ × (Fin (n + m) → ℝ) => tl p.2 j) :=
  (measurable_pi_apply _).comp measurable_snd

theorem Gf_integrable (A : ℝ) {h : (Fin (r + 3) → ℝ) → ℂ} (hint : Integrable h) :
    Integrable (Gf A h) := by
  have hI : Integrable (fun p : ℝ × (Fin (r + 2) → ℝ) => h (lam r p)) (volume.prod volume) :=
    ((lamMP r).integrable_comp hint.aestronglyMeasurable).2 hint
  let F : ℝ × (Fin (r + 2) → ℝ) → ℂ := fun p =>
    Complex.exp (((Real.pi * A * (p.1 - tl p.2 1) : ℝ) : ℂ) * Complex.I) * h (lam r p)
  have hFm : AEStronglyMeasurable F (volume.prod volume) := by
    have hc : Continuous (fun p : ℝ × (Fin (r + 2) → ℝ) =>
        Complex.exp (((Real.pi * A * (p.1 - tl p.2 1) : ℝ) : ℂ) * Complex.I)) := by
      have : Continuous (fun p : ℝ × (Fin (r + 2) → ℝ) => tl p.2 1) :=
        (continuous_apply _).comp continuous_snd
      fun_prop
    exact hc.aestronglyMeasurable.mul hI.aestronglyMeasurable
  have hFi : Integrable F (volume.prod volume) := by
    refine hI.norm.mono' hFm (ae_of_all _ fun p => ?_)
    simp only [F, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, le_refl]
  have hS1 : MeasurableSet {p : ℝ × (Fin (r + 2) → ℝ) | tl p.2 1 < p.1 ∧ p.1 ≤ tl p.2 0} :=
    (measurableSet_lt (measurable_tl 1) measurable_fst).inter
      (measurableSet_le measurable_fst (measurable_tl 0))
  have hS2 : MeasurableSet {p : ℝ × (Fin (r + 2) → ℝ) | tl p.2 0 < p.1 ∧ p.1 ≤ tl p.2 1} :=
    (measurableSet_lt (measurable_tl 0) measurable_fst).inter
      (measurableSet_le measurable_fst (measurable_tl 1))
  have h1 := (hFi.indicator hS1).integral_prod_right
  have h2 := (hFi.indicator hS2).integral_prod_right
  have hT : Integrable (Tf A h) := by
    convert h1.sub h2 using 1
    funext ts
    simp only [Tf, Pi.sub_apply]
    unfold intervalIntegral
    congr 1
    · rw [← integral_indicator measurableSet_Ioc]
      refine integral_congr_ae (ae_of_all _ fun u => ?_)
      simp [Set.indicator_apply, F, lam]
    · rw [← integral_indicator measurableSet_Ioc]
      refine integral_congr_ae (ae_of_all _ fun u => ?_)
      simp [Set.indicator_apply, F, lam]
  have hPm : AEStronglyMeasurable (fun ts : Fin (r + 2) → ℝ => Phi (tl ts)) volume := by
    have : Continuous (fun ts : Fin (r + 2) → ℝ => Phi (tl ts)) :=
      Phi_contDiff.continuous.comp (continuous_pi fun j => continuous_apply _)
    exact this.aestronglyMeasurable
  refine hT.norm.mono' (hPm.mul hT.aestronglyMeasurable) (ae_of_all _ fun ts => ?_)
  unfold Gf
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_Phi_le _)

end WaveTurbulence.Flower.ProtOpsTerm
