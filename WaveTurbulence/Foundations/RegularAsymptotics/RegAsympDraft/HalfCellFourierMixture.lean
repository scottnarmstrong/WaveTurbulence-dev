/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.HalfCellSingularRepresentation

/-! # Actual joint Fubini for parameter-dependent half-cell Fourier coefficients -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT

variable {U : Type*} [MeasurableSpace U] (μ : Measure U) {d n : ℕ}

/-- Actual half-cell Fourier coefficients are jointly measurable even when
both modulation arrays depend on an arbitrary measurable parameter. -/
theorem stronglyMeasurable_halfCellFourierMixture
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ : U → Fin n → Mom d)
    (hβ : Measurable β) (hγ : Measurable γ) (a : U → ℂ) (ha : StronglyMeasurable a) :
    StronglyMeasurable (fun p : U × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      a p.1 * fourierW (halfCellAmplitude z (β p.1) (γ p.1)) p.2.1 p.2.2) := by
  have hm : Measurable (fun p : U × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      ((β p.1,γ p.1),p.2)) := ((hβ.prodMk hγ).comp measurable_fst).prodMk measurable_snd
  have hbase : StronglyMeasurable (fun p :
      ((Fin n → Mom d) × (Fin n → Mom d)) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      fourierW (halfCellAmplitude z p.1.1 p.1.2) p.2.1 p.2.2) :=
    stronglyMeasurable_fourierW_parameter (d := d) (n := n)
      (P := (Fin n → Mom d) × (Fin n → Mom d)) (W := fun v => halfCellAmplitude z v.1 v.2)
      (continuous_halfCellAmplitude_joint z).stronglyMeasurable
  have hhat : StronglyMeasurable (fun p : U × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      fourierW (halfCellAmplitude z (β p.1) (γ p.1)) p.2.1 p.2.2) :=
    hbase.comp_measurable (g := fun p : U × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      ((β p.1,γ p.1),p.2)) hm
  have ha' : StronglyMeasurable (fun p : U × ((Fin n → Mom d) × (Fin n → Mom d)) => a p.1) :=
    ha.comp_measurable measurable_fst
  exact ha'.mul hhat

/-- Joint integrability and its exact linear mass budget. The premise is
an ordinary weighted coefficient L1 bound, independent of any singular operator. -/
theorem halfCellFourierMixture_integrable_mass [SFinite μ] (hn : 0 < n)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ : U → Fin n → Mom d)
    (hβ : Measurable β) (hγ : Measurable γ) (a : U → ℂ) (ha : StronglyMeasurable a)
    (hi : Integrable (fun u => ‖a u‖*(1+((∑ j, ‖β u j‖)+(∑ j, ‖γ u j‖)))) μ) :
    Integrable (fun p : U × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      a p.1 * fourierW (halfCellAmplitude z (β p.1) (γ p.1)) p.2.1 p.2.2) (μ.prod volume) ∧
    (∫ p : U × ((Fin n → Mom d) × (Fin n → Mom d)),
      ‖a p.1 * fourierW (halfCellAmplitude z (β p.1) (γ p.1)) p.2.1 p.2.2‖ ∂μ.prod volume) ≤
      ((1+2*Real.pi)*halfLinkFirstMomentConstant d^(2*n))*
        ∫ u, ‖a u‖*(1+((∑ j, ‖β u j‖)+(∑ j, ‖γ u j‖))) ∂μ := by
  have := isFiniteMeasureOnCompacts_pairs (n := n) (d := d)
  let f := fun p : U × ((Fin n → Mom d) × (Fin n → Mom d)) =>
    a p.1 * fourierW (halfCellAmplitude z (β p.1) (γ p.1)) p.2.1 p.2.2
  let K := (1+2*Real.pi)*halfLinkFirstMomentConstant d^(2*n)
  have hD := (halfLinkFirstMomentConstant_pos d).le
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hm : StronglyMeasurable f := stronglyMeasurable_halfCellFourierMixture z β γ hβ hγ a ha
  have hf (u : U) : Integrable (fun τ => f (u,τ)) :=
    ((halfCellAmplitude_fourier_setup hn z (β u) (γ u)).1).const_mul (a u)
  have hb (u : U) : (∫ τ, ‖f (u,τ)‖) ≤
      K*(‖a u‖*(1+((∑ j, ‖β u j‖)+(∑ j, ‖γ u j‖)))) := by
    simp only [f,norm_mul,integral_const_mul]
    have h := mul_le_mul_of_nonneg_left
      (integral_norm_fourierW_halfCellAmplitude_le hn z (β u) (γ u)) (norm_nonneg (a u))
    simpa only [K,mul_assoc,mul_left_comm,mul_comm] using h
  have hinner : Integrable (fun u => ∫ τ, ‖f (u,τ)‖) μ := by
    apply (hi.const_mul K).mono' hm.norm.integral_prod_right'.aestronglyMeasurable
    apply ae_of_all
    intro u
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact hb u
  have hfprod : Integrable f (μ.prod volume) :=
    (integrable_prod_iff hm.aestronglyMeasurable).mpr ⟨ae_of_all _ hf,hinner⟩
  refine ⟨hfprod,?_⟩
  rw [integral_prod _ hfprod.norm,← integral_const_mul]
  exact integral_mono hinner (hi.const_mul K) hb

end WaveTurbulence.RegAsymp
