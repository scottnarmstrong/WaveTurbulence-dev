/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3Sobolev
public import Mathlib

/-!
# X3: large deviations for the supremum in time (T (sobolev), L2315)

`prob_sup_le`: let `f(ω, ·)` have derivative `g(ω, ·)` on `[a, a+1]`, both jointly measurable, and let
`𝔼_F |f(t)|² ≤ c` and `𝔼_F |g(t)|² ≤ c'` for `t ∈ (a, a+1)`. Then
`P(F ∩ {sup_t |f(t)| > B}) ≤ (2c + 2c')/B²`.

The proof:
- Sobolev in `ℝ≥0∞` (`sobolev_lintegral`), so no `t`-integrability is needed for each `ω`;
- Tonelli in `(ω, t)`;
- Markov.

`stronglyMeasurable_intervalIntegral_param`: `a ↦ ∫_c^{T a} F(a, s) ds` is strongly measurable for jointly
strongly measurable `F` and measurable `T`.
-/

@[expose] public section

namespace WaveTurbulence.Fixedpt

open MeasureTheory Set intervalIntegral
open scoped ENNReal

/-- **Sobolev in `t`, in `ℝ≥0∞`.** -/
theorem sobolev_lintegral {a : ℝ} {f g : ℝ → ℂ}
    (hfg : ∀ t ∈ Icc a (a + 1), ∀ t₀ ∈ Icc a (a + 1), f t - f t₀ = ∫ s in t₀..t, g s)
    (hg : IntervalIntegrable g volume a (a + 1)) {t : ℝ} (ht : t ∈ Icc a (a + 1)) :
    ENNReal.ofReal (‖f t‖ ^ 2) ≤
      2 * (∫⁻ s in Ioc a (a + 1), ENNReal.ofReal (‖f s‖ ^ 2)) +
        2 * ∫⁻ s in Ioc a (a + 1), ENNReal.ofReal (‖g s‖ ^ 2) := by
  have ha : a ≤ a + 1 := by linarith
  have haI : a ∈ Icc a (a + 1) := ⟨le_rfl, ha⟩
  -- `f` is continuous on `[a, a+1]`
  have hprim : ContinuousOn (fun s => ∫ x in a..s, g x) (Icc a (a + 1)) := by
    have h := intervalIntegral.continuousOn_primitive_interval' hg (by rw [uIcc_of_le ha]; exact haI)
    rwa [uIcc_of_le ha] at h
  have hfc : ContinuousOn f (Icc a (a + 1)) :=
    (continuousOn_const.add hprim).congr fun s hs => by
      have := hfg s hs a haI
      show f s = f a + ∫ x in a..s, g x
      rw [← this]
      ring
  have hf2 : IntegrableOn (fun s => ‖f s‖ ^ 2) (Ioc a (a + 1)) :=
    ((hfc.norm.pow 2).integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  by_cases hG : ∫⁻ s in Ioc a (a + 1), ENNReal.ofReal (‖g s‖ ^ 2) = ⊤
  · rw [hG]
    simp
  have hgm : AEStronglyMeasurable (fun s => ‖g s‖ ^ 2) (volume.restrict (Ioc a (a + 1))) :=
    hg.1.aestronglyMeasurable.norm.pow 2
  have hg2 : IntegrableOn (fun s => ‖g s‖ ^ 2) (Ioc a (a + 1)) :=
    (lintegral_ofReal_ne_top_iff_integrable hgm (ae_of_all _ fun _ => sq_nonneg _)).1 hG
  have hS := sq_norm_le_sobolev hfg hg ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha).2 hg2)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha).2 hf2) ht
  rw [intervalIntegral.integral_of_le ha, intervalIntegral.integral_of_le ha] at hS
  have e1 : ∫⁻ s in Ioc a (a + 1), ENNReal.ofReal (‖f s‖ ^ 2) =
      ENNReal.ofReal (∫ s in Ioc a (a + 1), ‖f s‖ ^ 2) :=
    (ofReal_integral_eq_lintegral_ofReal hf2 (ae_of_all _ fun _ => sq_nonneg _)).symm
  have e2 : ∫⁻ s in Ioc a (a + 1), ENNReal.ofReal (‖g s‖ ^ 2) =
      ENNReal.ofReal (∫ s in Ioc a (a + 1), ‖g s‖ ^ 2) :=
    (ofReal_integral_eq_lintegral_ofReal hg2 (ae_of_all _ fun _ => sq_nonneg _)).symm
  rw [e1, e2]
  have h1 : 0 ≤ ∫ s in Ioc a (a + 1), ‖f s‖ ^ 2 := setIntegral_nonneg measurableSet_Ioc fun _ _ => sq_nonneg _
  have h2 : 0 ≤ ∫ s in Ioc a (a + 1), ‖g s‖ ^ 2 := setIntegral_nonneg measurableSet_Ioc fun _ _ => sq_nonneg _
  calc ENNReal.ofReal (‖f t‖ ^ 2)
      ≤ ENNReal.ofReal (2 * (∫ s in Ioc a (a + 1), ‖f s‖ ^ 2) + 2 * ∫ s in Ioc a (a + 1), ‖g s‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal hS
    _ = _ := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

/-- `a ↦ ∫_c^{T a} F(a, s) ds` is strongly measurable. -/
theorem stronglyMeasurable_intervalIntegral_param {α : Type*} [MeasurableSpace α] {F : α × ℝ → ℂ}
    (hF : StronglyMeasurable F) {T : α → ℝ} (hT : Measurable T) (c : ℝ) :
    StronglyMeasurable fun a => ∫ s in c..T a, F (a, s) := by
  have hpart : ∀ (lo hi : α → ℝ), Measurable lo → Measurable hi →
      StronglyMeasurable fun a => ∫ s in Ioc (lo a) (hi a), F (a, s) := by
    intro lo hi hlo hhi
    have hset : MeasurableSet {z : α × ℝ | z.2 ∈ Ioc (lo z.1) (hi z.1)} :=
      (measurableSet_lt (hlo.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hhi.comp measurable_fst))
    have h := (hF.indicator hset).integral_prod_right' (ν := (volume : Measure ℝ))
    convert h using 1
    funext a
    rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
    rfl
  have h1 := hpart (fun _ => c) T measurable_const hT
  have h2 := hpart T (fun _ => c) hT measurable_const
  convert h1.sub h2 using 1
  funext a
  rfl

/-- **Large deviations of `sup_t |f(t)|`** from second moments of `f` and `∂_t f`. -/
theorem prob_sup_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ] {F : Set Ω} (hF : MeasurableSet F)
    {a : ℝ} {f g : Ω → ℝ → ℂ}
    (hf : StronglyMeasurable (Function.uncurry f)) (hg : StronglyMeasurable (Function.uncurry g))
    (hfg : ∀ ω ∈ F, ∀ t ∈ Icc a (a + 1), ∀ t₀ ∈ Icc a (a + 1), f ω t - f ω t₀ = ∫ s in t₀..t, g ω s)
    (hgi : ∀ ω ∈ F, IntervalIntegrable (g ω) volume a (a + 1))
    {c c' B : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c') (hB : 0 < B)
    (hmf : ∀ t ∈ Ioo a (a + 1), Integrable (fun ω => ‖f ω t‖ ^ 2) (μ.restrict F) ∧
      ∫ ω in F, ‖f ω t‖ ^ 2 ∂μ ≤ c)
    (hmg : ∀ t ∈ Ioo a (a + 1), Integrable (fun ω => ‖g ω t‖ ^ 2) (μ.restrict F) ∧
      ∫ ω in F, ‖g ω t‖ ^ 2 ∂μ ≤ c') :
    μ (F ∩ {ω | ∃ t ∈ Icc a (a + 1), B < ‖f ω t‖}) ≤ ENNReal.ofReal ((2 * c + 2 * c') / B ^ 2) := by
  set G : Ω → ℝ≥0∞ := (fun ω => 2 * (∫⁻ s in Ioc a (a + 1), ENNReal.ofReal (‖f ω s‖ ^ 2)) +
    2 * ∫⁻ s in Ioc a (a + 1), ENNReal.ofReal (‖g ω s‖ ^ 2)) with hGdef
  have hHf : Measurable (Function.uncurry fun ω s => ENNReal.ofReal (‖f ω s‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp (hf.measurable.norm.pow_const 2)
  have hHg : Measurable (Function.uncurry fun ω s => ENNReal.ofReal (‖g ω s‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp (hg.measurable.norm.pow_const 2)
  have hm1 : Measurable fun ω => 2 * ∫⁻ s in Ioc a (a + 1), ENNReal.ofReal (‖f ω s‖ ^ 2) :=
    (hHf.lintegral_prod_right' (ν := volume.restrict (Ioc a (a + 1)))).const_mul 2
  have hm2 : Measurable fun ω => 2 * ∫⁻ s in Ioc a (a + 1), ENNReal.ofReal (‖g ω s‖ ^ 2) :=
    (hHg.lintegral_prod_right' (ν := volume.restrict (Ioc a (a + 1)))).const_mul 2
  have hGm : Measurable G := by rw [hGdef]; exact hm1.add hm2
  -- Sobolev
  have hsub : F ∩ {ω | ∃ t ∈ Icc a (a + 1), B < ‖f ω t‖} ⊆ {ω | ENNReal.ofReal (B ^ 2) ≤ G ω} ∩ F := by
    rintro ω ⟨hω, t, ht, hBt⟩
    refine ⟨?_, hω⟩
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (sobolev_lintegral (hfg ω hω) (hgi ω hω) ht)
    nlinarith [norm_nonneg (f ω t)]
  -- Tonelli and the moments
  have hone : ∀ {h : Ω → ℝ → ℂ} {C : ℝ}, Measurable (Function.uncurry fun ω s => ENNReal.ofReal (‖h ω s‖ ^ 2)) →
      (∀ t ∈ Ioo a (a + 1), Integrable (fun ω => ‖h ω t‖ ^ 2) (μ.restrict F) ∧
        ∫ ω in F, ‖h ω t‖ ^ 2 ∂μ ≤ C) →
      ∫⁻ ω in F, (∫⁻ s in Ioc a (a + 1), ENNReal.ofReal (‖h ω s‖ ^ 2)) ∂μ ≤ ENNReal.ofReal C := by
    intro h C hH hm
    rw [lintegral_lintegral_swap hH.aemeasurable, setLIntegral_congr Ioo_ae_eq_Ioc.symm]
    calc ∫⁻ s in Ioo a (a + 1), ∫⁻ ω in F, ENNReal.ofReal (‖h ω s‖ ^ 2) ∂μ
        ≤ ∫⁻ _s in Ioo a (a + 1), ENNReal.ofReal C := by
          refine setLIntegral_mono measurable_const fun s hs => ?_
          rw [← ofReal_integral_eq_lintegral_ofReal (hm s hs).1 (ae_of_all _ fun _ => sq_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (hm s hs).2
      _ = ENNReal.ofReal C := by
          rw [setLIntegral_const, Real.volume_Ioo, add_sub_cancel_left, ENNReal.ofReal_one, mul_one]
  have hint : ∫⁻ ω in F, G ω ∂μ ≤ 2 * ENNReal.ofReal c + 2 * ENNReal.ofReal c' := by
    have hI1 : Measurable fun ω => ∫⁻ s in Ioc a (a + 1), ENNReal.ofReal (‖f ω s‖ ^ 2) :=
      hHf.lintegral_prod_right'
    have hI2 : Measurable fun ω => ∫⁻ s in Ioc a (a + 1), ENNReal.ofReal (‖g ω s‖ ^ 2) :=
      hHg.lintegral_prod_right'
    rw [lintegral_add_left hm1, lintegral_const_mul _ hI1, lintegral_const_mul _ hI2]
    gcongr
    · exact hone hHf hmf
    · exact hone hHg hmg
  have hB2 : 0 < B ^ 2 := by positivity
  calc μ (F ∩ {ω | ∃ t ∈ Icc a (a + 1), B < ‖f ω t‖})
      ≤ μ ({ω | ENNReal.ofReal (B ^ 2) ≤ G ω} ∩ F) := measure_mono hsub
    _ = μ.restrict F {ω | ENNReal.ofReal (B ^ 2) ≤ G ω} := (Measure.restrict_apply' hF).symm
    _ ≤ (∫⁻ ω in F, G ω ∂μ) / ENNReal.ofReal (B ^ 2) :=
        meas_ge_le_lintegral_div hGm.aemeasurable (ENNReal.ofReal_pos.2 hB2).ne' ENNReal.ofReal_ne_top
    _ ≤ (2 * ENNReal.ofReal c + 2 * ENNReal.ofReal c') / ENNReal.ofReal (B ^ 2) := by gcongr
    _ = ENNReal.ofReal ((2 * c + 2 * c') / B ^ 2) := by
        rw [ENNReal.ofReal_div_of_pos hB2, ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

end WaveTurbulence.Fixedpt
