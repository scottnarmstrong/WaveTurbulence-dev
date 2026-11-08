/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.FiltLink.Decay
public import WaveTurbulence.Foundations.Flower.FlShell.Shell
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
/-! # D5a FILT-LINK: the filters of one link are presented multipliers (o82 (14.2), moment bound)

o82 (14.2): "The moment bound follows from scaling the Fourier transform of `ϑ` and convolution; it is uniform in
all scales." Here:
- `SmoothFilter f`: `f` is `C⁴`, compactly supported and even (o82 Lemma 18.1: only fixed Schwartz seminorms of
  the one-dimensional multiplier are used);
- `SmoothFilter.presentedMult`: `u ↦ f(|2u|/M)` is `K_f`-presented at every scale `0 ≤ L ≤ M`, by Fourier
  inversion (`G = 𝓕f`, shift `T v = 2v/M`), with `K_f = ∫ ‖𝓕f v‖ (1 + 2|v|)² dv` (scale-free: `L|2v/M| ≤ 2|v|`);
- `chi0` and `FlShell.chiD` are smooth filters; `filtProf a = if a then chiD else chi0` (the `filtWeight` profile);
- `linkFiltMult S a M u = ∏_{i ∈ S} filtProf (a i) (|2u|/M i)`: the filters of one link at `|Ω| = |2u|`;
  `exists_presentedMult_linkFiltMult` (`K₁^{#S}`-presented when every `M i ≥ L`) and its sup bound `B^{#S}`. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal FourierTransform
namespace WaveTurbulence.Flower.FiltLink
open WaveTurbulence.Incoh

/-- The scalar class of o82's filter profiles: `C⁴`, compactly supported, even. -/
structure SmoothFilter (f : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ 4 f
  compact : HasCompactSupport f
  even : ∀ x, f (-x) = f x

theorem hasCompactSupport_iteratedDeriv {g : ℝ → ℂ} (hg : HasCompactSupport g) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n g) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hg
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv

namespace SmoothFilter

variable {f : ℝ → ℝ}

theorem contDiff_complex (hf : SmoothFilter f) : ContDiff ℝ 4 (fun x => (f x : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hf.smooth

theorem hasCompactSupport_complex (hf : SmoothFilter f) : HasCompactSupport (fun x => (f x : ℂ)) :=
  hf.compact.comp_left Complex.ofReal_zero

theorem integrable_iteratedDeriv (hf : SmoothFilter f) (k : ℕ) (hk : k ≤ 4) :
    Integrable (iteratedDeriv k (fun x => (f x : ℂ))) :=
  (hf.contDiff_complex.continuous_iteratedDeriv k (by exact_mod_cast hk)).integrable_of_hasCompactSupport
    (hasCompactSupport_iteratedDeriv hf.hasCompactSupport_complex k)

theorem integrable_complex (hf : SmoothFilter f) : Integrable (fun x => (f x : ℂ)) := by
  simpa only [iteratedDeriv_zero] using hf.integrable_iteratedDeriv 0 (by norm_num)

theorem continuous_fourier (hf : SmoothFilter f) : Continuous (𝓕 (fun x => (f x : ℂ))) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hf.integrable_complex

theorem abs_eq (hf : SmoothFilter f) (x : ℝ) : f |x| = f x := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, hf.even]

private theorem weight_le (v : ℝ) : (1 + 2 * |v|) ^ 2 * (1 + v ^ 2) ≤ 16 * (1 + |v| ^ 4) := by
  have ha := abs_nonneg v
  have hv : v ^ 2 = |v| ^ 2 := (sq_abs v).symm
  rw [hv]
  nlinarith [sq_nonneg (|v| - 1), sq_nonneg (|v| ^ 2 - 1), mul_nonneg ha (sq_nonneg (|v| - 1)),
    sq_nonneg |v|, pow_nonneg ha 3, pow_nonneg ha 4]

/-- The Fourier transform of a smooth filter with its weight `(1 + 2|v|)²` is dominated by `A (1 + v²)⁻¹`. -/
theorem fourier_weight_le (hf : SmoothFilter f) : ∃ A : ℝ, 0 ≤ A ∧ ∀ v : ℝ,
    ‖𝓕 (fun x => (f x : ℂ)) v‖ * (1 + 2 * |v|) ^ 2 ≤ A * (1 + v ^ 2)⁻¹ := by
  set A₀ : ℝ := (∫ x, ‖(fun x => (f x : ℂ)) x‖) +
    ((2 * Real.pi) ^ 4)⁻¹ * ∫ x, ‖iteratedDeriv 4 (fun x => (f x : ℂ)) x‖
  have hA₀ : 0 ≤ A₀ := by positivity
  refine ⟨16 * A₀, by positivity, fun v => ?_⟩
  have hdec := Real.one_add_pow_mul_norm_fourier_le hf.contDiff_complex
    (fun k hk => hf.integrable_iteratedDeriv k hk) v
  have hn := norm_nonneg (𝓕 (fun x => (f x : ℂ)) v)
  have hp : 0 < 1 + v ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hp]
  calc
    _ = ‖𝓕 (fun x => (f x : ℂ)) v‖ * ((1 + 2 * |v|) ^ 2 * (1 + v ^ 2)) := by ring
    _ ≤ ‖𝓕 (fun x => (f x : ℂ)) v‖ * (16 * (1 + |v| ^ 4)) := mul_le_mul_of_nonneg_left (weight_le v) hn
    _ = 16 * ((1 + |v| ^ 4) * ‖𝓕 (fun x => (f x : ℂ)) v‖) := by ring
    _ ≤ 16 * A₀ := by gcongr

theorem integrable_fourier_weight (hf : SmoothFilter f) :
    Integrable (fun v : ℝ => ‖𝓕 (fun x => (f x : ℂ)) v‖ * (1 + 2 * |v|) ^ 2) := by
  obtain ⟨A, hA, hb⟩ := hf.fourier_weight_le
  refine (integrable_inv_one_add_sq.const_mul A).mono' ?_ (Filter.Eventually.of_forall fun v => ?_)
  · exact (hf.continuous_fourier.norm.mul (by fun_prop)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    exact hb v

theorem integrable_fourier (hf : SmoothFilter f) : Integrable (𝓕 (fun x => (f x : ℂ))) := by
  refine hf.integrable_fourier_weight.mono' hf.continuous_fourier.aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => ?_)
  have h1 : 1 ≤ (1 + 2 * |v|) ^ 2 := one_le_pow₀ (by linarith [abs_nonneg v])
  exact le_mul_of_one_le_right (norm_nonneg _) h1

/-- The moment constant `K_f = ∫ ‖𝓕f v‖ (1 + 2|v|)² dv` of a smooth filter. -/
def momentConst (f : ℝ → ℝ) : ℝ := ∫ v : ℝ, ‖𝓕 (fun x => (f x : ℂ)) v‖ * (1 + 2 * |v|) ^ 2

theorem momentConst_nonneg (f : ℝ → ℝ) : 0 ≤ momentConst f :=
  integral_nonneg fun v => by positivity

/-- **o82 (14.2) for one filter**: `u ↦ f(|2u|/M)` is `K_f`-presented at every scale `0 ≤ L ≤ M`. -/
theorem presentedMult (hf : SmoothFilter f) {L M : ℝ} (hL : 0 ≤ L) (hLM : L ≤ M) :
    PresentedMult L (momentConst f) (fun u => ((f (|2 * u| / M) : ℝ) : ℂ)) := by
  have hM : 0 ≤ M := hL.trans hLM
  refine ⟨ℝ, inferInstance, volume, inferInstance, 𝓕 (fun x => (f x : ℂ)), fun v => 2 * v / M,
    hf.continuous_fourier.measurable, by fun_prop, hf.integrable_fourier, ?_, ?_⟩
  · intro u
    have hinv := Continuous.fourierInv_fourier_eq
      (Complex.continuous_ofReal.comp hf.smooth.continuous) hf.integrable_complex hf.integrable_fourier
    have harg : f (|2 * u| / M) = f (2 * u / M) := by
      rw [show |2 * u| / M = |2 * u / M| by rw [abs_div, abs_of_nonneg hM], hf.abs_eq]
    dsimp only
    rw [harg]
    have h := congrFun hinv (2 * u / M)
    simp only [Function.comp_apply] at h
    rw [← h, Real.fourierInv_eq']
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun v => ?_
    simp only [smul_eq_mul, WeylSums.e, RCLike.inner_apply', conj_trivial]
    rw [mul_comm]
    congr 3
    push_cast
    ring
  · have hint := hf.integrable_fourier_weight
    calc
      _ ≤ ∫⁻ v : ℝ, ENNReal.ofReal (‖𝓕 (fun x => (f x : ℂ)) v‖ * (1 + 2 * |v|) ^ 2) := by
        apply lintegral_mono
        intro v
        dsimp only
        rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply pow_le_pow_left₀ (by positivity)
        have h : L * |2 * v / M| ≤ 2 * |v| := by
          rcases hM.lt_or_eq with hMp | hM0
          · rw [abs_div, abs_of_pos hMp, abs_mul, abs_two, mul_div_assoc', div_le_iff₀ hMp]
            nlinarith [abs_nonneg v]
          · rw [← hM0, div_zero, abs_zero, mul_zero]; positivity
        linarith
      _ = _ := (ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall fun v => by positivity)).symm

end SmoothFilter

/-! ### The two filter profiles -/

theorem smoothFilter_chi0 : SmoothFilter chi0 where
  smooth := by rw [FlShell.chi0_eq_fourier]; exact Fourier.chi0_contDiff
  compact := by rw [FlShell.chi0_eq_fourier]; exact Fourier.chi0_hasCompactSupport
  even x := by simp only [chi0, abs_neg]

theorem deriv_chi0_neg (x : ℝ) : deriv chi0 (-x) = -deriv chi0 x := by
  have h : (fun y => chi0 (-y)) = chi0 := funext fun y => by simp only [chi0, abs_neg]
  have h2 := deriv_comp_neg (f := chi0) (x := x)
  rw [h] at h2
  rw [h2, neg_neg]

theorem smoothFilter_chiD : SmoothFilter FlShell.chiD where
  smooth := by
    have h5 : ContDiff ℝ (4 + 1) chi0 := by rw [FlShell.chi0_eq_fourier]; exact Fourier.chi0_contDiff
    have hd : ContDiff ℝ 4 (deriv chi0) := (contDiff_succ_iff_deriv.mp h5).2.2
    unfold FlShell.chiD
    exact (contDiff_id.neg).mul hd
  compact := by
    apply HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
    intro x hx
    by_contra h
    have hs := (FlShell.chiD_support h).2
    exact hx ⟨(abs_lt.mp hs).1.le, (abs_lt.mp hs).2.le⟩
  even x := by
    simp only [FlShell.chiD, deriv_chi0_neg]
    ring

/-- The profile of a filtered branch: `chiD` if annular, else `chi0` (`ProtDefs.filtWeight`'s profile). -/
def filtProf (a : Bool) : ℝ → ℝ := if a then FlShell.chiD else chi0

theorem smoothFilter_filtProf (a : Bool) : SmoothFilter (filtProf a) := by
  cases a
  · exact smoothFilter_chi0
  · exact smoothFilter_chiD

/-- A uniform bound for both filter profiles. -/
theorem exists_filtProf_bound : ∃ B : ℝ, 1 ≤ B ∧ ∀ (a : Bool) (x : ℝ), |filtProf a x| ≤ B := by
  obtain ⟨B₀, hB₀⟩ := smoothFilter_chi0.smooth.continuous.bounded_above_of_compact_support
    smoothFilter_chi0.compact
  obtain ⟨B₁, hB₁⟩ := smoothFilter_chiD.smooth.continuous.bounded_above_of_compact_support
    smoothFilter_chiD.compact
  refine ⟨max 1 (max B₀ B₁), le_max_left _ _, fun a x => ?_⟩
  cases a
  · exact (hB₀ x).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hB₁ x).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- **The filter multiplier of one link** at the bilinear frequency `u` (`|Ω| = |2u|` on both linked branches):
the filters `filtProf (a i) (|Ω| / M i)`, `i ∈ S`. -/
def linkFiltMult {ι : Type*} (S : Finset ι) (a : ι → Bool) (M : ι → ℝ) (u : ℝ) : ℂ :=
  ∏ i ∈ S, ((filtProf (a i) (|2 * u| / M i) : ℝ) : ℂ)

/-- The moment constant common to both profiles. -/
def filtMomentConst : ℝ := max 1 (max (SmoothFilter.momentConst chi0) (SmoothFilter.momentConst FlShell.chiD))

theorem one_le_filtMomentConst : 1 ≤ filtMomentConst := le_max_left _ _

theorem momentConst_filtProf_le (a : Bool) : SmoothFilter.momentConst (filtProf a) ≤ filtMomentConst := by
  cases a
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

/-- **o82 (14.2) for the filters of one link**: `linkFiltMult S a M` is `K₁^{#S}`-presented at every scale
`0 ≤ L ≤ min M`, with `K₁ = filtMomentConst` independent of all scales, flags and `S`. -/
theorem presentedMult_linkFiltMult {ι : Type*} (S : Finset ι) (a : ι → Bool) (M : ι → ℝ) {L : ℝ}
    (hL : 0 ≤ L) (hM : ∀ i ∈ S, L ≤ M i) :
    PresentedMult L (filtMomentConst ^ S.card) (linkFiltMult S a M) :=
  presentedMult_prod S hL (zero_le_one.trans one_le_filtMomentConst) _ fun i hi =>
    ((smoothFilter_filtProf (a i)).presentedMult hL (hM i hi)).mono (momentConst_filtProf_le (a i))

/-- The sup bound of the filters of one link. -/
theorem norm_linkFiltMult_le {ι : Type*} (S : Finset ι) (a : ι → Bool) (M : ι → ℝ) {B : ℝ}
    (hB : ∀ (a : Bool) (x : ℝ), |filtProf a x| ≤ B) (u : ℝ) :
    ‖linkFiltMult S a M u‖ ≤ B ^ S.card := by
  unfold linkFiltMult
  rw [norm_prod]
  calc
    _ ≤ ∏ _i ∈ S, B := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      fun i _ => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hB _ _
    _ = _ := Finset.prod_const B

end WaveTurbulence.Flower.FiltLink
