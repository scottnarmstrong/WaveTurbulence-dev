/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltLink.Basic
public import WaveTurbulence.Foundations.Incoh.LinkMixture

/-! # D5b-1 FILT-SRC: the `φ`-carrying link interface (D5B-MAP §2.1, `LayerLink`, `LinkMixture`)

Twins of main's `Incoh.normalizedLinkIntegral` and `Incoh.linkMixtureFactor` (and of their measurability,
integrability and product-domination lemmas), with one multiplier `φ i : ℝ → ℂ` per link `i`, carried by D5a's
filtered link factor `FiltLink.filtLinkTimeFactor` and filtered phase coefficient `FiltLink.filtLinkPhaseCoefficient`.
The multiplier is a function of link `i`'s bilinear frequency `⟨x_i, y_i⟩` (D5a `linkBilinear`); with `φ ≡ 1` each
twin is main's object literally (`…Filt_one`).

Copied by source from main `Incoh/LayerLink.lean` and `Incoh/LinkMixture.lean` (sha256 in COPIED-SHA256SUMS); the only
edits are `linkTimeFactor L γ δ Q → filtLinkTimeFactor L γ δ Q φ` and
`linkPhaseCoefficient L Q → filtLinkPhaseCoefficient L Q φ`. Main's `LayerLink`, `linkBox`, `LinkMixturePoint` and
`linkMixtureMeasure` are reused (they do not see the multiplier). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Flower.FiltSrc
open WaveTurbulence.Incoh WaveTurbulence.Flower.FiltLink

variable {d n : ℕ}

/-! ### `LayerLink` twins -/

/-- **The filtered coupling-normalized product integral** (twin of main's `normalizedLinkIntegral`,
TARGET (incohproof9)): link `i` carries the multiplier `φ i` of its bilinear frequency. -/
def normalizedLinkIntegralFilt (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    (I : Set (Fin n → Fin 2 → ℝ)) : ℂ :=
  ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) : ℝ) *
    ∫ t in I, ∏ i, filtLinkTimeFactor L γ δ (Q i) (φ i) (t i)

/-- `φ ≡ 1` is main's normalized link integral. -/
theorem normalizedLinkIntegralFilt_one (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (I : Set (Fin n → Fin 2 → ℝ)) :
    normalizedLinkIntegralFilt L γ δ Q (fun _ _ => 1) I = normalizedLinkIntegral L γ δ Q I := by
  simp only [normalizedLinkIntegralFilt, normalizedLinkIntegral, filtLinkTimeFactor_one]

/-- The filtered product integrand is integrable on every source subdomain of the link boxes. -/
theorem integrableOn_linkProductFilt {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d)
    (φ : Fin n → ℝ → ℂ) {I : Set (Fin n → Fin 2 → ℝ)} (hI : I ⊆ univ.pi (fun i => linkBox (Q i))) :
    IntegrableOn (fun t => ∏ i, filtLinkTimeFactor L γ δ (Q i) (φ i) (t i)) I :=
  (integrableOn_pi_product (fun i => integrableOn_filtLinkTimeFactor hL γ δ (Q i) (φ i))).mono_set hI

/-- Product domination for the filtered literal source factors. -/
theorem norm_linkProduct_integral_leFilt {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d)
    (φ : Fin n → ℝ → ℂ) {I : Set (Fin n → Fin 2 → ℝ)} (hI : I ⊆ univ.pi (fun i => linkBox (Q i))) :
    ‖∫ t in I, ∏ i, filtLinkTimeFactor L γ δ (Q i) (φ i) (t i)‖ ≤
      ∏ i, ∫ t in linkBox (Q i), ‖filtLinkTimeFactor L γ δ (Q i) (φ i) t‖ :=
  norm_setIntegral_pi_product_le hI (fun i => integrableOn_filtLinkTimeFactor hL γ δ (Q i) (φ i))

/-! ### `LinkMixture` twins -/

/-- **The filtered selected-link mixture factor** (twin of main's `linkMixtureFactor`): a selected link is expanded
over its filtered lattice phases, an unselected link keeps its filtered time factor. -/
def linkMixtureFactorFilt (L γ δ : ℝ) (Q : LayerLink d) (φ : ℝ → ℂ) (selected : Bool)
    (z : LinkMixturePoint d) : ℂ :=
  (linkBox Q).indicator
    (fun t => if selected then filtLinkPhaseCoefficient L Q φ z.1 else filtLinkTimeFactor L γ δ Q φ t) z.2

/-- `φ ≡ 1` is main's mixture factor. -/
theorem linkMixtureFactorFilt_one (L γ δ : ℝ) (Q : LayerLink d) (selected : Bool) :
    linkMixtureFactorFilt L γ δ Q (fun _ => 1) selected = linkMixtureFactor L γ δ Q selected := by
  funext z
  simp only [linkMixtureFactorFilt, linkMixtureFactor, filtLinkPhaseCoefficient_one, filtLinkTimeFactor_one]

/-- Filtered lattice coefficients are integrable for counting measure (finite support). -/
theorem integrable_linkPhaseCoefficientFilt {L : ℝ} (hL : 0 < L) (Q : LayerLink d) (φ : ℝ → ℂ) :
    Integrable (filtLinkPhaseCoefficient L Q φ) Measure.count := by
  have hfin := finite_support_filtLinkPhaseCoefficient hL Q φ
  refine integrable_count_iff.mpr (summable_of_ne_finset_zero (s := hfin.toFinset) (fun p hp => ?_))
  rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hp
  rw [hp, norm_zero]

/-- The filtered mixture factors are measurable, including their hard layer cutoffs. -/
theorem stronglyMeasurable_linkMixtureFactorFilt {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : LayerLink d) (φ : ℝ → ℂ) (selected : Bool) :
    StronglyMeasurable (linkMixtureFactorFilt L γ δ Q φ selected) := by
  have hp : Measurable (filtLinkPhaseCoefficient L Q φ) := measurable_of_countable _
  have ht := (continuous_filtLinkTimeFactor hL γ δ Q φ).measurable
  have hs : MeasurableSet {z : LinkMixturePoint d | z.2 ∈ linkBox Q} :=
    measurableSet_Icc.preimage measurable_snd
  cases selected
  · exact (ht.comp measurable_snd).stronglyMeasurable.indicator hs
  · exact (hp.comp measurable_fst).stronglyMeasurable.indicator hs

/-- Each filtered factor is integrable against its literal phase/time measure. -/
theorem integrable_linkMixtureFactorFilt {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : LayerLink d) (φ : ℝ → ℂ) (selected : Bool) :
    Integrable (linkMixtureFactorFilt L γ δ Q φ selected) (linkMixtureMeasure d selected) := by
  have hbox : Integrable ((linkBox Q).indicator (fun _ => (1 : ℂ))) := by
    rw [integrable_indicator_iff (s := linkBox Q) measurableSet_Icc]
    exact integrableOn_const (by rw [volume_linkBox]; norm_num)
  have ht : Integrable ((linkBox Q).indicator (filtLinkTimeFactor L γ δ Q φ)) :=
    (integrable_indicator_iff (s := linkBox Q) measurableSet_Icc).mpr
      (integrableOn_filtLinkTimeFactor hL γ δ Q φ)
  cases selected
  · have h := (integrable_const (1 : ℂ) (μ := Measure.dirac (0 : (Fin d → ℤ) × (Fin d → ℤ)))).mul_prod ht
    change Integrable (fun z : LinkMixturePoint d =>
      (linkBox Q).indicator (filtLinkTimeFactor L γ δ Q φ) z.2) ((Measure.dirac 0).prod volume)
    simpa only [one_mul] using h
  · have h := (integrable_linkPhaseCoefficientFilt hL Q φ).mul_prod hbox
    change Integrable (fun z : LinkMixturePoint d =>
      (linkBox Q).indicator (fun _ => filtLinkPhaseCoefficient L Q φ z.1) z.2) (Measure.count.prod volume)
    convert h using 1
    funext z
    by_cases hz : z.2 ∈ linkBox Q <;> simp [hz]

end WaveTurbulence.Flower.FiltSrc
