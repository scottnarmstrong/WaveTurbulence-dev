/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.FiltLink.Basic
/-! # D5a FILT-LINK: Fourier-presented link multipliers and the time-shift mixture (o82 (14.2))

o82 (14.2): Fourier inversion of the filters writes the filtered link as a mixture of time-shifted unfiltered
links, `A_H(s) = ∫ A(s + τ) dω_M(τ)`, with moments `∫ (1 + M_*|τ|)^q d|ω_M| ≤ C_q`.

`PresentedMult L K φ` is that presentation, on an arbitrary s-finite measure space (so that the point mass of
`h = 0` and products of several filters are instances, without convolutions): `φ u = ∫ G ω e(T ω · u) dμ` with
`∫ ‖G‖ (1 + L|T|)² dμ ≤ K` (`q = 2` at the scale `L ≤ M_*`). Proved here:
- `presentedMult_one` (`h = 0`), `presentedMult_mul`, `presentedMult_prod` (products: `K` multiplies);
- `filtLinkLatticeSum_eq_integral`: the mixture identity (14.2) on the literal finite lattice sum;
- `filtLayerLinkMass_le_of_shift`: a shift bound `∫_box |A(·+c)| ≤ (1+L|c|)² B` for every `c` gives
  `filtLayerLinkMass ≤ K B`. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace WaveTurbulence.Flower.FiltLink
open WaveTurbulence.Incoh

variable {d : ℕ}

/-- **o82 (14.2)**: `φ` is a superposition of the characters `u ↦ e(T ω · u)` with weight `G`, and the `L`-scaled
second moment of the weight is at most `K`. -/
def PresentedMult (L K : ℝ) (φ : ℝ → ℂ) : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : SFinite μ) (G : Ω → ℂ) (T : Ω → ℝ),
    Measurable G ∧ Measurable T ∧ Integrable G μ ∧
    (∀ u, φ u = ∫ ω, G ω * WeylSums.e (T ω * u) ∂μ) ∧
    (∫⁻ ω, ‖G ω‖ₑ * ENNReal.ofReal ((1 + L * |T ω|) ^ 2) ∂μ) ≤ ENNReal.ofReal K

/-- `h = 0`: the constant multiplier is the unit point mass at the zero shift. -/
theorem presentedMult_one (L : ℝ) : PresentedMult L 1 (fun _ => 1) := by
  refine ⟨Unit, inferInstance, Measure.dirac (), inferInstance, fun _ => 1, fun _ => 0,
    measurable_const, measurable_const, integrable_const _, ?_, ?_⟩
  · intro u
    simp
  · rw [lintegral_dirac]
    simp

theorem PresentedMult.mono {L K K' : ℝ} {φ : ℝ → ℂ} (h : PresentedMult L K φ) (hK : K ≤ K') :
    PresentedMult L K' φ := by
  obtain ⟨Ω, m, μ, hμ, G, T, hG, hT, hi, he, hk⟩ := h
  exact ⟨Ω, m, μ, hμ, G, T, hG, hT, hi, he, hk.trans (ENNReal.ofReal_le_ofReal hK)⟩

theorem measurable_shiftWeight {Ω : Type*} [MeasurableSpace Ω] {T : Ω → ℝ} (hT : Measurable T) (L : ℝ) :
    Measurable fun x => ENNReal.ofReal ((1 + L * |T x|) ^ 2) :=
  ENNReal.measurable_ofReal.comp
    (((continuous_const.add (continuous_const.mul continuous_abs)).pow 2).measurable.comp hT)

private theorem one_add_abs_add_sq_le {L a b : ℝ} (hL : 0 ≤ L) :
    (1 + L * |a + b|) ^ 2 ≤ (1 + L * |a|) ^ 2 * (1 + L * |b|) ^ 2 := by
  rw [← mul_pow]
  have h1 : 1 + L * |a + b| ≤ (1 + L * |a|) * (1 + L * |b|) := by
    have hab : L * |a + b| ≤ L * |a| + L * |b| := by
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left (abs_add_le a b) hL
    nlinarith [mul_nonneg (mul_nonneg hL (abs_nonneg a)) (mul_nonneg hL (abs_nonneg b))]
  exact pow_le_pow_left₀ (by positivity) h1 2

/-- Products of presented multipliers are presented; the moment constants multiply. -/
theorem presentedMult_mul {L K₁ K₂ : ℝ} {φ₁ φ₂ : ℝ → ℂ} (hL : 0 ≤ L) (hK₁ : 0 ≤ K₁)
    (h₁ : PresentedMult L K₁ φ₁) (h₂ : PresentedMult L K₂ φ₂) :
    PresentedMult L (K₁ * K₂) (fun u => φ₁ u * φ₂ u) := by
  obtain ⟨Ω₁, m₁, μ₁, s₁, G₁, T₁, hG₁, hT₁, hi₁, he₁, hk₁⟩ := h₁
  obtain ⟨Ω₂, m₂, μ₂, s₂, G₂, T₂, hG₂, hT₂, hi₂, he₂, hk₂⟩ := h₂
  refine ⟨Ω₁ × Ω₂, inferInstance, μ₁.prod μ₂, inferInstance, fun ω => G₁ ω.1 * G₂ ω.2,
    fun ω => T₁ ω.1 + T₂ ω.2, (hG₁.comp measurable_fst).mul (hG₂.comp measurable_snd),
    (hT₁.comp measurable_fst).add (hT₂.comp measurable_snd), hi₁.mul_prod hi₂, ?_, ?_⟩
  · intro u
    dsimp only
    rw [he₁, he₂, ← integral_prod_mul]
    congr 1
    funext ω
    rw [add_mul, WeylSums.e_add]
    ring
  · calc
      _ ≤ ∫⁻ ω : Ω₁ × Ω₂, (‖G₁ ω.1‖ₑ * ENNReal.ofReal ((1 + L * |T₁ ω.1|) ^ 2)) *
            (‖G₂ ω.2‖ₑ * ENNReal.ofReal ((1 + L * |T₂ ω.2|) ^ 2)) ∂(μ₁.prod μ₂) := by
        apply lintegral_mono
        intro ω
        dsimp only
        rw [enorm_mul, mul_mul_mul_comm, ← ENNReal.ofReal_mul (by positivity)]
        gcongr
        exact one_add_abs_add_sq_le hL
      _ = (∫⁻ x, ‖G₁ x‖ₑ * ENNReal.ofReal ((1 + L * |T₁ x|) ^ 2) ∂μ₁) *
            ∫⁻ y, ‖G₂ y‖ₑ * ENNReal.ofReal ((1 + L * |T₂ y|) ^ 2) ∂μ₂ :=
        lintegral_prod_mul (hG₁.enorm.mul (measurable_shiftWeight hT₁ L)).aemeasurable
          (hG₂.enorm.mul (measurable_shiftWeight hT₂ L)).aemeasurable
      _ ≤ ENNReal.ofReal K₁ * ENNReal.ofReal K₂ := mul_le_mul' hk₁ hk₂
      _ = _ := (ENNReal.ofReal_mul hK₁).symm

/-- Finite products of presented multipliers. -/
theorem presentedMult_prod {ι : Type*} (S : Finset ι) {L K : ℝ} (hL : 0 ≤ L) (hK : 0 ≤ K)
    (φ : ι → ℝ → ℂ) (h : ∀ i ∈ S, PresentedMult L K (φ i)) :
    PresentedMult L (K ^ S.card) (fun u => ∏ i ∈ S, φ i u) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, Finset.card_empty, pow_zero] using presentedMult_one L
  | insert a S ha ih =>
    have h' := presentedMult_mul hL hK (h a (Finset.mem_insert_self a S))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa only [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ, mul_comm] using h'

/-! ### The mixture identity (14.2) on the literal link -/

theorem linkPhase_add_shift (L s c : ℝ) (A : LinkParameters d) (p : (Fin d → ℤ) × (Fin d → ℤ)) :
    WeylSums.e (linkPhase L (s + c) A p) = WeylSums.e (linkPhase L s A p) * WeylSums.e (c * linkBilinear L p) := by
  rw [← WeylSums.e_add]
  congr 1
  unfold linkPhase linkBilinear
  ring

/-- **o82 (14.2)**: the filtered link is the `G`-mixture of the `T`-shifted literal links. -/
theorem filtLinkLatticeSum_eq_integral {L : ℝ} (hL : 0 < L) (s : ℝ) (A : LinkParameters d)
    {φ : ℝ → ℂ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {G : Ω → ℂ} {T : Ω → ℝ}
    (hT : Measurable T) (hGi : Integrable G μ) (he : ∀ u, φ u = ∫ ω, G ω * WeylSums.e (T ω * u) ∂μ) :
    filtLinkLatticeSum L s A φ = ∫ ω, G ω * linkLatticeSum L (s + T ω) A ∂μ := by
  classical
  set S := (finite_support_linkAmplitude hL A).toFinset
  have hS (p : (Fin d → ℤ) × (Fin d → ℤ)) (hp : p ∉ S) : linkAmplitude L A p = 0 := by
    simpa only [S, Set.Finite.mem_toFinset, Function.mem_support, not_not] using hp
  have hlink (c : ℝ) : linkLatticeSum L c A = ∑ p ∈ S, linkAmplitude L A p * WeylSums.e (linkPhase L c A p) :=
    tsum_eq_sum fun p hp => by simp only [hS p hp, zero_mul]
  have hfilt : filtLinkLatticeSum L s A φ =
      ∑ p ∈ S, linkAmplitude L A p * φ (linkBilinear L p) * WeylSums.e (linkPhase L s A p) :=
    tsum_eq_sum fun p hp => by simp only [hS p hp, zero_mul]
  have hterm (p : (Fin d → ℤ) × (Fin d → ℤ)) :
      Integrable (fun ω => G ω * (linkAmplitude L A p * WeylSums.e (linkPhase L (s + T ω) A p))) μ := by
    refine hGi.mul_bdd (c := ‖linkAmplitude L A p‖) ?_ ?_
    · have hc : Continuous fun c : ℝ => linkAmplitude L A p * WeylSums.e (linkPhase L c A p) := by
        unfold WeylSums.e linkPhase; fun_prop
      exact (hc.measurable.comp (measurable_const.add hT)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ω => by rw [norm_mul, WeylSums.norm_e, mul_one]
  rw [hfilt]
  simp_rw [hlink, Finset.mul_sum]
  rw [integral_finsetSum S fun p _ => hterm p]
  apply Finset.sum_congr rfl
  intro p _
  have hfun : (fun ω => G ω * (linkAmplitude L A p * WeylSums.e (linkPhase L (s + T ω) A p))) =
      fun ω => (linkAmplitude L A p * WeylSums.e (linkPhase L s A p)) *
        (G ω * WeylSums.e (T ω * linkBilinear L p)) := by
    funext ω
    rw [linkPhase_add_shift]
    ring
  rw [hfun, integral_const_mul, ← he]
  ring

theorem enorm_filtLinkLatticeSum_le {L : ℝ} (hL : 0 < L) (s : ℝ) (A : LinkParameters d)
    {φ : ℝ → ℂ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {G : Ω → ℂ} {T : Ω → ℝ}
    (hT : Measurable T) (hGi : Integrable G μ) (he : ∀ u, φ u = ∫ ω, G ω * WeylSums.e (T ω * u) ∂μ) :
    ‖filtLinkLatticeSum L s A φ‖ₑ ≤ ∫⁻ ω, ‖G ω‖ₑ * ‖linkLatticeSum L (s + T ω) A‖ₑ ∂μ := by
  rw [filtLinkLatticeSum_eq_integral hL s A hT hGi he]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  congr 1
  funext ω
  rw [enorm_mul]

/-- The filtered pair mass is the `‖G‖`-mixture of the shifted literal pair masses (Tonelli). -/
theorem filtLayerLinkMass_le_lintegral {L : ℝ} (hL : 0 < L) (lam : ℝ) (Q : LayerLink d)
    {φ : ℝ → ℂ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ] {G : Ω → ℂ} {T : Ω → ℝ}
    (hG : Measurable G) (hT : Measurable T) (hGi : Integrable G μ)
    (he : ∀ u, φ u = ∫ ω, G ω * WeylSums.e (T ω * u) ∂μ) :
    filtLayerLinkMass L lam Q φ ≤
      ∫⁻ ω, ‖G ω‖ₑ * (∫⁻ t in linkBox Q,
        ‖linkLatticeSum L (((Q.orientation : ℤ) : ℝ) * lam * (t 0 - t 1) + T ω) Q.toLinkParameters‖ₑ) ∂μ := by
  have hc := continuous_linkLatticeSum hL Q.toLinkParameters
  have hjoint : Measurable fun z : (Fin 2 → ℝ) × Ω =>
      ‖G z.2‖ₑ * ‖linkLatticeSum L (((Q.orientation : ℤ) : ℝ) * lam * (z.1 0 - z.1 1) + T z.2)
        Q.toLinkParameters‖ₑ := by
    have harg : Measurable fun z : (Fin 2 → ℝ) × Ω =>
        ((Q.orientation : ℤ) : ℝ) * lam * (z.1 0 - z.1 1) + T z.2 := by fun_prop
    exact (hG.comp measurable_snd).enorm.mul (hc.measurable.comp harg).enorm
  unfold filtLayerLinkMass
  calc
    _ ≤ ∫⁻ t in linkBox Q, (∫⁻ ω, ‖G ω‖ₑ *
          ‖linkLatticeSum L (((Q.orientation : ℤ) : ℝ) * lam * (t 0 - t 1) + T ω) Q.toLinkParameters‖ₑ ∂μ) :=
      lintegral_mono fun t => enorm_filtLinkLatticeSum_le hL _ _ hT hGi he
    _ = ∫⁻ ω, (∫⁻ t in linkBox Q, ‖G ω‖ₑ *
          ‖linkLatticeSum L (((Q.orientation : ℤ) : ℝ) * lam * (t 0 - t 1) + T ω) Q.toLinkParameters‖ₑ) ∂μ :=
      lintegral_lintegral_swap hjoint.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro ω
      apply lintegral_const_mul
      have harg : Measurable fun t : Fin 2 → ℝ =>
          ((Q.orientation : ℤ) : ℝ) * lam * (t 0 - t 1) + T ω := by fun_prop
      exact (hc.measurable.comp harg).enorm

/-- **The transfer**: a bound `(1 + L|c|)² B` on every `c`-shifted literal pair mass gives `K B` for the filtered
pair mass of a `K`-presented multiplier. -/
theorem filtLayerLinkMass_le_of_shift {L : ℝ} (hL : 0 < L) (lam : ℝ) (Q : LayerLink d)
    {K : ℝ} {φ : ℝ → ℂ} (hP : PresentedMult L K φ) (B : ℝ≥0∞)
    (hB : ∀ c : ℝ, (∫⁻ t in linkBox Q,
        ‖linkLatticeSum L (((Q.orientation : ℤ) : ℝ) * lam * (t 0 - t 1) + c) Q.toLinkParameters‖ₑ) ≤
      ENNReal.ofReal ((1 + L * |c|) ^ 2) * B) :
    filtLayerLinkMass L lam Q φ ≤ ENNReal.ofReal K * B := by
  obtain ⟨Ω, m, μ, hμ, G, T, hG, hT, hi, he, hk⟩ := hP
  calc
    _ ≤ _ := filtLayerLinkMass_le_lintegral hL lam Q hG hT hi he
    _ ≤ ∫⁻ ω, ‖G ω‖ₑ * ENNReal.ofReal ((1 + L * |T ω|) ^ 2) * B ∂μ := by
      apply lintegral_mono
      intro ω
      dsimp only
      rw [mul_assoc]
      exact mul_le_mul' le_rfl (hB (T ω))
    _ = (∫⁻ ω, ‖G ω‖ₑ * ENNReal.ofReal ((1 + L * |T ω|) ^ 2) ∂μ) * B :=
      lintegral_mul_const _ (hG.enorm.mul (measurable_shiftWeight hT L))
    _ ≤ _ := mul_le_mul' hk le_rfl

end WaveTurbulence.Flower.FiltLink
