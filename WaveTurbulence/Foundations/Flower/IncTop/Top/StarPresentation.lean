/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Top.RootMeasure
public import WaveTurbulence.Foundations.Flower.IncTop.Top.StarStatements
public import Mathlib.MeasureTheory.Integral.Pi

/-! Ported by source from C2-B-TOP `C2BTop.StarPresentation` (sha256 in COPIED-SHA256SUMS); mechanical edits only.
 # Products of star presentations as root-modulated internal measures

For finitely many star weights `ω_i`, each presented by a C2-A measure `M i` on `(Mom d)^4`, and integer
rows `r i s` expressing the `s`-th star momentum as `k + Σ_{ij} r i s ij • x_{ij}` (root coefficient
one, internal paired momenta `x`), `starProduct M r` is a `RootMeasure` with
`(G.at k).value x = ∏_i ω_i (k + r i · x)` and `G.momentMass J ≤ ∏_i starMoment J (M i)`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Finset
open scoped ENNReal
namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh WaveTurbulence.Cut2A

/-- The internal linear form `x ↦ Σ_{ij} r ij • x_{ij}` of an integer row. -/
def rowLinear {d n : ℕ} (r : (Fin n × Fin 2) → ℤ) (x : PairedMomentum d n) : Mom d :=
  ∑ ij, ((r ij : ℤ) : ℝ) • x ij

/-- The star momenta of a star with rows `r`, at root `k` and internal momenta `x`. -/
def rowStar {d n : ℕ} (r : Fin 4 → (Fin n × Fin 2) → ℤ) (k : Mom d) (x : PairedMomentum d n) : Star d :=
  WithLp.toLp 2 (fun s => k + rowLinear (r s) x)

theorem fourierChar_sum_coe {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((Real.fourierChar (∑ i ∈ s, f i) : Circle) : ℂ) = ∏ i ∈ s, (Real.fourierChar (f i) : ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty, AddChar.map_zero_eq_one, Circle.coe_one, prod_empty]
  | @insert i s hi ih => rw [sum_insert hi, AddChar.map_add_eq_mul, Circle.coe_mul, prod_insert hi, ih]

theorem one_add_norm_sum_le_prod {ι E : Type*} [SeminormedAddCommGroup E] (s : Finset ι) (v : ι → E) :
    1 + ‖∑ i ∈ s, v i‖ ≤ ∏ i ∈ s, (1 + ‖v i‖) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [sum_insert hi, prod_insert hi]
    have h1 := norm_add_le (v i) (∑ j ∈ s, v j)
    have h2 : 0 ≤ ‖v i‖ := norm_nonneg _
    have h3 : 0 ≤ ‖∑ j ∈ s, v j‖ := norm_nonneg _
    nlinarith

variable {d n : ℕ} {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]

/-- The internal frequency of a product of star frequencies. -/
def starProductFrequency (r : ι → Fin 4 → (Fin n × Fin 2) → ℤ) (ξ : ι → Star d) : PairedMomentum d n :=
  WithLp.toLp 2 (fun ij => ∑ i, ∑ s, ((r i s ij : ℤ) : ℝ) • ξ i s)

/-- The product of star presentations, as a root-modulated internal Fourier measure. -/
def starProduct (M : (i : ι) → SpatialMeasure (Star d) (α i)) (hM : ∀ i, Measurable (M i).amplitude)
    (r : ι → Fin 4 → (Fin n × Fin 2) → ℤ) : RootMeasure d n ((i : ι) → α i) where
  base :=
    { μ := Measure.pi (fun i => (M i).μ)
      sigmaFinite := inferInstance
      frequency := fun θ => starProductFrequency r (fun i => (M i).frequency (θ i))
      frequency_measurable := by
        unfold starProductFrequency
        apply (PiLp.continuous_toLp 2 _).measurable.comp
        refine measurable_pi_iff.mpr fun ij => ?_
        refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun s _ => ?_
        exact (((PiLp.continuous_apply 2 _ s).measurable.comp
          ((M i).frequency_measurable.comp (measurable_pi_apply i)))).const_smul ((r i s ij : ℤ) : ℝ)
      amplitude := fun θ => ∏ i, (M i).amplitude (θ i)
      amplitude_integrable := Integrable.fintype_prod_dep (fun i => (M i).amplitude_integrable) }
  amplitude_measurable := Finset.measurable_prod _ fun i _ => (hM i).comp (measurable_pi_apply i)
  root := fun θ => ∑ i, starRootFrequency ((M i).frequency (θ i))
  root_measurable := by
    refine Finset.measurable_sum _ fun i _ => ?_
    unfold starRootFrequency
    refine Finset.measurable_sum _ fun s _ => ?_
    exact (PiLp.continuous_apply 2 _ s).measurable.comp
      ((M i).frequency_measurable.comp (measurable_pi_apply i))

/-- The exponent identity behind the product value. -/
theorem starProduct_phase (r : ι → Fin 4 → (Fin n × Fin 2) → ℤ) (ξ : ι → Star d) (k : Mom d)
    (x : PairedMomentum d n) :
    inner ℝ (∑ i, starRootFrequency (ξ i)) k + inner ℝ (starProductFrequency r ξ) x =
      ∑ i, inner ℝ (ξ i) (rowStar (r i) k x) := by
  have hS : ∀ u v : Star d, inner ℝ u v = ∑ s, inner ℝ (u s) (v s) := fun u v => PiLp.inner_apply u v
  have hP : ∀ u v : PairedMomentum d n, inner ℝ u v = ∑ ij, inner ℝ (u ij) (v ij) :=
    fun u v => PiLp.inner_apply u v
  rw [hP]
  simp_rw [hS]
  simp only [starProductFrequency, starRootFrequency, rowStar, rowLinear, PiLp.toLp_apply, sum_inner,
    inner_add_right, inner_sum, real_inner_smul_left, real_inner_smul_right, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

theorem starProduct_at_value (M : (i : ι) → SpatialMeasure (Star d) (α i))
    (hM : ∀ i, Measurable (M i).amplitude) (r : ι → Fin 4 → (Fin n × Fin 2) → ℤ)
    (k : Mom d) (x : PairedMomentum d n) :
    ((starProduct M hM r).at k).value x = ∏ i, (M i).value (rowStar (r i) k x) := by
  rw [RootMeasure.at_value]
  have he (θ : (i : ι) → α i) :
      (starProduct M hM r).base.amplitude θ * rootChar ((starProduct M hM r).root θ) k *
        (Real.fourierChar (inner ℝ ((starProduct M hM r).base.frequency θ) x) : ℂ) =
      ∏ i, ((M i).amplitude (θ i) *
        (Real.fourierChar (inner ℝ ((M i).frequency (θ i)) (rowStar (r i) k x)) : ℂ)) := by
    have hp := starProduct_phase r (fun i => (M i).frequency (θ i)) k x
    have h1 : (starProduct M hM r).base.amplitude θ = ∏ i, (M i).amplitude (θ i) := rfl
    have h2 : (starProduct M hM r).root θ = ∑ i, starRootFrequency ((M i).frequency (θ i)) := rfl
    have h3 : (starProduct M hM r).base.frequency θ =
        starProductFrequency r (fun i => (M i).frequency (θ i)) := rfl
    rw [h1, h2, h3, rootChar, mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, hp,
      fourierChar_sum_coe, ← Finset.prod_mul_distrib]
  simp_rw [he]
  exact integral_fintype_prod_eq_prod (μ := fun i => (M i).μ) (fun i a =>
    (M i).amplitude a * (Real.fourierChar (inner ℝ ((M i).frequency a) (rowStar (r i) k x)) : ℂ))

theorem measurable_starDensity (J : ℕ) {β : Type*} [MeasurableSpace β]
    (M : SpatialMeasure (Star d) β) (hM : Measurable M.amplitude) :
    Measurable (fun a => (1 + ‖starRootFrequency (M.frequency a)‖) ^ J * ‖M.amplitude a‖) := by
  refine ((measurable_const.add ?_).pow_const J).mul hM.norm
  unfold starRootFrequency
  exact (Finset.measurable_sum _ fun s _ =>
    (PiLp.continuous_apply 2 _ s).measurable.comp M.frequency_measurable).norm

theorem starMoment_eq (J : ℕ) {β : Type*} [MeasurableSpace β] (M : SpatialMeasure (Star d) β) :
    starMoment J M =
      ∫⁻ a, ENNReal.ofReal ((1 + ‖starRootFrequency (M.frequency a)‖) ^ J * ‖M.amplitude a‖) ∂M.μ := by
  unfold starMoment
  congr 1
  funext a
  rw [ENNReal.ofReal_mul (by positivity), ofReal_norm]

/-- The product moment is at most the product of the factor moments. -/
theorem starProduct_momentMass_le (M : (i : ι) → SpatialMeasure (Star d) (α i))
    (hM : ∀ i, Measurable (M i).amplitude) (r : ι → Fin 4 → (Fin n × Fin 2) → ℤ) (J : ℕ)
    (hfin : ∀ i, starMoment J (M i) < ⊤) :
    (starProduct M hM r).momentMass J ≤ ∏ i, starMoment J (M i) := by
  let f := fun i (a : α i) => (1 + ‖starRootFrequency ((M i).frequency a)‖) ^ J * ‖(M i).amplitude a‖
  have hf0 (i : ι) (a : α i) : 0 ≤ f i a := by positivity
  have hfi (i : ι) : Integrable (f i) (M i).μ := by
    refine ⟨(measurable_starDensity J (M i) (hM i)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun a => hf0 i a), ← starMoment_eq]
    exact hfin i
  have hint : Integrable (fun θ : (i : ι) → α i => ∏ i, f i (θ i)) (Measure.pi fun i => (M i).μ) :=
    Integrable.fintype_prod_dep hfi
  calc
    (starProduct M hM r).momentMass J ≤ ∫⁻ θ, ENNReal.ofReal (∏ i, f i (θ i))
        ∂(Measure.pi fun i => (M i).μ) := by
      rw [RootMeasure.momentMass_eq]
      refine lintegral_mono fun θ => ENNReal.ofReal_le_ofReal ?_
      have h1 : (starProduct M hM r).base.amplitude θ = ∏ i, (M i).amplitude (θ i) := rfl
      have h2 : (starProduct M hM r).root θ = ∑ i, starRootFrequency ((M i).frequency (θ i)) := rfl
      rw [h1, h2, norm_prod]
      have hprod : (∏ i, f i (θ i)) = (∏ i, (1 + ‖starRootFrequency ((M i).frequency (θ i))‖)) ^ J *
          ∏ i, ‖(M i).amplitude (θ i)‖ := by
        simp only [f]
        rw [Finset.prod_mul_distrib, Finset.prod_pow]
      rw [hprod]
      refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun i _ => norm_nonneg _)
      exact pow_le_pow_left₀ (by positivity)
        (one_add_norm_sum_le_prod _ (fun i => starRootFrequency ((M i).frequency (θ i)))) J
    _ = ENNReal.ofReal (∫ θ, ∏ i, f i (θ i) ∂(Measure.pi fun i => (M i).μ)) :=
      (ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun θ => Finset.prod_nonneg fun i _ => hf0 i (θ i))).symm
    _ = ENNReal.ofReal (∏ i, ∫ a, f i a ∂(M i).μ) := by
      rw [integral_fintype_prod_eq_prod (μ := fun i => (M i).μ) f]
    _ = ∏ i, ENNReal.ofReal (∫ a, f i a ∂(M i).μ) :=
      ENNReal.ofReal_prod_of_nonneg fun i _ => integral_nonneg (hf0 i)
    _ = ∏ i, starMoment J (M i) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [starMoment_eq, ofReal_integral_eq_lintegral_ofReal (hfi i)
        (Filter.Eventually.of_forall fun a => hf0 i a)]

/-- Measurable density representative of a star presentation: same value, same moment. -/
theorem starValue_measurableDensity {β : Type*} [MeasurableSpace β] (M : SpatialMeasure (Star d) β)
    (y : Star d) : (measurableDensity M).value y = M.value y := by
  apply integral_congr_ae
  filter_upwards [M.amplitude_integrable.aestronglyMeasurable.ae_eq_mk] with a ha
  exact congrArg (fun c : ℂ => c * (Real.fourierChar (inner ℝ (M.frequency a) y) : ℂ)) ha.symm

theorem starMoment_measurableDensity (J : ℕ) {β : Type*} [MeasurableSpace β]
    (M : SpatialMeasure (Star d) β) : starMoment J (measurableDensity M) = starMoment J M := by
  unfold starMoment
  apply lintegral_congr_ae
  filter_upwards [M.amplitude_integrable.aestronglyMeasurable.ae_eq_mk] with a ha
  change ENNReal.ofReal _ * ‖M.amplitude_integrable.aestronglyMeasurable.mk M.amplitude a‖ₑ =
    ENNReal.ofReal _ * ‖M.amplitude a‖ₑ
  rw [← ha]
  rfl

end WaveTurbulence.Flower.IncTop