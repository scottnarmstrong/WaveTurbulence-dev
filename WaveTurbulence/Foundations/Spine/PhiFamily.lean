/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.ElemIneq
public import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic
/-! The family `Φ_A(α) = ∫_Ω ∏_{v∈A} iπ(t_v - L_v) ∏_v e^{iπα_v t_v}` and its derivative identity
`∂_{α_b} Φ_A = Φ_{A∪b} + iπ L_b Φ_A` (TARGET L2007–L2008: the derivatives `∂_{α_v} - πi 𝔏_v` become
factors `πi(t_v - 𝔏_v)`). -/
@[expose] public section
open MeasureTheory Set Finset Function Metric
namespace WaveTurbulence.Ladder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Integrand of `Φ_A`. -/
noncomputable def famInt (L : ι → ℝ) (A : Finset ι) (α t : ι → ℝ) : ℂ :=
  (∏ v ∈ A, (((Real.pi * (t v - L v) : ℝ) : ℂ) * Complex.I)) *
    ∏ v, Complex.exp (((Real.pi * α v * t v : ℝ) : ℂ) * Complex.I)

/-- `Φ_A` over the time domain `Ω`. -/
noncomputable def Phi (Ω : Set (ι → ℝ)) (L : ι → ℝ) (A : Finset ι) (α : ι → ℝ) : ℂ :=
  ∫ t, Ω.indicator (famInt L A α) t

theorem continuous_famInt (L : ι → ℝ) (A : Finset ι) (t : ι → ℝ) :
    Continuous fun α => famInt L A α t := by
  unfold famInt; fun_prop

theorem norm_famInt_le (L : ι → ℝ) (A : Finset ι) (α t : ι → ℝ) :
    ‖famInt L A α t‖ ≤ ∏ v ∈ A, (Real.pi * |t v - L v|) := by
  unfold famInt
  rw [norm_mul, norm_prod, norm_prod]
  have h1 : ∀ v, ‖Complex.exp (((Real.pi * α v * t v : ℝ) : ℂ) * Complex.I)‖ = 1 :=
    fun v => Complex.norm_exp_ofReal_mul_I _
  simp only [h1, Finset.prod_const_one, mul_one]
  refine le_of_eq (Finset.prod_congr rfl (fun v _ => ?_))
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_of_pos Real.pi_pos]

variable (Ω : Set (ι → ℝ)) (hΩm : MeasurableSet Ω) (T : ℝ)
  (hΩb : ∀ t ∈ Ω, ∀ v, |t v| ≤ T)

include hΩm hΩb in
theorem volume_Ω_lt_top : volume Ω < ⊤ := by
  have hc : IsCompact (Set.pi univ (fun _ : ι => Icc (-T) T)) := isCompact_univ_pi (fun _ => isCompact_Icc)
  refine lt_of_le_of_lt (measure_mono (show Ω ⊆ Set.pi univ (fun _ : ι => Icc (-T) T) from fun t ht v _ => abs_le.mp (hΩb t ht v))) hc.measure_lt_top

include hΩm hΩb in
theorem integrable_indicator_famInt (L : ι → ℝ) (A : Finset ι) (α : ι → ℝ) :
    Integrable (Ω.indicator (famInt L A α)) := by
  set C : ℝ := ∏ v ∈ A, (Real.pi * (T + |L v|)) with hC
  have hb : Integrable (Ω.indicator (fun _ => C)) :=
    (integrable_indicator_iff hΩm).mpr (integrableOn_const (volume_Ω_lt_top Ω hΩm T hΩb).ne)
  refine hb.mono' ?_ (Filter.Eventually.of_forall (fun t => ?_))
  · refine (Measurable.indicator ?_ hΩm).aestronglyMeasurable
    unfold famInt; fun_prop
  · by_cases ht : t ∈ Ω
    · simp only [Set.indicator_of_mem ht]
      refine (norm_famInt_le L A α t).trans ?_
      refine Finset.prod_le_prod₀ (fun v _ => by positivity) (fun v _ => ?_)
      have := hΩb t ht v
      gcongr
      calc |t v - L v| ≤ |t v| + |L v| := abs_sub _ _
        _ ≤ T + |L v| := by linarith
    · simp [Set.indicator_of_notMem ht]

include hΩm hΩb in
theorem continuous_Phi (L : ι → ℝ) (A : Finset ι) : Continuous (Phi Ω L A) := by
  unfold Phi
  set C : ℝ := ∏ v ∈ A, (Real.pi * (T + |L v|)) with hC
  have hb : Integrable (Ω.indicator (fun _ => C)) :=
    (integrable_indicator_iff hΩm).mpr (integrableOn_const (volume_Ω_lt_top Ω hΩm T hΩb).ne)
  refine continuous_of_dominated (bound := Ω.indicator (fun _ => C)) ?_ ?_ hb ?_
  · intro α
    exact (integrable_indicator_famInt Ω hΩm T hΩb L A α).aestronglyMeasurable
  · intro α
    refine Filter.Eventually.of_forall (fun t => ?_)
    by_cases ht : t ∈ Ω
    · simp only [Set.indicator_of_mem ht]
      refine (norm_famInt_le L A α t).trans ?_
      refine Finset.prod_le_prod₀ (fun v _ => by positivity) (fun v _ => ?_)
      have := hΩb t ht v
      gcongr
      calc |t v - L v| ≤ |t v| + |L v| := abs_sub _ _
        _ ≤ T + |L v| := by linarith
    · simp [Set.indicator_of_notMem ht]
  · refine Filter.Eventually.of_forall (fun t => ?_)
    by_cases ht : t ∈ Ω
    · simp only [Set.indicator_of_mem ht]; exact continuous_famInt L A t
    · simp only [Set.indicator_of_notMem ht]; exact continuous_const


theorem hasDerivAt_exp_prod (α t : ι → ℝ) (b : ι) (r : ℝ) :
    HasDerivAt (fun r : ℝ => ∏ v, Complex.exp (((Real.pi * (update α b r) v * t v : ℝ) : ℂ) * Complex.I))
      ((((Real.pi * t b : ℝ) : ℂ) * Complex.I) *
        ∏ v, Complex.exp (((Real.pi * (update α b r) v * t v : ℝ) : ℂ) * Complex.I)) r := by
  have hsplit : ∀ r' : ℝ, ∏ v, Complex.exp (((Real.pi * (update α b r') v * t v : ℝ) : ℂ) * Complex.I) =
      (∏ v ∈ univ.erase b, Complex.exp (((Real.pi * α v * t v : ℝ) : ℂ) * Complex.I)) *
        Complex.exp (((Real.pi * r' * t b : ℝ) : ℂ) * Complex.I) := by
    intro r'
    rw [← Finset.prod_erase_mul univ _ (Finset.mem_univ b)]
    congr 1
    · refine Finset.prod_congr rfl (fun v hv => ?_)
      rw [update_of_ne (Finset.ne_of_mem_erase hv)]
    · rw [update_self]
  have h0 : HasDerivAt (fun r' : ℝ => Real.pi * r' * t b) (Real.pi * t b) r := by
    have := HasDerivAt.mul_const (HasDerivAt.const_mul Real.pi (hasDerivAt_id r)) (t b)
    simpa using this
  have h1 := HasDerivAt.cexp (HasDerivAt.mul_const (HasDerivAt.ofReal_comp h0) Complex.I)
  have h2 := HasDerivAt.const_mul (∏ v ∈ univ.erase b, Complex.exp (((Real.pi * α v * t v : ℝ) : ℂ) * Complex.I)) h1
  simp_rw [hsplit]
  convert h2 using 1
  ring

include hΩm hΩb in
theorem hasDerivAt_Phi (L : ι → ℝ) (A : Finset ι) (b : ι) (hb : b ∉ A) (α : ι → ℝ) :
    HasDerivAt (fun r => Phi Ω L A (update α b r))
      (Phi Ω L (insert b A) α + ((Real.pi * L b : ℝ) : ℂ) * Complex.I * Phi Ω L A α) (α b) := by
  set F' : ℝ → (ι → ℝ) → ℂ := fun r t => Ω.indicator (fun t =>
      (∏ v ∈ A, (((Real.pi * (t v - L v) : ℝ) : ℂ) * Complex.I)) *
        ((((Real.pi * t b : ℝ) : ℂ) * Complex.I) *
          ∏ v, Complex.exp (((Real.pi * (update α b r) v * t v : ℝ) : ℂ) * Complex.I))) t with hF'
  set C : ℝ := (∏ v ∈ A, (Real.pi * (T + |L v|))) * (Real.pi * T) with hC
  have hbd : Integrable (Ω.indicator (fun _ => C)) :=
    (integrable_indicator_iff hΩm).mpr (integrableOn_const (volume_Ω_lt_top Ω hΩm T hΩb).ne)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := α b)
    (F := fun r t => Ω.indicator (famInt L A (update α b r)) t) (F' := F')
    (bound := Ω.indicator (fun _ => C)) (s := univ) Filter.univ_mem
    (Filter.Eventually.of_forall (fun r =>
      (integrable_indicator_famInt Ω hΩm T hΩb L A _).aestronglyMeasurable))
    (integrable_indicator_famInt Ω hΩm T hΩb L A _)
    (by
      refine (Measurable.indicator ?_ hΩm).aestronglyMeasurable
      fun_prop)
    (Filter.Eventually.of_forall (fun t r _ => by
      by_cases ht : t ∈ Ω
      · simp only [hF', Set.indicator_of_mem ht]
        have h1 : ∀ v, ‖Complex.exp (((Real.pi * (update α b r) v * t v : ℝ) : ℂ) * Complex.I)‖ = 1 :=
          fun v => Complex.norm_exp_ofReal_mul_I _
        have hn : ∀ x : ℝ, ‖((x : ℝ) : ℂ) * Complex.I‖ = |x| := by
          intro x; rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        have e1 : ‖(∏ v ∈ A, (((Real.pi * (t v - L v) : ℝ) : ℂ) * Complex.I)) *
            ((((Real.pi * t b : ℝ) : ℂ) * Complex.I) *
              ∏ v, Complex.exp (((Real.pi * (update α b r) v * t v : ℝ) : ℂ) * Complex.I))‖ =
            (∏ v ∈ A, |Real.pi * (t v - L v)|) * |Real.pi * t b| := by
          rw [norm_mul, norm_mul, norm_prod, norm_prod, hn]
          simp only [hn, h1, Finset.prod_const_one, mul_one]
        rw [e1, hC]
        have hb1 : ∏ v ∈ A, (|Real.pi * (t v - L v)|) ≤ ∏ v ∈ A, (Real.pi * (T + |L v|)) := by
          refine Finset.prod_le_prod₀ (fun v _ => abs_nonneg _) (fun v _ => ?_)
          rw [abs_mul, abs_of_pos Real.pi_pos]
          have := hΩb t ht v
          gcongr
          calc |t v - L v| ≤ |t v| + |L v| := abs_sub _ _
            _ ≤ T + |L v| := by linarith
        have hb2 : |Real.pi * t b| ≤ Real.pi * T := by
          rw [abs_mul, abs_of_pos Real.pi_pos]; gcongr; exact hΩb t ht b
        have hT : 0 ≤ T := (abs_nonneg _).trans (hΩb t ht b)
        exact mul_le_mul hb1 hb2 (abs_nonneg _) (Finset.prod_nonneg (fun v _ => mul_nonneg Real.pi_pos.le (by linarith [abs_nonneg (L v)])))
      · simp [hF', Set.indicator_of_notMem ht])) hbd
    (Filter.Eventually.of_forall (fun t r _ => by
      by_cases ht : t ∈ Ω
      · simp only [hF', Set.indicator_of_mem ht, famInt]
        have := HasDerivAt.const_mul (∏ v ∈ A, (((Real.pi * (t v - L v) : ℝ) : ℂ) * Complex.I))
          (hasDerivAt_exp_prod α t b r)
        convert this using 1
      · simp only [hF', Set.indicator_of_notMem ht]; exact hasDerivAt_const _ _))
  have hF'a : ∀ t, F' (α b) t = Ω.indicator (famInt L (insert b A) α) t +
      ((Real.pi * L b : ℝ) : ℂ) * Complex.I * Ω.indicator (famInt L A α) t := by
    intro t
    by_cases ht : t ∈ Ω
    · simp only [hF', Set.indicator_of_mem ht, famInt, update_eq_self, Finset.prod_insert hb]
      push_cast; ring
    · simp [hF', Set.indicator_of_notMem ht]
  have hint := hmain.2
  have e1 : (fun r => ∫ t, Ω.indicator (famInt L A (update α b r)) t) =
      fun r => Phi Ω L A (update α b r) := rfl
  rw [e1] at hint
  convert hint using 1
  simp_rw [hF'a]
  unfold Phi
  rw [integral_add (integrable_indicator_famInt Ω hΩm T hΩb L _ α)
    ((integrable_indicator_famInt Ω hΩm T hΩb L A α).const_mul _), integral_const_mul]

end WaveTurbulence.Ladder
