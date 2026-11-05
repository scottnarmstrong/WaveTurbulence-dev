/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.MainGlue.SealInputs
public import WaveTurbulence.Foundations.Probability.RandomRapidDecay
/-! Integrable mass and event comparison for the conditional Theorem 1.1 assembly. -/
public section
namespace WaveTurbulence.MainGlue
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- A countable nonnegative series with summable integrals is integrable, including the
usual zero value of the real tsum on the exceptional divergent locus. -/
theorem integrable_nonneg_series {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    {μ : Measure Ω} (f : ι → Ω → ℝ) (hf : ∀ i, Integrable (f i) μ)
    (h0 : ∀ i ω, 0 ≤ f i ω) (hs : Summable (fun i => ∫ ω, f i ω ∂μ)) :
    Integrable (fun ω => ∑' i, f i ω) μ := by
  let F := fun ω => ∑' i, ENNReal.ofReal (f i ω)
  have hm : AEMeasurable F μ :=
    AEMeasurable.tsum (fun i => (hf i).aemeasurable.ennreal_ofReal)
  have hi : (∫⁻ ω, F ω ∂μ) ≠ ⊤ := by
    dsimp only [F]
    rw [lintegral_tsum (fun i => (hf i).aemeasurable.ennreal_ofReal)]
    simp_rw [← ofReal_integral_eq_lintegral_ofReal (hf _) (ae_of_all _ (h0 _))]
    exact hs.tsum_ofReal_ne_top
  have he : (fun ω => F ω |>.toReal) = (fun ω => ∑' i, f i ω) := by
    funext ω
    change (∑' i, ENNReal.ofReal (f i ω)).toReal = _
    rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    simp only [ENNReal.toReal_ofReal (h0 _ _)]
  rw [← he]
  exact integrable_toReal_of_lintegral_ne_top hm hi

/-- Integrability of the exact frozen initial-mass expression. -/
theorem integrable_initial_mass {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {L : ℝ} (hL : 0 < L)
    (φ : SchwartzMap (Mom d) ℝ) (hφ : ∀ k, 0 ≤ φ k)
    (g : (Fin d → ℤ) → Ω → ℂ) (hg : ∀ n, HasLaw (g n) stdComplexGaussian μ) :
    Integrable (fun ω => ∑' n, φ (latticePoint L n) * ‖g n ω‖ ^ 2) μ := by
  apply integrable_nonneg_series _ (fun n =>
    (Probability.integrable_norm_pow_of_hasLaw (hg n) 2).const_mul _)
    (fun _ _ => mul_nonneg (hφ _) (sq_nonneg _))
  have he (n : Fin d → ℤ) : (∫ ω, φ (latticePoint L n) * ‖g n ω‖ ^ 2 ∂μ) =
      φ (latticePoint L n) := by
    rw [integral_const_mul]
    have hn := Probability.integral_norm_even_of_hasLaw (hg n) 1
    norm_num at hn
    rw [hn, mul_one]
  simp_rw [he]
  exact summable_schwartz_lattice φ hL

/-- Two nonnegative observables bounded by one integrable mass differ only off their
agreement event. This is a genuine integral estimate, with integrability proved at the call site. -/
theorem integral_sub_le_mass_compl {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g M : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) (hM : Integrable M μ)
    {A : Set Ω} (hA : MeasurableSet A)
    (hb : ∀ ω, 0 ≤ f ω ∧ f ω ≤ M ω ∧ 0 ≤ g ω ∧ g ω ≤ M ω)
    (he : ∀ᵐ ω ∂μ, ω ∈ A → f ω = g ω) :
    |(∫ ω, f ω ∂μ) - ∫ ω, g ω ∂μ| ≤ ∫ ω in Aᶜ, M ω ∂μ := by
  calc
    _ = ‖∫ ω, f ω - g ω ∂μ‖ := by rw [integral_sub hf hg, Real.norm_eq_abs]
    _ ≤ ∫ ω, ‖f ω - g ω‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, Aᶜ.indicator M ω ∂μ := by
      apply integral_mono_ae (hf.sub hg).norm (hM.indicator hA.compl)
      filter_upwards [he] with ω hω
      dsimp only [Pi.sub_apply]
      by_cases ha : ω ∈ A
      · rw [hω ha, sub_self, norm_zero, indicator_of_notMem (show ω ∉ Aᶜ from not_not.mpr ha)]
      · rw [indicator_of_mem (show ω ∈ Aᶜ from ha), Real.norm_eq_abs]
        obtain ⟨hf0, hfM, hg0, hgM⟩ := hb ω
        exact abs_le.mpr ⟨by linarith only [hf0, hgM], by linarith only [hg0, hfM]⟩
    _ = _ := integral_indicator hA.compl

/-- Every rescaled time in [0,D] lies in one of the ansatz intervals [p-1,p], 1≤p≤D. -/
theorem exists_ansatz_step {D : ℕ} (hD : 1 ≤ D) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) D) :
    ∃ p : ℕ, 1 ≤ p ∧ p ≤ D ∧ s ∈ Icc ((p : ℝ) - 1) p := by
  refine ⟨max 1 ⌈s⌉₊, le_max_left _ _, max_le hD (Nat.ceil_le.mpr hs.2), ?_⟩
  by_cases hc : ⌈s⌉₊ ≤ 1
  · rw [max_eq_left hc]
    norm_num only [Nat.cast_one, sub_self, mem_Icc]
    exact ⟨hs.1, (Nat.le_ceil s).trans (by exact_mod_cast hc)⟩
  · rw [max_eq_right (by omega : 1 ≤ ⌈s⌉₊)]
    exact ⟨by linarith only [Nat.ceil_lt_add_one hs.1], Nat.le_ceil s⟩

end WaveTurbulence.MainGlue
