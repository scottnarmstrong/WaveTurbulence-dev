/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Regref.Trace00
public import WaveTurbulence.Foundations.Regref.ParamDerivFin
public import WaveTurbulence.Foundations.Fourier.MixedNorm

/-!
# Traces in the `𝔛^{θ,Λ,0}` norm with momentum derivatives (GAP.regrefNorm, the `q' < r` case)

The landed TARGET (normX) norm `Fourier.mixedFourierNorm θ Λ 0` (with the almost-everywhere smoothness guard of
WAVE-B §2.6). For an arbitrary extension `G` of finite norm, the cutoff trace of its continuous representatives,
`G'(t, k) = χ^{⊗r}(t) · (rep G(·, k))(t[j ↦ c])`, has

`‖G'‖_{𝔛^{θ,Λ,0}} ≤ 2^θ ‖χ^{⊗r}‖_{𝔛^θ} ‖G‖_{𝔛^{θ,Λ,0}}` (`mixedFourierNorm_cutoffTimeTrace_rep_le`, `Λ ≥ 1`).

Proof: the Fourier transform of `G'` is the frequency mixture `∫ Ĝ(ξ, k) m_λ(ξ) dξ` (Incoh's synthesis formula);
replacing `Ĝ` by its restriction `Φ` to a measurable full-measure set of `ξ` where `Ĝ(ξ, ·) ∈ C^Λ`, the momentum
derivatives pass under the `ξ`-integral (`ParamDerivFin`), dominated by the coordinate-word envelopes of `Ĝ`; each
derivative is then itself a mixture, bounded by the landed `Incoh.mixedFourierNorm00_integral_dominated_le`.
The restriction form is `mixedRestrictionNorm_trace_le`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace WaveTurbulence.Regref

open WaveTurbulence.Fourier WaveTurbulence.Incoh

variable {r d : ℕ}

theorem momentumSupNorm_zero_eq (f : Mom d → ℂ) : momentumSupNorm 0 f = ⨆ k, ‖f k‖ₑ := by
  unfold momentumSupNorm
  simp only [pow_zero, ENNReal.ofReal_one, one_mul]

theorem momentumDerivative_apply {n : ℕ} (ρ : Fin n → Fin d) (f : Mom d → ℂ) (k : Mom d) :
    momentumDerivative ρ f k = iteratedFDeriv ℝ n f k (fun i => EuclideanSpace.single (ρ i) 1) := rfl

theorem momentumDerivative_zero_fun {n : ℕ} (ρ : Fin n → Fin d) :
    momentumDerivative ρ (fun _ : Mom d => (0 : ℂ)) = fun _ => 0 := by
  funext k
  rw [momentumDerivative_apply]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  · rw [iteratedFDeriv_const_of_ne hn.ne']
    rfl

theorem continuous_momentumDerivative {N n : ℕ} (hn : n ≤ N) (ρ : Fin n → Fin d) {f : Mom d → ℂ}
    (hf : ContDiff ℝ N f) : Continuous (momentumDerivative ρ f) := by
  have hc := hf.continuous_iteratedFDeriv (m := n) (by exact_mod_cast hn)
  exact (continuous_eval_const (fun i => EuclideanSpace.single (ρ i) (1 : ℝ))).comp hc

/-- The supremum of a continuous `ℝ≥0∞`-valued function is attained on a dense set. -/
theorem iSup_eq_iSup_dense {X : Type*} [TopologicalSpace X] {D : Set X} (hD : Dense D)
    {g : X → ℝ≥0∞} (hg : Continuous g) : (⨆ x, g x) = ⨆ x : D, g x := by
  refine le_antisymm (iSup_le fun x => ?_) (iSup_le fun x => le_iSup g x.1)
  have hcl : IsClosed {y | g y ≤ ⨆ x : D, g x} := isClosed_le hg continuous_const
  have hsub : D ⊆ {y | g y ≤ ⨆ x : D, g x} := fun y hy => le_iSup (fun x : D => g x) ⟨y, hy⟩
  have := hcl.closure_subset_iff.2 hsub
  rw [hD.closure_eq] at this
  exact this (mem_univ x)

section Envelope

variable {Λ : ℕ} {Φ : (Fin r → ℝ) → Mom d → ℂ}

/-- The coordinate-word envelope `ξ ↦ sup_k |∂^w Φ(ξ, k)|` of a family `C^Λ` in `k` and measurable in `ξ` is
measurable. -/
theorem measurable_wordEnvelope (hs : ∀ ξ, ContDiff ℝ Λ (Φ ξ)) (hm : ∀ k, StronglyMeasurable fun ξ => Φ ξ k)
    {n : ℕ} (hn : n ≤ Λ) (ρ : Fin n → Fin d) :
    Measurable fun ξ => ⨆ k, ‖momentumDerivative ρ (Φ ξ) k‖ₑ := by
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense (Mom d)
  have : Countable D := hDc.to_subtype
  have he : (fun ξ => ⨆ k, ‖momentumDerivative ρ (Φ ξ) k‖ₑ) =
      fun ξ => ⨆ q : D, ‖momentumDerivative ρ (Φ ξ) q.1‖ₑ := by
    funext ξ
    exact iSup_eq_iSup_dense hD (continuous_enorm.comp (continuous_momentumDerivative hn ρ (hs ξ)))
  rw [he]
  refine Measurable.iSup fun q => ?_
  have hsm := stronglyMeasurable_iteratedFDeriv_param_of_le (f := fun k ξ => Φ ξ k) hs hm n hn q.1
  exact (((continuous_eval_const (fun i => EuclideanSpace.single (ρ i) (1 : ℝ))).comp_stronglyMeasurable
    hsm).measurable).enorm

end Envelope

/-! ### The main trace estimate -/

section Main

variable {Λ : ℕ} {θ : ℝ} {χ : ℝ → ℝ}

theorem mixedFourierAdmissible_of_lt_top {Λ₂ : ℕ} {G : (Fin r → ℝ) → Mom d → ℂ}
    (hG : mixedFourierNorm θ Λ Λ₂ G < ⊤) : MixedFourierAdmissible Λ G := by
  by_contra h
  rw [mixedFourierNorm_of_not_admissible h] at hG
  exact lt_irrefl _ hG

theorem mixedFourierNorm_eq_iSup {Λ₂ : ℕ} {G : (Fin r → ℝ) → Mom d → ℂ}
    (h : MixedFourierAdmissible Λ G) : mixedFourierNorm θ Λ Λ₂ G =
      ⨆ (n : ℕ) (_ : n ≤ Λ) (ρ : Fin n → Fin d),
        ∫⁻ ξ, timeWeight θ ξ * momentumSupNorm Λ₂ (momentumDerivative ρ (mixedTimeFourier G ξ)) := by
  unfold mixedFourierNorm
  rw [ite_eq_left h]

theorem one_le_timeWeight (hθ : 0 ≤ θ) (ξ : Fin r → ℝ) : 1 ≤ timeWeight θ ξ := by
  simpa only [timeWeight, ENNReal.ofReal_one] using
    ENNReal.ofReal_le_ofReal (Real.one_le_rpow (one_le_timeBracket ξ) hθ)

/-- The synthesis multiplier `m_λ(ξ) = e(cξ_j) · (χ^{⊗r} e_{ξ'})^∧(λ)`. -/
noncomputable def synthMult (χ : ℝ → ℝ) (j : Fin r) (c : ℝ) (lam ξ : Fin r → ℝ) : ℂ :=
  (Real.fourierChar (c * ξ j) : ℂ) * timeFourier (fun t => frozenModulation χ j t ξ) lam

theorem norm_synthMult_le (j : Fin r) (c : ℝ) (lam ξ : Fin r → ℝ) :
    ‖synthMult χ j c lam ξ‖ ≤ ∫ t : Fin r → ℝ, ‖coordinateCutoff χ t‖ := by
  unfold synthMult
  rw [norm_mul, Circle.norm_coe, one_mul]
  unfold timeFourier VectorFourier.fourierIntegral
  refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae (ae_of_all _ fun t => ?_)))
  beta_reduce
  rw [Circle.norm_smul, norm_frozenModulation]

theorem stronglyMeasurable_synthMult (hχ : ContDiff ℝ ∞ χ) (j : Fin r) (c : ℝ) (lam : Fin r → ℝ) :
    StronglyMeasurable (synthMult χ j c lam) := by
  have hcoe : Continuous (fun z : Circle => (z : ℂ)) := continuous_subtype_val
  have hp : Continuous (fun ξ : Fin r → ℝ => (Real.fourierChar (c * ξ j) : ℂ)) :=
    hcoe.comp (Real.continuous_fourierChar.comp (by fun_prop))
  have hft := stronglyMeasurable_timeFourier_family (K := fun t ξ => frozenModulation χ j t ξ)
    (stronglyMeasurable_frozenModulation hχ j)
  have hsec : StronglyMeasurable fun ξ : Fin r → ℝ =>
      timeFourier (fun t => frozenModulation χ j t ξ) lam := by
    have hg : Measurable fun ξ : Fin r → ℝ => (lam, ξ) := measurable_const.prodMk measurable_id
    have h3 := hft.comp_measurable hg
    simp only [Function.comp_def] at h3
    exact h3
  exact hp.stronglyMeasurable.mul hsec

/-- **The trace estimate with momentum derivatives** (`Λ ≥ 1`). -/
theorem mixedFourierNorm_cutoffTimeTrace_rep_le (hΛ : Λ ≠ 0) (hθ : 0 ≤ θ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    {G : (Fin r → ℝ) → Mom d → ℂ} (hG : mixedFourierNorm θ Λ 0 G < ⊤) (j : Fin r) (c : ℝ) :
    mixedFourierNorm θ Λ 0 (fun t k => cutoffTimeTrace χ j c (rep fun u => G u k) t) ≤
      traceConst (r := r) θ χ * mixedFourierNorm θ Λ 0 G := by
  classical
  set M := mixedFourierNorm θ Λ 0 G with hMdef
  have hadm := mixedFourierAdmissible_of_lt_top hG
  have hiG : ∀ k, Integrable (fun t => G t k) := hadm.1
  have hsm : ∀ᵐ ξ, ContDiff ℝ Λ (mixedTimeFourier G ξ) := hadm.2.resolve_left hΛ
  rw [mixedFourierNorm_eq_iSup hadm] at hMdef
  have hword : ∀ (n : ℕ) (_ : n ≤ Λ) (ρ : Fin n → Fin d),
      ∫⁻ ξ, timeWeight θ ξ * momentumSupNorm 0 (momentumDerivative ρ (mixedTimeFourier G ξ)) ≤ M :=
    fun n hn ρ => hMdef ▸ le_iSup₂_of_le n hn (le_iSup (fun ρ : Fin n → Fin d =>
      ∫⁻ ξ, timeWeight θ ξ * momentumSupNorm 0 (momentumDerivative ρ (mixedTimeFourier G ξ))) ρ)
  -- the slices have finite scalar norms
  have hslice : ∀ k, timeFourierNorm θ (fun t => G t k) < ⊤ := by
    intro k
    refine lt_of_le_of_lt ?_ hG
    rw [timeFourierNorm_eq_lintegral (hiG k)]
    refine le_trans ?_ (hword 0 (Nat.zero_le _) Fin.elim0)
    refine lintegral_mono fun ξ => mul_le_mul' le_rfl ?_
    rw [momentumDerivative_zero, momentumSupNorm_zero_eq]
    exact le_iSup (fun k => ‖mixedTimeFourier G ξ k‖ₑ) k
  have hR := fun k => rep_props hθ (hslice k)
  -- the good set
  obtain ⟨N, hNsup, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hsm)
  set S := Nᶜ with hS
  have hSm : MeasurableSet S := hNm.compl
  have haeS : ∀ᵐ ξ ∂(volume : Measure (Fin r → ℝ)), ξ ∈ S :=
    measure_mono_null (fun ξ hξ => by simpa [hS] using hξ) hN0
  have hSsm : ∀ ξ ∈ S, ContDiff ℝ Λ (mixedTimeFourier G ξ) := fun ξ hξ => by
    by_contra h
    exact hξ (hNsup h)
  let Φ : (Fin r → ℝ) → Mom d → ℂ := fun ξ => if ξ ∈ S then mixedTimeFourier G ξ else fun _ => 0
  have hΦs : ∀ ξ, ContDiff ℝ Λ (Φ ξ) := fun ξ => by
    by_cases hξ : ξ ∈ S
    · simp only [Φ, hξ, ite_true]; exact hSsm ξ hξ
    · simp only [Φ, hξ, ite_false]; exact contDiff_const
  have hΦm : ∀ k, StronglyMeasurable fun ξ => Φ ξ k := fun k => by
    have : (fun ξ => Φ ξ k) = S.indicator (fun ξ => mixedTimeFourier G ξ k) := by
      funext ξ
      by_cases hξ : ξ ∈ S <;> simp [Φ, hξ]
    rw [this]
    exact ((timeFourier_continuous (hiG k)).stronglyMeasurable).indicator hSm
  have hΦae : ∀ k, (fun ξ => Φ ξ k) =ᵐ[volume] fun ξ => mixedTimeFourier G ξ k := fun k => by
    filter_upwards [haeS] with ξ hξ
    simp [Φ, hξ]
  -- envelopes
  let E : (n : ℕ) → (Fin n → Fin d) → (Fin r → ℝ) → ℝ≥0∞ :=
    fun n ρ ξ => ⨆ k, ‖momentumDerivative ρ (Φ ξ) k‖ₑ
  have hEm : ∀ n, n ≤ Λ → ∀ ρ : Fin n → Fin d, Measurable (E n ρ) :=
    fun n hn ρ => measurable_wordEnvelope hΦs hΦm hn ρ
  have hEle : ∀ n (ρ : Fin n → Fin d) ξ,
      E n ρ ξ ≤ momentumSupNorm 0 (momentumDerivative ρ (mixedTimeFourier G ξ)) := by
    intro n ρ ξ
    rw [momentumSupNorm_zero_eq]
    by_cases hξ : ξ ∈ S
    · simp only [E, Φ, hξ, ite_true, le_rfl]
    · simp only [E, Φ, hξ, ite_false, momentumDerivative_zero_fun, enorm_zero, iSup_const]
      exact zero_le
  have hEw : ∀ n, n ≤ Λ → ∀ ρ : Fin n → Fin d, ∫⁻ ξ, timeWeight θ ξ * E n ρ ξ ≤ M :=
    fun n hn ρ => (lintegral_mono fun ξ => mul_le_mul' le_rfl (hEle n ρ ξ)).trans (hword n hn ρ)
  have hE1 : ∀ n, n ≤ Λ → ∀ ρ : Fin n → Fin d, ∫⁻ ξ, E n ρ ξ ≠ ⊤ := by
    intro n hn ρ
    have h1 : ∫⁻ ξ, E n ρ ξ ≤ ∫⁻ ξ, timeWeight θ ξ * E n ρ ξ := by
      refine lintegral_mono fun ξ => ?_
      calc E n ρ ξ = 1 * E n ρ ξ := (one_mul _).symm
        _ ≤ timeWeight θ ξ * E n ρ ξ := mul_le_mul' (one_le_timeWeight hθ ξ) le_rfl
    exact ((h1.trans (hEw n hn ρ)).trans_lt hG).ne
  have hEfin : ∀ n, n ≤ Λ → ∀ ρ : Fin n → Fin d, ∀ᵐ ξ, E n ρ ξ < ⊤ := fun n hn ρ =>
    ae_lt_top (hEm n hn ρ) (hE1 n hn ρ)
  have hEint : ∀ n, n ≤ Λ → ∀ ρ : Fin n → Fin d, Integrable fun ξ => (E n ρ ξ).toReal := fun n hn ρ =>
    integrable_toReal_of_lintegral_ne_top (hEm n hn ρ).aemeasurable (hE1 n hn ρ)
  have hmD : ∀ n (ρ : Fin n → Fin d) ξ k, ‖momentumDerivative ρ (Φ ξ) k‖ₑ ≤ E n ρ ξ :=
    fun n ρ ξ k => le_iSup (fun k => ‖momentumDerivative ρ (Φ ξ) k‖ₑ) k
  -- constants
  set c₀ : ℝ := ∫ t : Fin r → ℝ, ‖coordinateCutoff χ t‖ with hc₀
  have hc₀0 : 0 ≤ c₀ := integral_nonneg fun _ => norm_nonneg _
  have hmb : ∀ lam ξ, ‖synthMult χ j c lam ξ‖ ≤ c₀ := norm_synthMult_le j c
  -- Step 1: the trace as a mixture of `Φ`
  have hK := stronglyMeasurable_frozenModulation hχ j
  have hB := integrable_norm_coordinateCutoff (r := r) hχ hcχ
  have hb := fun t ξ => (norm_frozenModulation χ j t ξ).le
  have hcoe : Continuous (fun z : Circle => (z : ℂ)) := continuous_subtype_val
  have hp : Continuous (fun ξ : Fin r → ℝ => (Real.fourierChar (c * ξ j) : ℂ)) :=
    hcoe.comp (Real.continuous_fourierChar.comp (by fun_prop))
  have hFhat : ∀ k, Integrable fun ξ => mixedTimeFourier G ξ k := fun k => by
    have := (hR k).2.2.2.2
    rwa [(hR k).2.2.2.1] at this
  let A : Mom d → (Fin r → ℝ) → ℂ := fun k ξ => (Real.fourierChar (c * ξ j) : ℂ) * Φ ξ k
  have hiA : ∀ k, Integrable (A k) := fun k =>
    ((hFhat k).congr (hΦae k).symm).bdd_mul hp.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => by simp only [Circle.norm_coe]; exact le_rfl))
  have hmA : ∀ k, StronglyMeasurable (A k) := fun k => hp.stronglyMeasurable.mul (hΦm k)
  have hj : ∀ k, Integrable (fun z : (Fin r → ℝ) × (Fin r → ℝ) => A k z.2 * frozenModulation χ j z.1 (id z.2))
      (volume.prod volume) := fun k =>
    integrable_joint_kernel_mixture volume hK hB hb (hiA k) (hmA k) measurable_id
  have hG' : ∀ t k, cutoffTimeTrace χ j c (rep fun u => G u k) t = ∫ ξ, A k ξ * frozenModulation χ j t ξ := by
    intro t k
    rw [cutoffTimeTrace_eq_fourier_mixture χ j c (hR k).2.2.1 (hR k).2.2.2.2 (hR k).1 t]
    refine integral_congr_ae ?_
    filter_upwards [hΦae k] with ξ hξ
    simp only [A, (hR k).2.2.2.1, hξ]
    rfl
  set G' : (Fin r → ℝ) → Mom d → ℂ := fun t k => cutoffTimeTrace χ j c (rep fun u => G u k) t with hG'def
  have hiG' : ∀ k, Integrable fun t => G' t k := fun k => by
    have := (hj k).integral_prod_left
    simpa only [hG'def, hG', id] using this
  -- Step 2: its Fourier transform
  have hFT : ∀ lam k, mixedTimeFourier G' lam k = ∫ ξ, synthMult χ j c lam ξ * Φ ξ k := by
    intro lam k
    have h := timeFourier_integral_mixture volume (A k) id (fun t ξ => frozenModulation χ j t ξ) (hj k) lam
    simp only [id] at h
    change timeFourier (fun t => G' t k) lam = _
    rw [show (fun t => G' t k) = fun t => ∫ ξ, A k ξ * frozenModulation χ j t ξ from funext fun t => hG' t k, h]
    refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
    simp only [A, synthMult]
    ring
  -- Step 3: differentiation under the `ξ`-integral
  let f : (Fin r → ℝ) → Mom d → (Fin r → ℝ) → ℂ := fun lam k ξ => synthMult χ j c lam ξ * Φ ξ k
  have hfs : ∀ lam ξ, ContDiff ℝ Λ fun k => f lam k ξ := fun lam ξ => contDiff_const.mul (hΦs ξ)
  have hfd : ∀ lam ξ (n : ℕ), n ≤ Λ → ∀ k, iteratedFDeriv ℝ n (fun k => f lam k ξ) k =
      synthMult χ j c lam ξ • iteratedFDeriv ℝ n (Φ ξ) k := by
    intro lam ξ n hn k
    have : (fun k => f lam k ξ) = synthMult χ j c lam ξ • Φ ξ := by
      funext k; simp [f, smul_eq_mul]
    rw [this, iteratedFDeriv_const_smul_apply ((hΦs ξ).contDiffAt.of_le (by exact_mod_cast hn))]
  have hfm : ∀ lam (n : ℕ), n ≤ Λ → ∀ k, AEStronglyMeasurable (fun ξ => iteratedFDeriv ℝ n (fun k => f lam k ξ) k) := by
    intro lam n hn k
    have hsm := stronglyMeasurable_iteratedFDeriv_param_of_le (f := fun k ξ => f lam k ξ) (hfs lam)
      (fun k => (stronglyMeasurable_synthMult hχ j c lam).mul (hΦm k)) n hn k
    exact hsm.aestronglyMeasurable
  have hfb : ∀ lam (n : ℕ), n ≤ Λ → ∃ B : (Fin r → ℝ) → ℝ, Integrable B ∧
      ∀ᵐ ξ, ∀ k, ‖iteratedFDeriv ℝ n (fun k => f lam k ξ) k‖ ≤ B ξ := by
    intro lam n hn
    refine ⟨fun ξ => c₀ * ∑ ρ : Fin n → Fin d, (E n ρ ξ).toReal,
      (integrable_finsetSum _ fun ρ _ => hEint n hn ρ).const_mul c₀, ?_⟩
    filter_upwards [ae_all_iff.2 (hEfin n hn)] with ξ hξ k
    rw [hfd lam ξ n hn k, norm_smul]
    refine mul_le_mul (hmb lam ξ) ((norm_le_sum_coordWords _).trans (Finset.sum_le_sum fun ρ _ => ?_))
      (norm_nonneg _) hc₀0
    have h1 := hmD n ρ ξ k
    rw [← ofReal_norm] at h1
    exact (ENNReal.ofReal_le_iff_le_toReal (hξ ρ).ne).1 h1
  have hint : ∀ lam (n : ℕ), n ≤ Λ → ∀ k, Integrable (fun ξ => iteratedFDeriv ℝ n (fun k => f lam k ξ) k) := by
    intro lam n hn k
    obtain ⟨B, hBi, hBb⟩ := hfb lam n hn
    exact hBi.mono' (hfm lam n hn k) (by filter_upwards [hBb] with ξ hξ using hξ k)
  have hGeq : ∀ lam, mixedTimeFourier G' lam = fun k => ∫ ξ, f lam k ξ := fun lam => funext fun k => hFT lam k
  have hcd : ∀ lam, ContDiff ℝ Λ (mixedTimeFourier G' lam) := fun lam => by
    rw [hGeq lam]
    exact contDiff_integral_param_of_le (hfs lam) (hfm lam) (hfb lam)
  have hder : ∀ lam (n : ℕ), n ≤ Λ → ∀ (ρ : Fin n → Fin d) k,
      momentumDerivative ρ (mixedTimeFourier G' lam) k =
        ∫ ξ, synthMult χ j c lam ξ * momentumDerivative ρ (Φ ξ) k := by
    intro lam n hn ρ k
    rw [momentumDerivative_apply, hGeq lam,
      iteratedFDeriv_integral_param_of_le (hfs lam) (hfm lam) (hfb lam) n hn,
      ContinuousMultilinearMap.integral_apply (hint lam n hn k)]
    refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
    beta_reduce
    rw [hfd lam ξ n hn k]
    rfl
  -- Step 4: each derivative is a mixture; Incoh's bound
  have hadm' : MixedFourierAdmissible Λ G' := ⟨hiG', Or.inr (ae_of_all _ hcd)⟩
  rw [mixedFourierNorm_eq_iSup hadm']
  refine iSup₂_le fun n hn => iSup_le fun ρ => ?_
  let Aρ : Mom d → (Fin r → ℝ) → ℂ := fun k ξ =>
    (Real.fourierChar (c * ξ j) : ℂ) * momentumDerivative ρ (Φ ξ) k
  have hmAρ : ∀ k, StronglyMeasurable (Aρ k) := fun k => by
    have hsm := stronglyMeasurable_iteratedFDeriv_param_of_le (f := fun k ξ => Φ ξ k) hΦs hΦm n hn k
    exact hp.stronglyMeasurable.mul ((continuous_eval_const (fun i => EuclideanSpace.single (ρ i) (1 : ℝ))).comp_stronglyMeasurable hsm)
  have hiAρ : ∀ k, Integrable (Aρ k) := fun k => by
    refine (hEint n hn ρ).mono' (hmAρ k).aestronglyMeasurable ?_
    filter_upwards [hEfin n hn ρ] with ξ hξ
    simp only [Aρ, norm_mul, Circle.norm_coe, one_mul]
    have h1 := hmD n ρ ξ k
    rw [← ofReal_norm] at h1
    exact (ENNReal.ofReal_le_iff_le_toReal hξ.ne).1 h1
  have hjρ : ∀ k, Integrable (fun z : (Fin r → ℝ) × (Fin r → ℝ) => Aρ k z.2 * frozenModulation χ j z.1 (id z.2))
      (volume.prod volume) := fun k =>
    integrable_joint_kernel_mixture volume hK hB hb (hiAρ k) (hmAρ k) measurable_id
  let H : (Fin r → ℝ) → Mom d → ℂ := fun t k => ∫ ξ, Aρ k ξ * frozenModulation χ j t ξ
  have hiH : ∀ k, Integrable fun t => H t k := fun k => by
    simpa only [H, id] using (hjρ k).integral_prod_left
  have hHFT : ∀ lam k, timeFourier (fun t => H t k) lam =
      momentumDerivative ρ (mixedTimeFourier G' lam) k := by
    intro lam k
    have h := timeFourier_integral_mixture volume (Aρ k) id (fun t ξ => frozenModulation χ j t ξ) (hjρ k) lam
    simp only [id] at h
    rw [h, hder lam n hn ρ k]
    refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
    simp only [Aρ, synthMult]
    ring
  have hHle := mixedFourierNorm00_integral_dominated_le volume θ Aρ (fun t ξ => frozenModulation χ j t ξ)
    hK (integrable_frozenModulation hχ hcχ j) hjρ (hEm n hn ρ) (fun k ξ => by
      simp only [Aρ, enorm_mul]
      rw [← ofReal_norm (((Real.fourierChar (c * ξ j) : Circle) : ℂ)), Circle.norm_coe, ENNReal.ofReal_one,
        one_mul]
      exact hmD n ρ ξ k)
  have hHnorm : mixedFourierNorm00 θ H =
      ∫⁻ lam, timeWeight θ lam * momentumSupNorm 0 (momentumDerivative ρ (mixedTimeFourier G' lam)) := by
    rw [mixedFourierNorm00_eq_lintegral hiH]
    refine lintegral_congr fun lam => ?_
    rw [momentumSupNorm_zero_eq]
    unfold mixedFourierEnvelope00
    simp only [hHFT]
  rw [← hHnorm]
  refine hHle.trans ?_
  calc
    _ ≤ ∫⁻ ξ, E n ρ ξ * (ENNReal.ofReal (2 ^ θ) * timeWeight θ ξ *
          timeFourierNorm θ (coordinateCutoff (r := r) χ)) :=
      lintegral_mono (fun ξ => mul_le_mul' le_rfl (timeFourierNorm_frozenModulation_le hθ χ j ξ))
    _ = ∫⁻ ξ, traceConst (r := r) θ χ * (timeWeight θ ξ * E n ρ ξ) := by
      refine lintegral_congr fun ξ => ?_
      unfold traceConst
      ac_rfl
    _ = traceConst (r := r) θ χ * ∫⁻ ξ, timeWeight θ ξ * E n ρ ξ :=
      lintegral_const_mul _ ((timeWeight_measurable θ).mul (hEm n hn ρ))
    _ ≤ traceConst (r := r) θ χ * M := mul_le_mul' le_rfl (hEw n hn ρ)

/-- A time slice of finite `𝔛^{θ,Λ,0}` norm has finite scalar norm. -/
theorem timeFourierNorm_slice_le_mixedFourierNorm (G : (Fin r → ℝ) → Mom d → ℂ) (k : Mom d) :
    timeFourierNorm θ (fun t => G t k) ≤ mixedFourierNorm θ Λ 0 G := by
  by_cases hadm : MixedFourierAdmissible Λ G
  · rw [mixedFourierNorm_eq_iSup hadm, timeFourierNorm_eq_lintegral (hadm.1 k)]
    refine le_iSup₂_of_le 0 (Nat.zero_le _) (le_iSup_of_le Fin.elim0 (lintegral_mono fun ξ => ?_))
    refine mul_le_mul' le_rfl ?_
    rw [momentumDerivative_zero, momentumSupNorm_zero_eq]
    exact le_iSup (fun k => ‖mixedTimeFourier G ξ k‖ₑ) k
  · rw [mixedFourierNorm_of_not_admissible hadm]
    exact le_top

theorem mixedRestrictionNorm_eq_agreement {Λ₂ : ℕ} (B : Set (Fin r → ℝ)) (K : Set (Mom d))
    (F : (Fin r → ℝ) → Mom d → ℂ) :
    mixedRestrictionNorm θ Λ Λ₂ B K (fun t k => F t k) =
      ⨅ (G : (Fin r → ℝ) → Mom d → ℂ) (_ : ∀ t ∈ B, ∀ k ∈ K, G t k = F t k), mixedFourierNorm θ Λ Λ₂ G := by
  unfold mixedRestrictionNorm
  refine iInf_congr fun G => ?_
  have he : (∀ (t : B) (k : K), G t k = F t k) ↔ (∀ t ∈ B, ∀ k ∈ K, G t k = F t k) :=
    ⟨fun h t ht k hk => h ⟨t, ht⟩ ⟨k, hk⟩, fun h t k => h t t.property k k.property⟩
  rw [he]

/-- **The trace estimate for `𝔛^{θ,Λ,0}` restriction norms** (`Λ ≥ 1`). -/
theorem mixedRestrictionNorm_trace_le (hΛ : Λ ≠ 0) (hθ : 0 ≤ θ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    {B T : Set (Fin r → ℝ)} {K : Set (Mom d)} (h : (Fin r → ℝ) → Mom d → ℂ)
    (hh : ∀ k ∈ K, Continuous fun t => h t k) (j : Fin r) (c : ℝ)
    (hT : ∀ t ∈ T, Function.update t j c ∈ closure (interior B))
    (hχT : ∀ t ∈ T, coordinateCutoff χ t = 1) :
    mixedRestrictionNorm θ Λ 0 T K (fun t k => h (Function.update t j c) k) ≤
      traceConst (r := r) θ χ * mixedRestrictionNorm θ Λ 0 B K (fun t k => h t k) := by
  rcases T.eq_empty_or_nonempty with hTe | ⟨t₀, ht₀⟩
  · subst hTe
    refine le_trans ?_ zero_le
    refine iInf₂_le (fun _ _ => 0) (fun t => absurd t.2 (Set.notMem_empty _)) |>.trans (le_of_eq ?_)
    have h0 : MixedFourierAdmissible Λ (fun (_ : Fin r → ℝ) (_ : Mom d) => (0 : ℂ)) :=
      ⟨fun _ => integrable_zero _ _ _, Or.inr (ae_of_all _ fun ξ => by
        have : mixedTimeFourier (fun (_ : Fin r → ℝ) (_ : Mom d) => (0 : ℂ)) ξ = fun _ => 0 := by
          funext k
          simp [mixedTimeFourier, timeFourier, VectorFourier.fourierIntegral]
        rw [this]
        exact contDiff_const)⟩
    rw [mixedFourierNorm_eq_iSup h0]
    refine le_antisymm (iSup₂_le fun n _ => iSup_le fun ρ => ?_) zero_le
    have : ∀ ξ, mixedTimeFourier (fun (_ : Fin r → ℝ) (_ : Mom d) => (0 : ℂ)) ξ = fun _ => 0 := by
      intro ξ
      funext k
      simp [mixedTimeFourier, timeFourier, VectorFourier.fourierIntegral]
    simp only [this, momentumDerivative_zero_fun, momentumSupNorm_zero_eq, enorm_zero, iSup_const,
      mul_zero, lintegral_zero, le_refl]
  have hK0 : traceConst (r := r) θ χ ≠ 0 :=
    (one_pos.trans_le (one_le_traceConst hθ hχ (hχT t₀ ht₀))).ne'
  have hKt : traceConst (r := r) θ χ ≠ ⊤ := by
    unfold traceConst
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (timeFourierNorm_lt_top_of_smooth_compact θ (coordinateCutoff_hasCompactSupport hcχ)
        (coordinateCutoff_contDiff hχ)).ne
  rw [mixedRestrictionNorm_eq_agreement T K (fun t k => h (Function.update t j c) k),
    mixedRestrictionNorm_eq_agreement B K h, ENNReal.mul_iInf_of_ne hK0 hKt]
  refine le_iInf fun G => ?_
  rw [ENNReal.mul_iInf_of_ne hK0 hKt]
  refine le_iInf fun hG => ?_
  by_cases hGt : mixedFourierNorm θ Λ 0 G = ⊤
  · rw [hGt, ENNReal.mul_top hK0]
    exact le_top
  have hGf : mixedFourierNorm θ Λ 0 G < ⊤ := lt_top_iff_ne_top.2 hGt
  refine iInf₂_le (fun t k => cutoffTimeTrace χ j c (rep fun u => G u k) t) (fun t ht k hk => ?_) |>.trans
    (mixedFourierNorm_cutoffTimeTrace_rep_le hΛ hθ hχ hcχ hGf j c)
  show coordinateCutoff χ t * rep (fun u => G u k) (Function.update t j c) = h (Function.update t j c) k
  rw [hχT t ht, one_mul]
  exact rep_eq_of_mem_closure_interior hθ ((timeFourierNorm_slice_le_mixedFourierNorm G k).trans_lt hGf)
    (fun s hs => hG s hs k hk) (hh k hk) (hT t ht)

end Main

end WaveTurbulence.Regref
