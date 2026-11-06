/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL2330Draft.Prod4
public import WaveTurbulence.Foundations.Regref.TraceDeriv

/-!
# Traces in the weighted norm `𝔛^{θ,Λ,Λ₂}` with momentum derivatives (PL23-30D)

The trace estimate `Regref.mixedFourierNorm_cutoffTimeTrace_rep_le` (landed, `Λ₂ = 0`) with the momentum weight
`⟨k⟩^{Λ₂}`. The proof is the landed one: the derivatives of the transform of the trace are mixtures of the
derivatives of the regularized transform `Φ`; the unweighted envelopes dominate the differentiation under the
integral, the weighted envelopes give the bound (the weight `⟨k⟩^{Λ₂}` is moved into the integrand `A`).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace WaveTurbulence.PL2330

open WaveTurbulence.Fourier WaveTurbulence.Regref WaveTurbulence.Incoh

variable {r d : ℕ} {Λ Λ₂ : ℕ} {θ : ℝ} {χ : ℝ → ℝ}

theorem enorm_real_mul {x : ℝ} (hx : 0 ≤ x) (z : ℂ) : ‖(x : ℂ) * z‖ₑ = ENNReal.ofReal x * ‖z‖ₑ := by
  rw [enorm_mul]
  congr 1
  rw [← ofReal_norm]
  simp [abs_of_nonneg hx]

theorem enorm_ofReal_mul_le_envW (Λ₂ : ℕ) (k : Mom d) (z : ℂ) :
    ‖(((momentumBracket k ^ Λ₂ : ℝ) : ℂ)) * z‖ₑ = ENNReal.ofReal (momentumBracket k ^ Λ₂) * ‖z‖ₑ :=
  enorm_real_mul (pow_nonneg (momentumBracket_nonneg k) _) z

/-- **The trace estimate with momentum derivatives and weights** (`Λ ≥ 1`). -/
theorem mixedFourierNorm_cutoffTimeTrace_rep_le_w (hΛ : Λ ≠ 0) (hθ : 0 ≤ θ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    {G : (Fin r → ℝ) → Mom d → ℂ} (hG : mixedFourierNorm θ Λ Λ₂ G < ⊤) (j : Fin r) (c : ℝ) :
    mixedFourierNorm θ Λ Λ₂ (fun t k => cutoffTimeTrace χ j c (rep fun u => G u k) t) ≤
      traceConst (r := r) θ χ * mixedFourierNorm θ Λ Λ₂ G := by
  classical
  have hadm := admissible_of_lt_top hG
  have hiG : ∀ k, Integrable (fun t => G t k) := hadm.1
  have hsm : ∀ᵐ ξ, ContDiff ℝ Λ (mixedTimeFourier G ξ) := hadm.2.resolve_left hΛ
  obtain ⟨Gd⟩ := Good.exists hiG hsm
  set M := mixedFourierNorm θ Λ Λ₂ G with hMdef
  -- the slices have finite scalar norms
  have hslice : ∀ k, timeFourierNorm θ (fun t => G t k) < ⊤ := fun k =>
    (timeFourierNorm_slice_le (θ := θ) (Λ := Λ) (Λ₂ := Λ₂) G k).trans_lt hG
  have hR := fun k => rep_props hθ (hslice k)
  -- the regularization
  let Φ : (Fin r → ℝ) → Mom d → ℂ := Gd.Φ
  have hΦs : ∀ ξ, ContDiff ℝ Λ (Φ ξ) := Gd.smooth
  have hΦm : ∀ k, StronglyMeasurable fun ξ => Φ ξ k := Gd.meas
  have hΦae : ∀ k, (fun ξ => Φ ξ k) =ᵐ[volume] fun ξ => mixedTimeFourier G ξ k := fun k => by
    filter_upwards [Gd.ae] with ξ hξ
    exact congrFun hξ k
  -- envelopes: unweighted (domination) and weighted (the bound)
  let E : (n : ℕ) → (Fin n → Fin d) → (Fin r → ℝ) → ℝ≥0∞ :=
    fun n ρ ξ => ⨆ k, ‖momentumDerivative ρ (Φ ξ) k‖ₑ
  let Ew : (n : ℕ) → (Fin n → Fin d) → (Fin r → ℝ) → ℝ≥0∞ :=
    fun n ρ ξ => momentumSupNorm Λ₂ (momentumDerivative ρ (Φ ξ))
  have hEm : ∀ n, n ≤ Λ → ∀ ρ : Fin n → Fin d, Measurable (E n ρ) :=
    fun n hn ρ => measurable_wordEnvelope hΦs hΦm hn ρ
  have hEwm : ∀ n, n ≤ Λ → ∀ ρ : Fin n → Fin d, Measurable (Ew n ρ) :=
    fun n hn ρ => Gd.env_meas Λ₂ hn ρ
  have hEEw : ∀ n (ρ : Fin n → Fin d) ξ, E n ρ ξ ≤ Ew n ρ ξ := fun n ρ ξ => by
    have h0 : E n ρ ξ = momentumSupNorm 0 (momentumDerivative ρ (Φ ξ)) := (momentumSupNorm_zero_eq _).symm
    rw [h0]
    exact momentumSupNorm_mono_weight (Nat.zero_le _) _
  have hEw : ∀ n, n ≤ Λ → ∀ ρ : Fin n → Fin d, ∫⁻ ξ, timeWeight θ ξ * Ew n ρ ξ ≤ M :=
    fun n hn ρ => Gd.nInt_le hadm hn ρ
  have hw1 : ∀ ξ : Fin r → ℝ, (1 : ℝ≥0∞) ≤ timeWeight θ ξ := fun ξ => one_le_timeWeight hθ ξ
  have hE1w : ∀ n, n ≤ Λ → ∀ ρ : Fin n → Fin d, ∫⁻ ξ, Ew n ρ ξ ≠ ⊤ := by
    intro n hn ρ
    have h1 : ∫⁻ ξ, Ew n ρ ξ ≤ ∫⁻ ξ, timeWeight θ ξ * Ew n ρ ξ := by
      refine lintegral_mono fun ξ => ?_
      calc Ew n ρ ξ = 1 * Ew n ρ ξ := (one_mul _).symm
        _ ≤ timeWeight θ ξ * Ew n ρ ξ := mul_le_mul_left (hw1 ξ) _
    exact ((h1.trans (hEw n hn ρ)).trans_lt hG).ne
  have hE1 : ∀ n, n ≤ Λ → ∀ ρ : Fin n → Fin d, ∫⁻ ξ, E n ρ ξ ≠ ⊤ := fun n hn ρ =>
    ne_top_of_le_ne_top (hE1w n hn ρ) (lintegral_mono fun ξ => hEEw n ρ ξ)
  have hEfin : ∀ n, n ≤ Λ → ∀ ρ : Fin n → Fin d, ∀ᵐ ξ, E n ρ ξ < ⊤ := fun n hn ρ =>
    ae_lt_top (hEm n hn ρ) (hE1 n hn ρ)
  have hEint : ∀ n, n ≤ Λ → ∀ ρ : Fin n → Fin d, Integrable fun ξ => (E n ρ ξ).toReal := fun n hn ρ =>
    integrable_toReal_of_lintegral_ne_top (hEm n hn ρ).aemeasurable (hE1 n hn ρ)
  have hEwfin : ∀ n, n ≤ Λ → ∀ ρ : Fin n → Fin d, ∀ᵐ ξ, Ew n ρ ξ < ⊤ := fun n hn ρ =>
    ae_lt_top (hEwm n hn ρ) (hE1w n hn ρ)
  have hEwint : ∀ n, n ≤ Λ → ∀ ρ : Fin n → Fin d, Integrable fun ξ => (Ew n ρ ξ).toReal := fun n hn ρ =>
    integrable_toReal_of_lintegral_ne_top (hEwm n hn ρ).aemeasurable (hE1w n hn ρ)
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
  -- Step 4: each derivative is a mixture; Incoh's bound (the weight is moved into the integrand)
  have hadm' : MixedFourierAdmissible Λ G' := ⟨hiG', Or.inr (ae_of_all _ hcd)⟩
  rw [mixedFourierNorm_eq_iSup hadm']
  refine iSup₂_le fun n hn => iSup_le fun ρ => ?_
  let W : Mom d → ℂ := fun k => (((momentumBracket k ^ Λ₂ : ℝ) : ℂ))
  let Aρ : Mom d → (Fin r → ℝ) → ℂ := fun k ξ =>
    W k * ((Real.fourierChar (c * ξ j) : ℂ) * momentumDerivative ρ (Φ ξ) k)
  have hmAρ : ∀ k, StronglyMeasurable (Aρ k) := fun k => by
    have hsm := stronglyMeasurable_iteratedFDeriv_param_of_le (f := fun k ξ => Φ ξ k) hΦs hΦm n hn k
    exact stronglyMeasurable_const.mul (hp.stronglyMeasurable.mul
      ((continuous_eval_const (fun i => EuclideanSpace.single (ρ i) (1 : ℝ))).comp_stronglyMeasurable hsm))
  have hAbd : ∀ k ξ, ‖Aρ k ξ‖ₑ ≤ Ew n ρ ξ := fun k ξ => by
    simp only [Aρ, W]
    rw [enorm_ofReal_mul_le_envW, enorm_mul, ← ofReal_norm (((Real.fourierChar (c * ξ j) : Circle) : ℂ)),
      Circle.norm_coe, ENNReal.ofReal_one, one_mul]
    exact le_iSup (fun k => ENNReal.ofReal (momentumBracket k ^ Λ₂) * ‖momentumDerivative ρ (Φ ξ) k‖ₑ) k
  have hiAρ : ∀ k, Integrable (Aρ k) := fun k => by
    refine (hEwint n hn ρ).mono' (hmAρ k).aestronglyMeasurable ?_
    filter_upwards [hEwfin n hn ρ] with ξ hξ
    have h1 := hAbd k ξ
    rw [← ofReal_norm] at h1
    exact (ENNReal.ofReal_le_iff_le_toReal hξ.ne).1 h1
  have hjρ : ∀ k, Integrable (fun z : (Fin r → ℝ) × (Fin r → ℝ) => Aρ k z.2 * frozenModulation χ j z.1 (id z.2))
      (volume.prod volume) := fun k =>
    integrable_joint_kernel_mixture volume hK hB hb (hiAρ k) (hmAρ k) measurable_id
  let H : (Fin r → ℝ) → Mom d → ℂ := fun t k => ∫ ξ, Aρ k ξ * frozenModulation χ j t ξ
  have hiH : ∀ k, Integrable fun t => H t k := fun k => by
    simpa only [H, id] using (hjρ k).integral_prod_left
  have hHFT : ∀ lam k, timeFourier (fun t => H t k) lam =
      W k * momentumDerivative ρ (mixedTimeFourier G' lam) k := by
    intro lam k
    have h := timeFourier_integral_mixture volume (Aρ k) id (fun t ξ => frozenModulation χ j t ξ) (hjρ k) lam
    simp only [id] at h
    rw [h, hder lam n hn ρ k, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
    simp only [Aρ, synthMult]
    ring
  have hHle := mixedFourierNorm00_integral_dominated_le volume θ Aρ (fun t ξ => frozenModulation χ j t ξ)
    hK (integrable_frozenModulation hχ hcχ j) hjρ (hEwm n hn ρ) hAbd
  have hHnorm : mixedFourierNorm00 θ H =
      ∫⁻ lam, timeWeight θ lam * momentumSupNorm Λ₂ (momentumDerivative ρ (mixedTimeFourier G' lam)) := by
    rw [mixedFourierNorm00_eq_lintegral hiH]
    refine lintegral_congr fun lam => ?_
    unfold mixedFourierEnvelope00 momentumSupNorm
    simp only [hHFT, W, enorm_ofReal_mul_le_envW]
  rw [← hHnorm]
  refine hHle.trans ?_
  calc
    _ ≤ ∫⁻ ξ, Ew n ρ ξ * (ENNReal.ofReal (2 ^ θ) * timeWeight θ ξ *
          timeFourierNorm θ (coordinateCutoff (r := r) χ)) :=
      lintegral_mono (fun ξ => mul_le_mul_right (timeFourierNorm_frozenModulation_le hθ χ j ξ) _)
    _ = ∫⁻ ξ, traceConst (r := r) θ χ * (timeWeight θ ξ * Ew n ρ ξ) := by
      refine lintegral_congr fun ξ => ?_
      unfold traceConst
      ac_rfl
    _ = traceConst (r := r) θ χ * ∫⁻ ξ, timeWeight θ ξ * Ew n ρ ξ :=
      lintegral_const_mul _ ((timeWeight_measurable θ).mul (hEwm n hn ρ))
    _ ≤ traceConst (r := r) θ χ * M := mul_le_mul_right (hEw n hn ρ) _

/-- **The trace estimate for restriction norms with weights** (`Λ ≥ 1`, all momenta). -/
theorem rN_trace_le_w (hΛ : Λ ≠ 0) (hθ : 0 ≤ θ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    {B T : Set (Fin r → ℝ)} (h : (Fin r → ℝ) → Mom d → ℂ) (hh : ∀ k, Continuous fun t => h t k)
    (j : Fin r) (c : ℝ) (hT : ∀ t ∈ T, Function.update t j c ∈ closure (interior B))
    (hχT : ∀ t ∈ T, coordinateCutoff χ t = 1) :
    rN θ Λ Λ₂ T (fun t k => h (Function.update t j c) k) ≤ traceConst (r := r) θ χ * rN θ Λ Λ₂ B h := by
  rcases T.eq_empty_or_nonempty with hTe | ⟨t₀, ht₀⟩
  · subst hTe
    refine le_trans ?_ zero_le
    exact (rN_le_extension _ _ (fun (_ : Fin r → ℝ) (_ : Mom d) => (0 : ℂ))
      (fun t ht => absurd ht (Set.notMem_empty _))).trans (mixedFourierNorm_zero θ Λ Λ₂).le
  have hK0 : traceConst (r := r) θ χ ≠ 0 :=
    (one_pos.trans_le (one_le_traceConst hθ hχ (hχT t₀ ht₀))).ne'
  have hKt : traceConst (r := r) θ χ ≠ ⊤ := by
    unfold traceConst
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (timeFourierNorm_lt_top_of_smooth_compact θ (coordinateCutoff_hasCompactSupport hcχ)
        (coordinateCutoff_contDiff hχ)).ne
  rw [rN_eq_agreement T (fun t k => h (Function.update t j c) k), rN_eq_agreement B h,
    ENNReal.mul_iInf_of_ne hK0 hKt]
  refine le_iInf fun G => ?_
  rw [ENNReal.mul_iInf_of_ne hK0 hKt]
  refine le_iInf fun hG => ?_
  by_cases hGt : mixedFourierNorm θ Λ Λ₂ G = ⊤
  · rw [hGt, ENNReal.mul_top hK0]
    exact le_top
  have hGf : mixedFourierNorm θ Λ Λ₂ G < ⊤ := lt_top_iff_ne_top.2 hGt
  refine iInf₂_le (fun t k => cutoffTimeTrace χ j c (rep fun u => G u k) t) (fun t ht k hk => ?_) |>.trans
    (mixedFourierNorm_cutoffTimeTrace_rep_le_w hΛ hθ hχ hcχ hGf j c)
  show coordinateCutoff χ t * rep (fun u => G u k) (Function.update t j c) = h (Function.update t j c) k
  rw [hχT t ht, one_mul]
  exact rep_eq_of_mem_closure_interior hθ
    ((timeFourierNorm_slice_le (θ := θ) (Λ := Λ) (Λ₂ := Λ₂) G k).trans_lt hGf)
    (fun s hs => hG s hs k hk) (hh k) (hT t ht)

end WaveTurbulence.PL2330
