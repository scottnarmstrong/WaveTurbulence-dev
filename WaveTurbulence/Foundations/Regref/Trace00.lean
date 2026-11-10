/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Regref.FourierAE
public import WaveTurbulence.Foundations.Incoh.FrozenModulationMeasurable
public import WaveTurbulence.Foundations.Incoh.DominatedFourierMixture
public import WaveTurbulence.Foundations.Fourier.Norm00VRestriction

/-!
# Traces in the `𝔛^{θ,0,0}` norm, for arbitrary extensions (GAP.regrefNorm, the `q' < r` case)

The landed `Incoh.mixedFourierNorm00_cutoffTimeTrace_le` bounds the cutoff trace `χ(t) F(t[j ↦ c])` of a **smooth
compactly supported** family. A restriction norm `‖h‖_{𝔛(ℬ)}` is an infimum over **arbitrary** extensions `G`
(agreeing with `h` pointwise on `ℬ`), whose values on the null set `{t_j = c}` are not controlled by `Ĝ`. Here:

* `rep f := t ↦ (𝓕𝓕 f)(-t)` is the continuous representative (`Regref.FourierAE`: `rep f = f` a.e.);
* `mixedFourierNorm00_cutoffTimeTrace_rep_le`: the trace of the representative obeys the Incoh bound;
* `rep_eq_of_mem_closure_interior`: if `G = h` on `ℬ` and `h` is continuous, then `rep G = h` on `closure (interior ℬ)`;
* **`mixedRestrictionNorm00_trace_le`**: `‖h(t[j ↦ c])‖_{𝔛^{θ,0,0}(T)} ≤ 2^θ ‖χ^{⊗r}‖_{𝔛^θ} ‖h‖_{𝔛^{θ,0,0}(ℬ)}` when
  `t[j ↦ c] ∈ closure (interior ℬ)` and `χ^{⊗r} = 1` on `T`, for `h` continuous in time.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace WaveTurbulence.Regref

open WaveTurbulence.Fourier WaveTurbulence.Incoh

variable {r : ℕ}

/-- The continuous representative `t ↦ (𝓕𝓕 f)(-t)`. -/
noncomputable def rep (f : (Fin r → ℝ) → ℂ) : (Fin r → ℝ) → ℂ := fun t => timeFourier (timeFourier f) (-t)

theorem timeFourier_congr_ae {f g : (Fin r → ℝ) → ℂ} (h : f =ᵐ[volume] g) :
    timeFourier f = timeFourier g := by
  funext ξ
  unfold timeFourier VectorFourier.fourierIntegral
  exact integral_congr_ae (h.mono fun t ht => by simp only [ht])

/-- The representative of a slice of finite `𝔛^{θ}` norm: continuous, integrable, the same transform. -/
theorem rep_props {θ : ℝ} (hθ : 0 ≤ θ) {f : (Fin r → ℝ) → ℂ} (hf : timeFourierNorm θ f < ⊤) :
    Continuous (rep f) ∧ rep f =ᵐ[volume] f ∧ Integrable (rep f) ∧ timeFourier (rep f) = timeFourier f ∧
      Integrable (timeFourier (rep f)) := by
  obtain ⟨hc, hae⟩ := timeFourier_continuous_representative hθ f hf
  have hi := integrable_of_timeFourierNorm_lt_top hf
  have hft : timeFourier (rep f) = timeFourier f := timeFourier_congr_ae hae
  exact ⟨hc, hae, hi.congr hae.symm, hft, hft ▸ integrable_timeFourier_of_norm_lt_top hθ hf⟩

/-- **The cutoff trace of the continuous representatives** obeys the landed Incoh bound. -/
theorem mixedFourierNorm00_cutoffTimeTrace_rep_le {V : Type*} {θ : ℝ} (hθ : 0 ≤ θ)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    {F : (Fin r → ℝ) → V → ℂ} (hF : mixedFourierNorm00 θ F < ⊤) (j : Fin r) (c : ℝ) :
    mixedFourierNorm00 θ (fun t v => cutoffTimeTrace χ j c (rep fun u => F u v) t) ≤
      (ENNReal.ofReal (2 ^ θ) * timeFourierNorm θ (coordinateCutoff (r := r) χ)) *
        mixedFourierNorm00 θ F := by
  have hiF (v : V) : Integrable (fun t => F t v) := integrable_of_mixedFourierNorm00_lt_top hF v
  have hR (v : V) := rep_props hθ ((timeFourierNorm_slice_le_mixedFourierNorm00 θ F v).trans_lt hF)
  let A : V → (Fin r → ℝ) → ℂ := fun v ξ =>
    (Real.fourierChar (c * ξ j) : ℂ) * timeFourier (rep fun u => F u v) ξ
  have hcoe : Continuous (fun z : Circle => (z : ℂ)) := continuous_subtype_val
  have hp : Continuous (fun ξ : Fin r → ℝ => (Real.fourierChar (c * ξ j) : ℂ)) :=
    hcoe.comp (Real.continuous_fourierChar.comp (by fun_prop))
  have hiA (v : V) : Integrable (A v) :=
    (hR v).2.2.2.2.bdd_mul hp.aestronglyMeasurable (Filter.Eventually.of_forall (fun ξ => by
      simp only [Circle.norm_coe]; exact le_rfl))
  have hmA (v : V) : StronglyMeasurable (A v) :=
    hp.stronglyMeasurable.mul (timeFourier_continuous (hR v).2.2.1).stronglyMeasurable
  have hK := stronglyMeasurable_frozenModulation hχ j
  have hB := integrable_norm_coordinateCutoff (r := r) hχ hcχ
  have hb := fun t ξ => (norm_frozenModulation χ j t ξ).le
  have hj (v : V) := integrable_joint_kernel_mixture volume hK hB hb (hiA v) (hmA v) measurable_id
  have he (t : Fin r → ℝ) (v : V) : cutoffTimeTrace χ j c (rep fun u => F u v) t =
      ∫ ξ, A v ξ * frozenModulation χ j t ξ :=
    cutoffTimeTrace_eq_fourier_mixture χ j c (hR v).2.2.1 (hR v).2.2.2.2 (hR v).1 t
  have hAmp (v : V) (ξ : Fin r → ℝ) : ‖A v ξ‖ₑ ≤ mixedFourierEnvelope00 F ξ := by
    have hn : ‖A v ξ‖ = ‖timeFourier (fun t => F t v) ξ‖ := by
      simp only [A, norm_mul, Circle.norm_coe, one_mul, (hR v).2.2.2.1]
    rw [← ofReal_norm, hn, ofReal_norm]
    exact le_iSup (fun v => ‖timeFourier (fun t => F t v) ξ‖ₑ) v
  have hs := mixedFourierNorm00_integral_dominated_le volume θ A (fun t ξ => frozenModulation χ j t ξ)
    hK (integrable_frozenModulation hχ hcχ j) hj (measurable_mixedFourierEnvelope00 hiF) hAmp
  have hEq : (fun t v => cutoffTimeTrace χ j c (rep fun u => F u v) t) =
      (fun t v => ∫ ξ, A v ξ * frozenModulation χ j t ξ) := funext (fun t => funext (he t))
  rw [← hEq] at hs
  apply hs.trans
  calc
    _ ≤ ∫⁻ ξ, mixedFourierEnvelope00 F ξ *
        (ENNReal.ofReal (2 ^ θ) * timeWeight θ ξ *
          timeFourierNorm θ (coordinateCutoff (r := r) χ)) :=
      lintegral_mono (fun ξ => mul_le_mul' le_rfl (timeFourierNorm_frozenModulation_le hθ χ j ξ))
    _ = ∫⁻ ξ, (ENNReal.ofReal (2 ^ θ) * timeFourierNorm θ (coordinateCutoff (r := r) χ)) *
        (timeWeight θ ξ * mixedFourierEnvelope00 F ξ) := by
      apply lintegral_congr
      intro ξ
      ac_rfl
    _ = _ := by
      rw [mixedFourierNorm00_eq_lintegral hiF]
      exact lintegral_const_mul _ ((timeWeight_measurable θ).mul
        (measurable_mixedFourierEnvelope00 hiF))

/-- **The representative agrees with a continuous `h` on `closure (interior ℬ)`** when `G = h` on `ℬ`. -/
theorem rep_eq_of_mem_closure_interior {θ : ℝ} (hθ : 0 ≤ θ) {B : Set (Fin r → ℝ)}
    {g h : (Fin r → ℝ) → ℂ} (hg : timeFourierNorm θ g < ⊤) (hgh : ∀ t ∈ B, g t = h t)
    (hh : Continuous h) {t : Fin r → ℝ} (ht : t ∈ closure (interior B)) : rep g t = h t := by
  obtain ⟨hc, hae, -⟩ := rep_props hθ hg
  have hint : ∀ x ∈ interior B, rep g x = h x := by
    have hU : IsOpen ({x | rep g x ≠ h x} ∩ interior B) :=
      (isOpen_ne_fun hc hh).inter isOpen_interior
    have hnull : volume ({x | rep g x ≠ h x} ∩ interior B) = 0 := by
      refine measure_mono_null (fun x hx => ?_) (ae_iff.1 hae)
      simp only [mem_inter_iff, mem_ofPred_eq] at hx ⊢
      rw [hgh x (interior_subset hx.2)]
      exact hx.1
    have hemp := hU.measure_eq_zero_iff volume |>.1 hnull
    intro x hx
    by_contra hne
    exact (Set.eq_empty_iff_forall_notMem.1 hemp) x ⟨hne, hx⟩
  have hcl : IsClosed {x | rep g x = h x} := isClosed_eq hc hh
  exact closure_minimal hint hcl ht

/-- `2^θ ‖χ^{⊗r}‖_{𝔛^θ}`, the trace constant. -/
noncomputable def traceConst (θ : ℝ) (χ : ℝ → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 ^ θ) * timeFourierNorm θ (coordinateCutoff (r := r) χ)

theorem one_le_traceConst {θ : ℝ} (hθ : 0 ≤ θ) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {t : Fin r → ℝ}
    (ht : coordinateCutoff χ t = 1) : 1 ≤ traceConst (r := r) θ χ := by
  have h1 := enorm_le_timeFourierNorm_at hθ (coordinateCutoff (r := r) χ) t
    ((coordinateCutoff_contDiff hχ).continuous.continuousAt)
  rw [ht, enorm_one] at h1
  have h2 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 ^ θ) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_rpow (by norm_num) hθ)
  unfold traceConst
  calc (1 : ℝ≥0∞) = 1 * 1 := (one_mul 1).symm
    _ ≤ _ := mul_le_mul' h2 h1

/-- **The trace estimate for restriction norms** (`𝔛^{θ,0,0}`, any vector variables). -/
theorem mixedRestrictionNorm00_trace_le {V : Type*} {θ : ℝ} (hθ : 0 ≤ θ)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    {B T : Set (Fin r → ℝ)} {K : Set V} (h : (Fin r → ℝ) → V → ℂ)
    (hh : ∀ v ∈ K, Continuous fun t => h t v) (j : Fin r) (c : ℝ)
    (hT : ∀ t ∈ T, Function.update t j c ∈ closure (interior B))
    (hχT : ∀ t ∈ T, coordinateCutoff χ t = 1) :
    mixedRestrictionNorm00 θ T K (fun t v => h (Function.update t j c) v) ≤
      traceConst (r := r) θ χ * mixedRestrictionNorm00 θ B K (fun t v => h t v) := by
  rcases T.eq_empty_or_nonempty with hTe | ⟨t₀, ht₀⟩
  · subst hTe
    have h0 : mixedRestrictionNorm00 θ (∅ : Set (Fin r → ℝ)) K
        (fun t v => h (Function.update t.1 j c) v.1) ≤ 0 := by
      calc _ ≤ mixedFourierNorm00 θ (fun (_ : Fin r → ℝ) (_ : V) => (0 : ℂ)) :=
            mixedRestrictionNorm00_le_extension _ (fun t => absurd t.2 (Set.notMem_empty _))
        _ ≤ 0 := by simp
    exact h0.trans zero_le
  rw [mixedRestrictionNorm00_eq_agreement θ T K (fun t v => h (Function.update t j c) v),
    mixedRestrictionNorm00_eq_agreement θ B K h, ENNReal.mul_iInf_of_ne
      (one_pos.trans_le (one_le_traceConst hθ hχ (hχT t₀ ht₀))).ne' (by
        unfold traceConst
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (timeFourierNorm_lt_top_of_smooth_compact θ (coordinateCutoff_hasCompactSupport hcχ)
            (coordinateCutoff_contDiff hχ)).ne)]
  refine le_iInf fun G => ?_
  rw [ENNReal.mul_iInf_of_ne
      (one_pos.trans_le (one_le_traceConst hθ hχ (hχT t₀ ht₀))).ne' (by
        unfold traceConst
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (timeFourierNorm_lt_top_of_smooth_compact θ (coordinateCutoff_hasCompactSupport hcχ)
            (coordinateCutoff_contDiff hχ)).ne)]
  refine le_iInf fun hG => ?_
  by_cases hGt : mixedFourierNorm00 θ G = ⊤
  · rw [hGt, ENNReal.mul_top (one_pos.trans_le (one_le_traceConst hθ hχ (hχT t₀ ht₀))).ne']
    exact le_top
  have hGf : mixedFourierNorm00 θ G < ⊤ := lt_top_iff_ne_top.2 hGt
  refine iInf₂_le (fun t v => cutoffTimeTrace χ j c (rep fun u => G u v) t) (fun t ht v hv => ?_) |>.trans
    (mixedFourierNorm00_cutoffTimeTrace_rep_le hθ hχ hcχ hGf j c)
  show coordinateCutoff χ t * rep (fun u => G u v) (Function.update t j c) = h (Function.update t j c) v
  rw [hχT t ht, one_mul]
  exact rep_eq_of_mem_closure_interior hθ ((timeFourierNorm_slice_le_mixedFourierNorm00 θ G v).trans_lt hGf)
    (fun s hs => hG s hs v hv) (hh v hv) (hT t ht)

end WaveTurbulence.Regref
