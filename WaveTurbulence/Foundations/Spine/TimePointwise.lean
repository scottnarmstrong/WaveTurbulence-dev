/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Fourier.TimeProduct
public import WaveTurbulence.Foundations.Fourier.Norm00VRestriction
/-! Pointwise use of source Fourier norm estimates retains the continuity-point hypothesis. -/
public section
namespace WaveTurbulence.LGSpine
open MeasureTheory WithLp WaveTurbulence.Fourier
open scoped FourierTransform ENNReal Topology

/-- The landed coordinate inversion proof, localized to one continuity point. -/
theorem timeFourier_inversion_at {r : ℕ} {f : (Fin r → ℝ) → ℂ}
    (hf : Integrable f) (hhf : Integrable (timeFourier f)) (t : Fin r → ℝ) (hc : ContinuousAt f t) : timeFourier (timeFourier f) (-t) = f t := by
  have hfi := (PiLp.volume_preserving_ofLp (Fin r)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (Fin r → ℝ)).symm.measurableEmbedding (g := f) |>.mpr hf
  have he : (fun x : EuclideanSpace ℝ (Fin r) => timeFourier f (ofLp x)) =
      𝓕 (fun x : EuclideanSpace ℝ (Fin r) => f (ofLp x)) := by
    funext x
    simpa only [toLp_ofLp] using timeFourier_eq_euclidean f (ofLp x)
  have hhi := (PiLp.volume_preserving_ofLp (Fin r)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (Fin r → ℝ)).symm.measurableEmbedding
      (g := timeFourier f) |>.mpr hhf
  simp only [Function.comp_def] at hhi
  rw [he] at hhi
  have hcont : ContinuousAt (fun x : EuclideanSpace ℝ (Fin r) => f (ofLp x)) (toLp 2 t) :=
    hc.comp (PiLp.continuous_ofLp 2 _).continuousAt
  have hinv := hfi.fourierInv_fourier_eq hhi hcont
  rw [timeFourier_eq_euclidean, he]
  rw [Real.fourierInv_eq_fourier_neg] at hinv
  simpa only [Function.comp_def, ofLp_toLp, toLp_neg] using hinv


/-- A nonnegative Fourier regularity norm bounds a function at each of its continuity points. -/
theorem enorm_le_timeFourierNorm_at {r : ℕ} {θ : ℝ} (hθ : 0 ≤ θ)
    (f : (Fin r → ℝ) → ℂ) (t : Fin r → ℝ) (hc : ContinuousAt f t) :
    ‖f t‖ₑ ≤ timeFourierNorm θ f := by
  by_cases ht : timeFourierNorm θ f = ⊤
  · rw [ht]; exact le_top
  have hf := integrable_of_timeFourierNorm_lt_top (lt_top_iff_ne_top.mpr ht)
  have hff := integrable_timeFourier_of_norm_lt_top hθ (lt_top_iff_ne_top.mpr ht)
  rw [← timeFourier_inversion_at hf hff t hc]
  calc
    ‖timeFourier (timeFourier f) (-t)‖ₑ ≤ ∫⁻ ξ, ‖timeFourier f ξ‖ₑ := by
      change ‖∫ ξ, Real.fourierChar (-timePairing r ξ (-t)) • timeFourier f ξ‖ₑ ≤ _
      simpa only [Circle.enorm_smul] using
        (enorm_integral_le_lintegral_enorm
          (fun ξ => Real.fourierChar (-timePairing r ξ (-t)) • timeFourier f ξ))
    _ ≤ timeFourierNorm θ f := by
      rw [timeFourierNorm_eq_lintegral hf]
      apply lintegral_mono
      intro ξ
      have hw : (1 : ℝ≥0∞) ≤ timeWeight θ ξ := by
        simpa only [timeWeight, ENNReal.ofReal_one] using
          ENNReal.ofReal_le_ofReal (Real.one_le_rpow (one_le_timeBracket ξ) hθ)
      simpa only [one_mul] using mul_le_mul_left hw ‖timeFourier f ξ‖ₑ

/-- At an interior continuity point, every agreeing extension gives the same bound,
so the infimum over all such extensions gives a pointwise bound too. -/
theorem enorm_le_mixedRestrictionNorm00_at {r : ℕ} {V : Type*} {θ : ℝ}
    (hθ : 0 ≤ θ) (B : Set (Fin r → ℝ)) (K : Set V)
    (F : (Fin r → ℝ) → V → ℂ) (t : Fin r → ℝ) (v : V)
    (hB : B ∈ 𝓝 t) (hv : v ∈ K) (hc : ContinuousAt (fun s => F s v) t) :
    ‖F t v‖ₑ ≤ mixedRestrictionNorm00 θ B K (fun s k => F s k) := by
  rw [mixedRestrictionNorm00_eq_agreement]
  apply le_iInf
  intro G
  apply le_iInf
  intro hG
  have he : (fun s => G s v) =ᶠ[𝓝 t] (fun s => F s v) :=
    Filter.mem_of_superset hB (fun s hs => hG s hs v hv)
  have hcG := hc.congr_of_eventuallyEq he
  rw [← hG t (mem_of_mem_nhds hB) v hv]
  exact (enorm_le_timeFourierNorm_at hθ _ t hcG).trans
    (timeFourierNorm_slice_le_mixedFourierNorm00 θ G v)

/-- Continuity propagates the interior estimate to every point in the closure of the interior.
In particular this covers the closed rectangular time boxes of the source. -/
theorem enorm_le_mixedRestrictionNorm00_closure_interior {r : ℕ} {V : Type*} {θ : ℝ}
    (hθ : 0 ≤ θ) (B : Set (Fin r → ℝ)) (K : Set V)
    (F : (Fin r → ℝ) → V → ℂ) (t : Fin r → ℝ) (v : V)
    (ht : t ∈ closure (interior B)) (hv : v ∈ K) (hc : Continuous (fun s => F s v)) :
    ‖F t v‖ₑ ≤ mixedRestrictionNorm00 θ B K (fun s k => F s k) := by
  have hclosed : IsClosed {s : Fin r → ℝ | ‖F s v‖ₑ ≤
      mixedRestrictionNorm00 θ B K (fun s k => F s k)} :=
    isClosed_le (continuous_enorm.comp hc) continuous_const
  have hsub : interior B ⊆ {s : Fin r → ℝ | ‖F s v‖ₑ ≤
      mixedRestrictionNorm00 θ B K (fun s k => F s k)} := by
    intro s hs
    exact enorm_le_mixedRestrictionNorm00_at hθ B K F s v
      (mem_interior_iff_mem_nhds.mp hs) hv hc.continuousAt
  exact closure_minimal hsub hclosed ht

end WaveTurbulence.LGSpine
