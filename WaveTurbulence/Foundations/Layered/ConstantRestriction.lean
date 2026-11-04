/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Layered.Telescope

/-!
# The restriction norm of a constant on a unit box

On a box `T` mapped into the unit box by a translation, a function constant in time has finite order-zero
restriction norm, controlled by the trace constant `2^θ ‖χ^{⊗r}‖_{𝔛^θ}` of the unit cutoff:

* `mixedRestrictionNorm00_one_le`: the constant `1` (extension: the translated cutoff `χ^{⊗r}(t + b)`);
* `mixedRestrictionNorm00_const_le`: a constant `c`, with the factor `‖c‖`.
-/

@[expose] public section

open MeasureTheory Set WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.Layered

variable {r : ℕ} {V : Type*}

theorem mixedRestrictionNorm00_one_le {θ : ℝ} (hθ : 0 ≤ θ) (T : Set (Fin r → ℝ)) (K : Set V)
    (b : Fin r → ℝ) (hT : ∀ t ∈ T, t + b ∈ (unitBox : Set (Fin r → ℝ))) :
    mixedRestrictionNorm00 θ T K (fun _ _ => (1 : ℂ)) ≤ Regref.traceConst (r := r) θ chiUnit := by
  have h1 := mixedRestrictionNorm00_translate_le θ (B := T) (B' := unitBox) K (fun _ _ => (1 : ℂ)) b hT
  refine h1.trans ?_
  refine (mixedRestrictionNorm00_le_extension (B := (unitBox : Set (Fin r → ℝ))) (K := K)
    (fun t (_ : V) => coordinateCutoff (r := r) chiUnit t)
    fun t _ => coordinateCutoff_chiUnit_eq_one t.2).trans ?_
  have hfin := timeFourierNorm_lt_top_of_smooth_compact θ
    (coordinateCutoff_hasCompactSupport (r := r) chiUnit_hasCompactSupport)
    (coordinateCutoff_contDiff (r := r) chiUnit_contDiff)
  have hint := integrable_of_timeFourierNorm_lt_top hfin
  rw [mixedFourierNorm00_eq_lintegral (fun _ => hint)]
  have h2 : ∫⁻ ξ, timeWeight θ ξ * mixedFourierEnvelope00
      (fun t (_ : V) => coordinateCutoff (r := r) chiUnit t) ξ ≤
      timeFourierNorm θ (coordinateCutoff (r := r) chiUnit) := by
    rw [timeFourierNorm_eq_lintegral hint]
    exact lintegral_mono fun ξ => mul_le_mul_right (iSup_le fun _ => le_rfl) _
  refine h2.trans ?_
  unfold Regref.traceConst
  have h3 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 ^ θ) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_rpow (by norm_num) hθ)
  calc timeFourierNorm θ (coordinateCutoff (r := r) chiUnit)
      = 1 * timeFourierNorm θ (coordinateCutoff (r := r) chiUnit) := (one_mul _).symm
    _ ≤ _ := mul_le_mul_left h3 _

theorem mixedRestrictionNorm00_const_le {θ : ℝ} (hθ : 0 ≤ θ) (T : Set (Fin r → ℝ)) (K : Set V)
    (b : Fin r → ℝ) (hT : ∀ t ∈ T, t + b ∈ (unitBox : Set (Fin r → ℝ))) (c : ℂ) :
    mixedRestrictionNorm00 θ T K (fun _ _ => c) ≤
      ENNReal.ofReal ‖c‖ * Regref.traceConst (r := r) θ chiUnit := by
  have h := mixedRestrictionNorm00_mul_momentum_le θ T K (fun _ => c) (norm_nonneg c)
    (fun _ _ => le_rfl) (fun _ _ => (1 : ℂ))
  have e : mixedRestrictionNorm00 θ T K (fun _ _ => c) =
      mixedRestrictionNorm00 θ T K (fun t v => (fun _ => c) (v : V) * (fun _ _ => (1 : ℂ)) (t : Fin r → ℝ) v) := by
    simp only [mul_one]
  rw [e]
  exact h.trans (mul_le_mul_right (mixedRestrictionNorm00_one_le hθ T K b hT) _)

end WaveTurbulence.Layered
