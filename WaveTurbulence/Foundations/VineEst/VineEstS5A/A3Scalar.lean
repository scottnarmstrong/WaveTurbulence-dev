/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.FSNorm
public import WaveTurbulence.Foundations.VineEst.VineEstS3.FSMain

/-! # Fourier-series expansion of a scalar time function, almost everywhere (V5 Step 4d-A, item 2)

`scalar_fs_ae`: for `g` with finite `timeFourierNorm θ g` and a box `B ⊆ Q_q`, the coefficients
`ĥ_m = ∫ kern_q(m, λ) ĝ(λ) dλ` satisfy `g(t) = ∑_m ĥ_m e^{πi m·t}` for almost every `t ∈ B` (no continuity of `g` is
needed: the continuous representative `rep g` is expanded and equals `g` a.e.), and
`∑_m ⟨m/2⟩^θ ‖ĥ_m‖ ≤ C ‖g‖_{𝔛^{θ,0,0}}` with `C` independent of `g, q, B`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5A
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.NormBridgeScratch
  MeasureTheory Set
open scoped ENNReal

variable {r : ℕ}

/-- The scalar Fourier-series coefficient. -/
noncomputable def hcoef (q : Fin r → ℝ) (g : (Fin r → ℝ) → ℂ) (m : Fin r → ℤ) : ℂ :=
  ∫ lam, kern q m lam * timeFourier g lam

theorem hcoef_sum_le {θ : ℝ} (hθ : 0 ≤ θ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (q : Fin r → ℝ) (g : (Fin r → ℝ) → ℂ),
      ∑' m : Fin r → ℤ, maxBracketPow θ (half m) * ‖hcoef q g m‖ₑ ≤ C * timeFourierNorm θ g := by
  obtain ⟨C0, hC0, hC0b⟩ := weight_kern_tsum_le (r := r) hθ
  refine ⟨ENNReal.ofReal C0 + 1, ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.one_ne_top⟩, fun q g => ?_⟩
  by_cases hint : Integrable g
  swap
  · have : timeFourierNorm θ g = ⊤ := by unfold timeFourierNorm; simp [hint]
    rw [this, ENNReal.mul_top (by simp)]; exact le_top
  have h1 : ∀ m : Fin r → ℤ, ‖hcoef q g m‖ₑ ≤
      ∫⁻ lam, ENNReal.ofReal ‖kern q m lam‖ * ‖timeFourier g lam‖ₑ := by
    intro m
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun lam => ?_
    rw [enorm_mul, ofReal_norm]
  have hw : ∀ m : Fin r → ℤ, maxBracketPow θ (half m) ≠ ⊤ := fun m => ENNReal.ofReal_ne_top
  have hmeas : ∀ m : Fin r → ℤ, AEMeasurable (fun lam => (maxBracketPow θ (half m) *
      ENNReal.ofReal ‖kern q m lam‖) * ‖timeFourier g lam‖ₑ) volume := by
    intro m
    refine ((measurable_const.mul (continuous_kern q m).measurable.norm.ennreal_ofReal).mul ?_).aemeasurable
    exact (timeFourier_continuous hint).measurable.enorm
  calc ∑' m : Fin r → ℤ, maxBracketPow θ (half m) * ‖hcoef q g m‖ₑ
      ≤ ∑' m : Fin r → ℤ, maxBracketPow θ (half m) * ∫⁻ lam, ENNReal.ofReal ‖kern q m lam‖ * ‖timeFourier g lam‖ₑ :=
        ENNReal.tsum_le_tsum fun m => mul_le_mul_right (h1 m) _
    _ = ∑' m : Fin r → ℤ, ∫⁻ lam, (maxBracketPow θ (half m) * ENNReal.ofReal ‖kern q m lam‖) * ‖timeFourier g lam‖ₑ := by
        refine tsum_congr fun m => ?_
        rw [← lintegral_const_mul' _ _ (hw m)]
        simp_rw [mul_assoc]
    _ = ∫⁻ lam, (∑' m : Fin r → ℤ, maxBracketPow θ (half m) * ENNReal.ofReal ‖kern q m lam‖) * ‖timeFourier g lam‖ₑ := by
        rw [← lintegral_tsum hmeas]
        simp_rw [ENNReal.tsum_mul_right]
    _ ≤ ∫⁻ lam, ENNReal.ofReal C0 * (maxBracketPow θ lam * ‖timeFourier g lam‖ₑ) :=
        lintegral_mono fun lam => by rw [← mul_assoc]; exact mul_le_mul_left (hC0b q lam) _
    _ = ENNReal.ofReal C0 * ∫⁻ lam, maxBracketPow θ lam * ‖timeFourier g lam‖ₑ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ (ENNReal.ofReal C0 + 1) * timeFourierNorm θ g := by
        refine mul_le_mul' le_self_add ?_
        unfold timeFourierNorm
        simp only [hint, ↓reduceIte]
        simp only [maxBracketPow_eq_timeWeight]; exact le_rfl

/-- **Scalar Fourier-series expansion, a.e. on a box.** -/
theorem scalar_fs_hasSum_ae {θ : ℝ} (hθ : 0 ≤ θ) (q : Fin r → ℝ) {B : Set (Fin r → ℝ)} (hB : B ⊆ cell q)
    (hBi : B ⊆ closure (interior B)) {g : (Fin r → ℝ) → ℂ} (hg : timeFourierNorm θ g < ⊤) :
    ∀ᵐ t : Fin r → ℝ, t ∈ B → HasSum (fun m : Fin r → ℤ => hcoef q g m * fsPhase m t) (g t) := by
  obtain ⟨hc, hae, hint', hft, -⟩ := Regref.rep_props hθ hg
  have hgn' : timeFourierNorm θ (Regref.rep g) < ⊤ := by
    have : timeFourierNorm θ (Regref.rep g) = timeFourierNorm θ g := by
      unfold timeFourierNorm
      have hi : Integrable g := integrable_of_timeFourierNorm_lt_top hg
      simp only [hint', hi, ↓reduceIte, hft]
    rwa [this]
  filter_upwards [hae] with t ht htB
  have := hasSum_coeff_slice hθ q hB (g := Regref.rep g) (h := Regref.rep g) hgn' (fun _ _ => rfl) hc
    (hBi htB)
  rw [hft] at this
  rw [← ht]
  exact this

end WaveTurbulence.VineEstS5A
