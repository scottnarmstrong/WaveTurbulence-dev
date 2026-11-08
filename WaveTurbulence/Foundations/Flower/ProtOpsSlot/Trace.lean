/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtOps.LinSynth
public import WaveTurbulence.Foundations.Regref.FourierAE
public import WaveTurbulence.Foundations.VineEst.VineEstS4c.TimeDiffRestr

/-! # PROT-OPS slots: the trace identity and the generic restriction bound

For `H` of finite `𝔛^{θ,0,0}` norm that is continuous in time, the synthesized output of the character atoms
`c(l) e(⟨y, ν l⟩) κ(y)` is `κ(y) H(φ y, v)` when `e(⟨φ y, l⟩) = c(l) e(⟨y, ν l⟩)`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.ProtOpsSlot

open WaveTurbulence.Flower.ProtOps

variable {n p : ℕ} {V : Type*}

theorem synth_eq_trace {θ : ℝ} (hθ0 : 0 ≤ θ) {κ : (Fin p → ℝ) → ℂ} {ν : (Fin n → ℝ) → (Fin p → ℝ)}
    {c : (Fin n → ℝ) → ℂ} {H : (Fin n → ℝ) → V → ℂ} (hH : mixedFourierNorm00 θ H < ⊤)
    (hcont : ∀ v, Continuous fun t => H t v) (φ : (Fin p → ℝ) → (Fin n → ℝ))
    (hφ : ∀ y l, (Real.fourierChar (timePairing n (φ y) l) : ℂ) =
      c l * (Real.fourierChar (timePairing p y (ν l)) : ℂ)) (y : Fin p → ℝ) (v : V) :
    synth (linAtom κ ν c) H y v = κ y * H (φ y) v := by
  have hk : Integrable (fun t => H t v) := integrable_of_mixedFourierNorm00_lt_top hH v
  have hhat : Integrable (timeFourier fun t => H t v) :=
    integrable_timeFourier_of_norm_lt_top hθ0
      ((timeFourierNorm_slice_le_mixedFourierNorm00 θ H v).trans_lt hH)
  have hinv := Regref.timeFourier_inversion_at hk hhat (φ y) (hcont v).continuousAt
  rw [← hinv]
  change _ = κ y * ∫ ξ, Real.fourierChar (-timePairing n ξ (-φ y)) • timeFourier (fun t => H t v) ξ
  rw [← integral_const_mul]
  unfold synth
  refine integral_congr_ae (ae_of_all _ fun l => ?_)
  have h1 : timePairing n l (φ y) = timePairing n (φ y) l := by
    simp [timePairing, dotProduct_comm]
  have h2 := hφ y l
  simp only [linAtom, Circle.smul_def, smul_eq_mul, map_neg, neg_neg, h1]
  rw [h2]; ring

/-- The generic restriction bound: an extension that is a.e. the synthesized character output. -/
theorem xnormRestr_le_of_ext {d : ℕ} {θ : ℝ} (hθ0 : 0 ≤ θ) (n p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℝ) (B : Set (Fin p → ℝ)), (∀ y ∈ B, ∀ i, q ≤ y i ∧ y i ≤ q + 1) →
      ∀ (K : Set (Mom d)) (F : (Fin p → ℝ) → Mom d → ℂ) (G : (Fin n → ℝ) → Mom d → ℂ)
        (ν : (Fin n → ℝ) → (Fin p → ℝ)), Continuous ν → (∀ l, timeBracket (ν l) ≤ 2 * timeBracket l) →
        ∀ (c : (Fin n → ℝ) → ℂ), Continuous c → (∀ l, ‖c l‖ ≤ 1) →
        (mixedFourierNorm00 θ G < ⊤ → ∃ E : (Fin p → ℝ) → Mom d → ℂ,
          (∀ y ∈ B, ∀ k ∈ K, E y k = F y k) ∧
          ∀ k, (fun y => E y k) =ᵐ[volume] fun y => synth (linAtom (cutK p q) ν c) G y k) →
        XNormRestr θ 0 0 B K F ≤ ENNReal.ofReal C * XNorm θ 0 0 G := by
  set c0 : ℝ≥0∞ := ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) * timeFourierNorm θ (cutK p 0) with hc0
  have hc0t : c0 < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
    (cutK_norm_lt_top p 0 θ)
  refine ⟨max 1 c0.toReal, le_trans zero_le_one (le_max_left _ _), fun q B hB K F G ν hν hν2 c hc hc1 hext => ?_⟩
  have hcle : c0 ≤ ENNReal.ofReal (max 1 c0.toReal) :=
    (ENNReal.ofReal_toReal hc0t.ne).symm.le.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))
  rw [NormBridgeScratch.XNorm_zero_eq_XNorm00, NormBridgeScratch.XNorm00_eq_mixedFourierNorm00]
  by_cases hG : mixedFourierNorm00 θ G < ⊤
  · obtain ⟨E, hE, hae⟩ := hext hG
    have h1 : XNormRestr θ 0 0 B K F ≤ XNorm θ 0 0 E := by
      unfold XNormRestr
      exact iInf_le_of_le E (iInf_le_of_le hE le_rfl)
    refine h1.trans ?_
    rw [NormBridgeScratch.XNorm_zero_eq_XNorm00, NormBridgeScratch.XNorm00_eq_mixedFourierNorm00,
      VineEstS4c.TimeDiff.mixedFourierNorm00_congr_ae θ hae]
    have h2 := linsynth_norm_le (n := n) (p := p) hθ0 (cutK_compact p q) (cutK_contDiff p q) hν hν2 hc hc1 hG
    rw [cutK_norm_eq p q θ] at h2
    exact h2.trans (mul_le_mul_left hcle _)
  · have : mixedFourierNorm00 θ G = ⊤ := not_lt_top_iff.1 hG
    rw [this, ENNReal.mul_top (by simp)]
    exact le_top

end WaveTurbulence.Flower.ProtOpsSlot
