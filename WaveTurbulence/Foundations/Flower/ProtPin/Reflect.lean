/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TermLift

/-! # D3 PROT-PIN: time reflection and the lone-port clock alone (groundwork for the mirrored kink of (P1)/(trace))

* `timeFourier_comp_neg`, `timeFourierNorm_comp_neg`: `t ↦ f(-t)` has Fourier transform `ξ ↦ f̂(-ξ)` and the same
  weighted norm (the bracket weight is even, Lebesgue measure is reflection invariant).
* `rn_comp_neg_le`: the restricted norm of `f ∘ (-·)` on `B` is at most that of `f` on any set containing `-B`.
* `rn_lift2`: a function of the second clock alone, on a set inside `[p, p+1] × [q', q'+1]` (the mirror of `rn_lift`).

In (P1) with the root pinned at `t`, the kernel on the R176 box is `σ ↦ Σ_e c_e ∫_{max(σ,p)}^t e^{iπA_e(t-u)} W_e(t,u) du`
in the port clock `σ`; reflecting `u ↦ -u`, `σ ↦ -σ` turns it into the terminal operator of `kink_restr`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtPin

variable {r : ℕ}

theorem timeFourier_comp_neg (f : (Fin r → ℝ) → ℂ) (ξ : Fin r → ℝ) :
    timeFourier (fun t => f (-t)) ξ = timeFourier f (-ξ) := by
  unfold timeFourier VectorFourier.fourierIntegral
  conv_rhs => rw [← integral_neg_eq_self]
  congr 1
  funext v
  simp only [LinearMap.map_neg, LinearMap.neg_apply, neg_neg]

theorem timeBracket_neg (ξ : Fin r → ℝ) : timeBracket (-ξ) = timeBracket ξ := by
  unfold timeBracket
  simp only [Pi.neg_apply, neg_sq]

theorem timeWeight_neg (θ : ℝ) (ξ : Fin r → ℝ) : timeWeight θ (-ξ) = timeWeight θ ξ := by
  unfold timeWeight
  rw [timeBracket_neg]

/-- **Reflection invariance of the weighted Fourier norm.** -/
theorem timeFourierNorm_comp_neg (θ : ℝ) (f : (Fin r → ℝ) → ℂ) :
    timeFourierNorm θ (fun t => f (-t)) = timeFourierNorm θ f := by
  have hmp : MeasurePreserving (Neg.neg : (Fin r → ℝ) → (Fin r → ℝ)) volume volume :=
    Measure.measurePreserving_neg volume
  have hi : Integrable (fun t => f (-t)) ↔ Integrable f :=
    hmp.integrable_comp_emb (MeasurableEquiv.neg (Fin r → ℝ)).measurableEmbedding
  unfold timeFourierNorm
  rw [hi]
  split_ifs
  · simp only [timeFourier_comp_neg]
    rw [← lintegral_neg_eq_self (fun ξ => timeWeight θ ξ * ‖timeFourier f ξ‖ₑ)]
    simp only [timeWeight_neg]
  · rfl

/-- **The restricted norm under reflection.** -/
theorem rn_comp_neg_le (θ : ℝ) {B B' : Set (Fin r → ℝ)} (h : ∀ x ∈ B, -x ∈ B') (f : (Fin r → ℝ) → ℂ) :
    rn θ B (fun x => f (-x)) ≤ rn θ B' f := by
  conv_rhs => rw [rn_eq_iInf]
  refine le_iInf₂ fun g hg => ?_
  refine (rn_le θ (g := fun x => g (-x)) fun x hx => hg _ (h x hx)).trans ?_
  rw [timeFourierNorm_comp_neg]

/-- **Lift in the second clock**: a function of the second clock alone. -/
theorem rn_lift2 {θ : ℝ} (hθ : 0 ≤ θ) (p q' : ℝ) {B : Set (Fin 2 → ℝ)} (hB : B ⊆ timeBox p q')
    (f : (Fin 1 → ℝ) → ℂ) :
    rn θ B (fun ts => f (fun _ => ts 1)) ≤ cutNorm θ * rn θ (win q') f := by
  have key : ∀ g : (Fin 1 → ℝ) → ℂ, (∀ T ∈ win q', g T = f T) →
      rn θ B (fun ts => f (fun _ => ts 1)) ≤ cutNorm θ * timeFourierNorm θ g := by
    intro g hg
    refine (rn_le θ (g := fun ts => cut1 p (fun _ => ts 0) * g (fun _ => ts 1)) fun ts hts => ?_).trans ?_
    · rw [cut1_eq_one (hB hts).1, one_mul]
      exact hg _ (hB hts).2
    · refine (timeFourierNorm_tensor2_le hθ (cut1 p) g).trans ?_
      rw [cut1_norm]
  by_cases h0 : cutNorm θ = 0
  · refine (key f fun _ _ => rfl).trans ?_
    rw [h0, zero_mul]
    exact zero_le
  conv_rhs => rw [rn_eq_iInf]
  rw [ENNReal.mul_iInf_of_ne h0 (cutNorm_lt_top θ).ne]
  refine le_iInf fun g => ?_
  rw [ENNReal.mul_iInf_of_ne h0 (cutNorm_lt_top θ).ne]
  exact le_iInf fun hg => key g hg

end WaveTurbulence.Flower.ProtPin
