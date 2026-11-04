/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Layered.ParamFinite
public import WaveTurbulence.Frozen.Defs.Mom

/-!
# Momentum regularity of inverse time-Fourier integrals

For a frequency function `Ĝ(λ, k)` (`λ ∈ ℝ^r`, `k ∈ ℝ^d`) that is `C^N` in `k` for every `λ`, strongly
measurable in `λ`, and whose weighted iterated `k`-derivatives are dominated by integrable functions
`S_j(λ)` of the frequency, `w(k) ‖D^j_k Ĝ(λ, k)‖ ≤ S_j(λ)` with a weight `w ≥ 1`, the inverse
time-Fourier integral

`g(t, k) = ∫ Ĝ(λ, k) e^{2πi⟨λ, t⟩} dλ`

is `C^N` in `k` (`contDiff_invTimeFourier`), and its weighted iterated derivatives are bounded by the
integrals of the dominating functions (`weight_mul_norm_iteratedFDeriv_invTimeFourier_le`). This is the
momentum part of the point trace of TARGET's weighted Fourier norms `𝔛^{θ,Λ₁,Λ₂}` (TARGET (normX),
L581): the supremum over `k` sits inside the frequency integral.
-/

public section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace WaveTurbulence.Layered

variable {r d : ℕ}

/-- The phase `e^{2πi⟨λ, t⟩}`. -/
noncomputable def timePhase (t lam : Fin r → ℝ) : ℂ :=
  Complex.exp ((2 * Real.pi * ∑ i, lam i * t i : ℝ) * Complex.I)

theorem norm_timePhase (t lam : Fin r → ℝ) : ‖timePhase t lam‖ = 1 := by
  unfold timePhase
  exact Complex.norm_exp_ofReal_mul_I _

/-- The inverse time-Fourier integral. -/
noncomputable def invTimeFourier (Ghat : (Fin r → ℝ) → Mom d → ℂ) (t : Fin r → ℝ) (k : Mom d) : ℂ :=
  ∫ lam, Ghat lam k * timePhase t lam

theorem iteratedFDeriv_const_mul_param {N : ℕ} {h : Mom d → ℂ} (hh : ContDiff ℝ N h) (c : ℂ)
    {j : ℕ} (hj : j ≤ N) (k : Mom d) :
    iteratedFDeriv ℝ j (fun k => h k * c) k = c • iteratedFDeriv ℝ j h k := by
  have : (fun k => h k * c) = fun k => c • h k := by funext k; rw [smul_eq_mul, mul_comm]
  rw [this]
  exact iteratedFDeriv_const_smul_apply' (hh.contDiffAt.of_le (by exact_mod_cast hj))

variable {N : ℕ} {Ghat : (Fin r → ℝ) → Mom d → ℂ}

theorem invTimeFourier_hyps (hC : ∀ lam, ContDiff ℝ N (Ghat lam))
    (hm : ∀ k, StronglyMeasurable fun lam => Ghat lam k)
    (w : Mom d → ℝ) (hw : ∀ k, 1 ≤ w k) (S : ℕ → (Fin r → ℝ) → ℝ)
    (hSi : ∀ j ≤ N, Integrable (S j))
    (hS : ∀ j ≤ N, ∀ lam k, w k * ‖iteratedFDeriv ℝ j (Ghat lam) k‖ ≤ S j lam) (t : Fin r → ℝ) :
    (∀ lam, ContDiff ℝ N (fun k => Ghat lam k * timePhase t lam)) ∧
    (∀ j ≤ N, ∀ k, AEStronglyMeasurable
      (fun lam => iteratedFDeriv ℝ j (fun k => Ghat lam k * timePhase t lam) k) volume) ∧
    (∀ j ≤ N, ∃ B : (Fin r → ℝ) → ℝ, Integrable B volume ∧
      ∀ᵐ lam, ∀ k, ‖iteratedFDeriv ℝ j (fun k => Ghat lam k * timePhase t lam) k‖ ≤ B lam) := by
  have hC' : ∀ lam, ContDiff ℝ N (fun k => Ghat lam k * timePhase t lam) := fun lam =>
    (hC lam).mul contDiff_const
  have hphase : StronglyMeasurable fun lam : Fin r → ℝ => timePhase t lam := by
    unfold timePhase
    exact (Continuous.stronglyMeasurable (by fun_prop))
  refine ⟨hC', fun j hj k => ?_, fun j hj => ⟨S j, hSi j hj, Eventually.of_forall fun lam k => ?_⟩⟩
  · have := stronglyMeasurable_iteratedFDeriv_param_of_le (f := fun k lam => Ghat lam k * timePhase t lam)
      hC' (fun k => (hm k).mul hphase) j hj k
    exact this.aestronglyMeasurable
  · rw [iteratedFDeriv_const_mul_param (hC lam) _ hj, norm_smul, norm_timePhase, one_mul]
    have h1 := hS j hj lam k
    have h0 : 0 ≤ ‖iteratedFDeriv ℝ j (Ghat lam) k‖ := norm_nonneg _
    nlinarith [hw k]

/-- **The inverse time-Fourier integral is `C^N` in the momentum.** -/
theorem contDiff_invTimeFourier (hC : ∀ lam, ContDiff ℝ N (Ghat lam))
    (hm : ∀ k, StronglyMeasurable fun lam => Ghat lam k)
    (w : Mom d → ℝ) (hw : ∀ k, 1 ≤ w k) (S : ℕ → (Fin r → ℝ) → ℝ)
    (hSi : ∀ j ≤ N, Integrable (S j))
    (hS : ∀ j ≤ N, ∀ lam k, w k * ‖iteratedFDeriv ℝ j (Ghat lam) k‖ ≤ S j lam) (t : Fin r → ℝ) :
    ContDiff ℝ N (invTimeFourier Ghat t) := by
  obtain ⟨h1, h2, h3⟩ := invTimeFourier_hyps hC hm w hw S hSi hS t
  exact contDiff_integral_param_of_le (μ := volume) h1 h2 h3

/-- **Weighted momentum derivatives of the inverse time-Fourier integral** are bounded by the integrals
of the dominating functions. -/
theorem weight_mul_norm_iteratedFDeriv_invTimeFourier_le (hC : ∀ lam, ContDiff ℝ N (Ghat lam))
    (hm : ∀ k, StronglyMeasurable fun lam => Ghat lam k)
    (w : Mom d → ℝ) (hw : ∀ k, 1 ≤ w k) (S : ℕ → (Fin r → ℝ) → ℝ)
    (hSi : ∀ j ≤ N, Integrable (S j))
    (hS : ∀ j ≤ N, ∀ lam k, w k * ‖iteratedFDeriv ℝ j (Ghat lam) k‖ ≤ S j lam) (t : Fin r → ℝ)
    {j : ℕ} (hj : j ≤ N) (k : Mom d) :
    w k * ‖iteratedFDeriv ℝ j (invTimeFourier Ghat t) k‖ ≤ ∫ lam, S j lam := by
  obtain ⟨h1, h2, h3⟩ := invTimeFourier_hyps hC hm w hw S hSi hS t
  have he := iteratedFDeriv_integral_param_of_le (μ := volume) h1 h2 h3 j hj
  have hw0 : 0 ≤ w k := le_trans zero_le_one (hw k)
  unfold invTimeFourier
  rw [he]
  calc w k * ‖∫ lam, iteratedFDeriv ℝ j (fun k => Ghat lam k * timePhase t lam) k‖
      ≤ w k * ∫ lam, ‖iteratedFDeriv ℝ j (fun k => Ghat lam k * timePhase t lam) k‖ := by
        gcongr
        exact norm_integral_le_integral_norm _
    _ = ∫ lam, w k * ‖iteratedFDeriv ℝ j (fun k => Ghat lam k * timePhase t lam) k‖ :=
        (integral_const_mul _ _).symm
    _ ≤ ∫ lam, S j lam := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => by positivity) (hSi j hj)
          (Eventually.of_forall fun lam => ?_)
        show w k * ‖iteratedFDeriv ℝ j (fun k => Ghat lam k * timePhase t lam) k‖ ≤ S j lam
        rw [iteratedFDeriv_const_mul_param (hC lam) _ hj, norm_smul, norm_timePhase, one_mul]
        exact hS j hj lam k

end WaveTurbulence.Layered
