/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SchwartzBracketBound
/-! The induction spatial norm supplies the two-point input bound without a new gate. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory

theorem theta_nonneg (P : WTParams) (p : ℕ) : 0 ≤ P.theta p := by
  unfold WTParams.theta
  positivity

theorem ansatz_inputsF_bracket_bound (P : WTParams) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (g : (Fin P.d → ℤ) → Ω → ℂ)
    (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω)
    (R : ℕ → Mom P.d → ℝ) (E : ℕ → (Fin P.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ)
    (p : ℕ) (ha : AnsatzAt P μ g a Fev R E Et p) (hL : 1 ≤ P.L)
    (C : ℝ) (hφ : ∀ k, |P.φ (P.δ * p) k| ≤ C * jbr k ^ (-(P.Lambda p : ℝ))) :
    ∀ k, |inputsF P R p k| ≤ (C + 1) * jbr k ^ (-(P.Lambda p : ℝ)) := by
  intro k
  have hRp := SNormR_pointwise (R p) (P.L ^ (-P.theta p))
    (Real.rpow_nonneg (zero_le_one.trans hL) _) ha.2.1.1 k
  have hscale : P.L ^ (-P.theta p) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL (neg_nonpos.mpr (theta_nonneg P p))
  have hR : |R p k| ≤ jbr k ^ (-(P.Lambda p : ℝ)) :=
    hRp.trans (by
      simpa only [one_mul] using (mul_le_mul_of_nonneg_right hscale
        (Real.rpow_nonneg (jbr_pos k).le _)))
  change |P.φ (P.δ * p) k + R p k| ≤ _
  exact (abs_add_le _ _).trans (by
    have h := hφ k
    change |P.φ (P.δ * p) k| + |R p k| ≤ _
    nlinarith)

end WaveTurbulence.Induct
