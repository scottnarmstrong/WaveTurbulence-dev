/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.ProperTruncSumCarrier
public import WaveTurbulence.Foundations.WaveB.FrozenB1
/-! The actual higher input-cumulant residual in cmattr has exactly the induction-hypothesis bound. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory

theorem ansatz_higher_input_residual_bound (P : WTParams) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (g : (Fin P.d → ℤ) → Ω → ℂ)
    (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω)
    (R : ℕ → Mom P.d → ℝ) (E : ℕ → (Fin P.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ)
    (p : ℕ) (ha : AnsatzAt P μ g a Fev R E Et p)
    (m : ℕ) (hm : 2 ≤ m) (hR : m ≤ P.R p) (sig : Fin (2 * m) → ℤˣ)
    (hbal : ∑ j, (sig j : ℤ) = 0) (n : Fin (2 * m) → (Fin P.d → ℤ)) :
    ‖cumulant (μ.restrict (Fev p)) (fun j ω => zpowSign (sig j) (a ω p (n j))) univ -
      lowerKernelSum P.L P.γ P.δ (inputsF P R) sig p (P.N p) n‖ ≤
      (∏ j, jbr (latticePoint P.L (n j))) ^ (-(P.Lambda p : ℝ)) * Real.exp (-(P.N p : ℝ)) := by
  have h := ha.2.2.2.1 m hm hR sig hbal n
  have he : cumulant (μ.restrict (Fev p)) (fun j ω => zpowSign (sig j) (a ω p (n j))) univ =
      (∑ N ∈ range (P.N p + 1), truncSum P (inputsF P R) p N p sig n) + Et p m sig n := h.1
  rw [lowerKernelSum_eq_sum_truncSum P (inputsF P R) sig p (by omega) n, he, add_sub_cancel_left]
  exact h.2.2

end WaveTurbulence.Induct
