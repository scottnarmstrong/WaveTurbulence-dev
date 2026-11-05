/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.AnsatzPairResidual
public import WaveTurbulence.Foundations.XChain.JbrBounds
/-! The diagonal E_p error gives half the source exponent at each of the two input leaves. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory Set

theorem ansatz_pair_input_residual_bound (P : WTParams) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (g : (Fin P.d → ℤ) → Ω → ℂ)
    (hG : IsGaussianData μ g) (hL : 0 < P.L)
    (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω)
    (R : ℕ → Mom P.d → ℝ) (E : ℕ → (Fin P.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ)
    (p : ℕ) (ha : AnsatzAt P μ g a Fev R E Et p)
    (hrapid : ∀ ω ∈ Fev p, IsRapidDecay (initialCoeff P.L P.φin g ω))
    (sig : Fin 2 → ℤˣ) (hbal : ∑ j, (sig j : ℤ) = 0) (n : Fin 2 → (Fin P.d → ℤ)) :
    ‖cumulant (μ.restrict (Fev p)) (fun j ω => zpowSign (sig j) (a ω p (n j))) univ -
      lowerKernelSum P.L P.γ P.δ (inputsF P R) sig p (P.N p) n‖ ≤
      (∏ j, jbr (latticePoint P.L (n j))) ^ (-(P.Lambda p : ℝ) / 2) * Real.exp (-(P.N p : ℝ)) := by
  rw [ansatz_pair_input_residual_eq P μ g hG hL a Fev R E Et p ha hrapid sig hbal n]
  by_cases hn : n 0 = n 1
  · rw [ite_eq_left hn, jbrProd_pair_rpow_half P.L n hn, Complex.norm_real, Real.norm_eq_abs]
    exact ha.2.1.2.1 (n 0)
  · rw [ite_eq_right hn, norm_zero]
    exact mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (one_le_jbrProd P.L n)) _) (Real.exp_pos _).le

end WaveTurbulence.Induct
