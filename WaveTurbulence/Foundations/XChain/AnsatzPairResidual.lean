/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.AnsatzMeans
public import WaveTurbulence.Foundations.XChain.SignedPairCovariance
/-! The actual two-point cmattr input residual is precisely the source E_p diagonal error. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory Set

section
variable (P : WTParams) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : (Fin P.d → ℤ) → Ω → ℂ) (hG : IsGaussianData μ g) (hL : 0 < P.L)
    (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω)
    (R : ℕ → Mom P.d → ℝ) (E : ℕ → (Fin P.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ)
    (p : ℕ) (ha : AnsatzAt P μ g a Fev R E Et p)
    (hrapid : ∀ ω ∈ Fev p, IsRapidDecay (initialCoeff P.L P.φin g ω))
include hG hL ha hrapid

theorem ansatz_pair_input_residual_eq (sig : Fin 2 → ℤˣ) (hbal : ∑ j, (sig j : ℤ) = 0)
    (n : Fin 2 → (Fin P.d → ℤ)) :
    cumulant (μ.restrict (Fev p)) (fun j ω => zpowSign (sig j) (a ω p (n j))) univ -
      lowerKernelSum P.L P.γ P.δ (inputsF P R) sig p (P.N p) n =
      if n 0 = n 1 then (E p (n 0) : ℂ) else 0 := by
  have hc := cumulant_signed_pair_of_covariance (μ.restrict (Fev p)) (fun ω n => a ω p n)
    (fun n => P.φ (P.δ * p) (latticePoint P.L n) + R p (latticePoint P.L n) + E p n)
    ha.2.1.2.2 (ansatz_input_mean_zero P μ g hG hL a Fev R E Et p ha hrapid) sig hbal n
  rw [hc, lowerKernelSum_pair P.L P.γ P.δ (inputsF P R) sig (neg_sig_one_of_balanced_two sig hbal)]
  by_cases h : n 0 = n 1
  · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h]
    unfold inputsF
    push_cast
    ring
  · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h, sub_self]

end
end WaveTurbulence.Induct
