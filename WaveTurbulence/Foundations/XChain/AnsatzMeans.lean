/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SignedGauge
public import WaveTurbulence.Foundations.XChain.SignedIntegrals
/-! Gauge symmetry gives zero actual input means on the approved rapid-decay good events. -/
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

theorem ansatz_input_mean_zero (n : Fin P.d → ℤ) : (∫ ω in Fev p, a ω p n ∂μ) = 0 := by
  let t : Fin 1 → Icc (0 : ℝ) p := fun _ => ⟨p, Nat.cast_nonneg p, le_rfl⟩
  have hz := cumulant_signed_solution_eq_zero_of_unbalanced (ι := Fin 1) hL P.φin hG
    (Fev p) ha.1.1 ha.1.2.1 a (fun ω hω => (ha.1.2.2.2.2.1 ω hω).1) hrapid
    ha.1.2.2.2.2.2.1 t (fun _ => n) (fun _ => (1 : ℤˣ)) {0} (by simp)
  simpa only [cumulant_singleton, zpowSign, ite_true, t] using hz

end
end WaveTurbulence.Induct
