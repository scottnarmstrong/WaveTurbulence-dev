/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.AnsatzPairResidualBound
public import WaveTurbulence.Foundations.XChain.AnsatzHigherResidual
public import WaveTurbulence.Foundations.XChain.SignatureParity
/-! Uniform actual input-cumulant error bound for every nonempty leaf block in the induction range. -/
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

theorem ansatz_unbalanced_input_residual_zero {w : ℕ} (sig : Fin w → ℤˣ)
    (hbal : ∑ j, (sig j : ℤ) ≠ 0) (n : Fin w → (Fin P.d → ℤ)) :
    cumulant (μ.restrict (Fev p)) (fun j ω => zpowSign (sig j) (a ω p (n j))) univ -
      lowerKernelSum P.L P.γ P.δ (inputsF P R) sig p (P.N p) n = 0 := by
  let t : Fin w → Icc (0 : ℝ) p := fun _ => ⟨p, Nat.cast_nonneg p, le_rfl⟩
  have hz := cumulant_signed_solution_eq_zero_of_unbalanced hL P.φin hG
    (Fev p) ha.1.1 ha.1.2.1 a (fun ω hω => (ha.1.2.2.2.2.1 ω hω).1) hrapid
    ha.1.2.2.2.2.2.1 t n sig univ hbal
  have hzero : cumulant (μ.restrict (Fev p)) (fun j ω => zpowSign (sig j) (a ω p (n j))) univ = 0 := hz
  rw [hzero, lowerKernelSum_unbalanced P.L P.γ P.δ (inputsF P R) sig p (P.N p) hbal n, sub_self]

theorem ansatz_input_residual_bound {w : ℕ} (hw : 1 ≤ w) (hR : w ≤ 2 * P.R p)
    (sig : Fin w → ℤˣ) (n : Fin w → (Fin P.d → ℤ)) :
    ‖cumulant (μ.restrict (Fev p)) (fun j ω => zpowSign (sig j) (a ω p (n j))) univ -
      lowerKernelSum P.L P.γ P.δ (inputsF P R) sig p (P.N p) n‖ ≤
      (∏ j, jbr (latticePoint P.L (n j))) ^ (-(P.Lambda p : ℝ) / 2) * Real.exp (-(P.N p : ℝ)) := by
  classical
  by_cases hbal : ∑ j, (sig j : ℤ) = 0
  · have heven : Even w := by
      simpa only [card_univ, Fintype.card_fin] using even_card_of_balanced_units sig univ hbal
    obtain ⟨m, hm⟩ := heven
    have he : w = 2 * m := by omega
    clear hm
    subst w
    by_cases hm1 : m = 1
    · subst m
      exact ansatz_pair_input_residual_bound P μ g hG hL a Fev R E Et p ha hrapid sig hbal n
    · have hm2 : 2 ≤ m := by omega
      have hmR : m ≤ P.R p := by omega
      have h := ansatz_higher_input_residual_bound P μ g a Fev R E Et p ha m hm2 hmR sig hbal n
      have hΛ : 0 ≤ (P.Lambda p : ℝ) := Nat.cast_nonneg _
      exact h.trans (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le (one_le_jbrProd P.L n) (by linarith)) (Real.exp_pos _).le)
  · rw [ansatz_unbalanced_input_residual_zero P μ g hG hL a Fev R E Et p ha hrapid sig hbal n, norm_zero]
    exact mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (one_le_jbrProd P.L n)) _) (Real.exp_pos _).le

end
end WaveTurbulence.Induct
