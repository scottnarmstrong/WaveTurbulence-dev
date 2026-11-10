/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTerm10
/-! **FINALCOUNT-ASSEMBLY, `hterm` part 12: the cluster exponents add up.** -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

/-- The exponent of `clusterRHSs` for one cluster. -/
noncomputable def exK (γ η C₀ : ℝ) (m e : ℕ) (j : ℤ) : ℝ :=
  -η ^ 3 - 3 * η + eraseA γ η * ((m : ℝ) - j) - η * e - C₀ * η ^ 5 * ((m : ℝ) + e)

theorem clusterRHSs_eq (L γ η C₀ : ℝ) (m e : ℕ) (j : ℤ) : clusterRHSs L γ η C₀ m e j = L ^ exK γ η C₀ m e j := rfl

theorem sum_exK {ι : Type*} (𝒦 : Finset ι) (γ η C₀ : ℝ) (cK eK : ι → ℕ) (jK : ι → ℤ) :
    ∑ K ∈ 𝒦, exK γ η C₀ (cK K) (eK K) (jK K) =
      -(η ^ 3 + 3 * η) * (𝒦.card : ℝ) + eraseA γ η * ((∑ K ∈ 𝒦, (cK K : ℝ)) - ∑ K ∈ 𝒦, (jK K : ℝ)) -
        η * ∑ K ∈ 𝒦, (eK K : ℝ) - C₀ * η ^ 5 * ((∑ K ∈ 𝒦, (cK K : ℝ)) + ∑ K ∈ 𝒦, (eK K : ℝ)) := by
  unfold exK
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  ring

end WaveTurbulence.FinalCountAsm
