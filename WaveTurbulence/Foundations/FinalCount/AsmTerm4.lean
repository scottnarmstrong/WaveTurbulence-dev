/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTerm3
public import WaveTurbulence.Foundations.FinalCount.AsmPotW
/-! **FINALCOUNT-ASSEMBLY, `hterm` part 4: the ENNReal glue.**  `Q ≤ I · ∏ C_a`, `I = ∏_K L^{exK}`, `C_a ≤ A_a L^{exa}`, `∏ A_a ≤ 1/ap`,
`Σ exK + Σ exa ≤ Ey` give `Q ≤ L^{Ey}/ap`; and the form of `WPot`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm

theorem term_glue {ι κ : Type*} (𝒦 : Finset ι) (R : Finset κ) (exK : ι → ℝ) (A exa : κ → ℝ) (C : κ → ℝ≥0∞) {Q : ℝ≥0∞}
    {L ap Ey : ℝ} (hL1 : 1 ≤ L) (hap : 0 < ap) (hA : ∀ a ∈ R, 0 ≤ A a)
    (hQ : Q ≤ (∏ K ∈ 𝒦, ENNReal.ofReal (L ^ exK K)) * ∏ a ∈ R, C a)
    (hC : ∀ a ∈ R, C a ≤ ENNReal.ofReal (A a * L ^ exa a))
    (hAp : ∏ a ∈ R, A a ≤ ap⁻¹) (hexp : ∑ K ∈ 𝒦, exK K + ∑ a ∈ R, exa a ≤ Ey) :
    Q ≤ ENNReal.ofReal (L ^ Ey / ap) := by
  have hL : 0 < L := by linarith
  refine hQ.trans ?_
  have h1 : ∏ a ∈ R, C a ≤ ∏ a ∈ R, ENNReal.ofReal (A a * L ^ exa a) := Finset.prod_le_prod' hC
  have h2 : ∏ a ∈ R, ENNReal.ofReal (A a * L ^ exa a) = ENNReal.ofReal (∏ a ∈ R, (A a * L ^ exa a)) :=
    (ENNReal.ofReal_prod_of_nonneg fun a ha => mul_nonneg (hA a ha) (by positivity)).symm
  have h3 : ∏ K ∈ 𝒦, ENNReal.ofReal (L ^ exK K) = ENNReal.ofReal (∏ K ∈ 𝒦, L ^ exK K) :=
    (ENNReal.ofReal_prod_of_nonneg fun K _ => by positivity).symm
  calc (∏ K ∈ 𝒦, ENNReal.ofReal (L ^ exK K)) * ∏ a ∈ R, C a
      ≤ (∏ K ∈ 𝒦, ENNReal.ofReal (L ^ exK K)) * ∏ a ∈ R, ENNReal.ofReal (A a * L ^ exa a) := by gcongr
    _ = ENNReal.ofReal ((∏ K ∈ 𝒦, L ^ exK K) * ∏ a ∈ R, (A a * L ^ exa a)) := by
        rw [h2, h3, ← ENNReal.ofReal_mul (Finset.prod_nonneg fun K _ => by positivity)]
    _ ≤ ENNReal.ofReal (L ^ Ey / ap) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hL, ← Real.rpow_sum_of_pos hL]
        have hLs : L ^ (∑ K ∈ 𝒦, exK K) * L ^ (∑ a ∈ R, exa a) ≤ L ^ Ey := by
          rw [← Real.rpow_add hL]
          exact Real.rpow_le_rpow_of_exponent_le hL1 hexp
        have hP0 : 0 ≤ ∏ a ∈ R, A a := Finset.prod_nonneg hA
        calc L ^ (∑ K ∈ 𝒦, exK K) * ((∏ a ∈ R, A a) * L ^ (∑ a ∈ R, exa a))
            = (L ^ (∑ K ∈ 𝒦, exK K) * L ^ (∑ a ∈ R, exa a)) * ∏ a ∈ R, A a := by ring
          _ ≤ L ^ Ey * ap⁻¹ := mul_le_mul hLs hAp hP0 (by positivity)
          _ = L ^ Ey / ap := by rw [div_eq_mul_inv]

end WaveTurbulence.FinalCountAsm
