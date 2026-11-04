/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceCoreUntouched
public import WaveTurbulence.Foundations.Sumint.TouchedCoreProductBound
public import WaveTurbulence.Foundations.Sumint.CorePowerBudget

/-!
# Conditional numerical product reduction for fixed and free source cores

This helper accepts full-mass budgets explicitly. The actual source
budgets are supplied separately by exists_source_all_core_budgets.
Untouched masses keep their Lebesgue estimates; at most eight touched
inputs pay the crude fixed-time cost. Budgets at least one can be
inserted without dividing by any source mass.
-/

public section
open MeasureTheory Set ENNReal
open scoped Classical
namespace WaveTurbulence.Sumint

/-- Conditional fixed/free product reduction from explicit full core budgets. -/
theorem prod_sourceCore_mixed_le_of_full_budgets {d : ℕ} (D : SumintDatum d)
    {A G L γ δ η : ℝ} {N : ℕ} (hD : D.Admissible A L γ η N) (hd : 2 ≤ d)
    (hG : 1 ≤ G) (hL : 1 ≤ L) (hγ : γ ∈ Ioo (0:ℝ) 1) (hδ : δ ∈ Ioc (0:ℝ) 1)
    (hη : 0 ≤ 1-3*η) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d)
    (r : Mom d) (hr : ‖r‖ ≤ 1) (t c : ℝ) {h : ℝ} (hh : h ≤ 1)
    (s : Finset D.S.TVar) (hs : s.card ≤ 2) (x : D.S.TVar → ℝ)
    (hfull : ∀ b : FactorIdx D.S, (∫⁻ z, sourceCoreNormFactor D L γ δ η p ν r t c h b z) ≤
      ENNReal.ofReal (sourceCorePowerBudget D G L γ δ b)) :
    (∏ b : FactorIdx D.S, ∫⁻ z, sourceCoreNormFactor D L γ δ η p ν r t c h b z
      ∂Measure.pi (fun j => fixedCoordinateMeasure (s:Set D.S.TVar) x (sourceCoreCoordinateTimeEquiv D ⟨b,j⟩))) ≤
      (ENNReal.ofReal (3*max 1 (((N:ℝ)+2)^(1-3*η))*(8*L+1)^d))^8 *
        ∏ b : FactorIdx D.S, ENNReal.ofReal (sourceCorePowerBudget D G L γ δ b) := by
  rw [← Finset.prod_mul_prod_compl (sourceExitCores D s)]
  apply mul_le_mul' (prod_touchedCore_fixed_count_le D hD hL hη δ p ν r hr t c hh s hs x)
  calc
    _ ≤ ∏ b ∈ (sourceExitCores D s)ᶜ, ENNReal.ofReal (sourceCorePowerBudget D G L γ δ b) := by
      apply Finset.prod_le_prod
      intro b hb
      rw [lintegral_sourceCore_untouched_eq D L γ δ η p ν r t c h s x b (Finset.mem_compl.mp hb)]
      exact hfull b
    _ ≤ _ := Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _) (fun b _ _ => by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (one_le_sourceCorePowerBudget D hd hG hL hγ hδ b))

end WaveTurbulence.Sumint
