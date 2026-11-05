/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.CoefficientMassBudget
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickCorrectionSourceEnvelope

/-! # Uniform geometric masses for the actual tree NT and Wick profiles -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR

/-- The original weak Wick coefficient mass is contained in the same proved
positive source coefficient mass, with its actual4A Gevrey parameter. -/
theorem tree_wickCoefficientMass_le_local {n : ℕ} (J : Finset (Fin n))
    {η N A : ℝ} (hη : η ≤ 1-η/8) :
    (ENNReal.ofReal N*∑' k : ℕ, ENNReal.ofReal ((4*A)^k*((2*k).factorial:ℝ)/(4*k).factorial)) +
        (∫⁻ lam, wL η lam*ENNReal.ofReal (frequencyGaussian lam)) ≤ localCoefficientMass J η N (4*A) := by
  have hg : (∫⁻ lam, wL η lam*ENNReal.ofReal (frequencyGaussian lam)) ≤
      ∫⁻ lam, wL (1-η/8) lam*ENNReal.ofReal (frequencyGaussian lam) :=
    lintegral_mono (fun lam => mul_le_mul' (temporalWeight_mono hη lam) le_rfl)
  apply (add_le_add le_rfl hg).trans
  exact le_add_of_nonneg_left bot_le

/-- Enlarging the original scalar coefficient budget preserves its actual source premises. -/
theorem tree_SRep_mono_mass {ι : Type} [Fintype ι] {θ a b A N N' : ℝ}
    {C : (ι → ℝ) → ℝ × ℝ → ℂ} (hC : SRep θ a b A N C)
    (hA : 0 ≤ A) (hN : N ≤ N') : SRep θ a b A N' C := by
  refine ⟨hC.nonneg.trans hN,hC.reg,?_,?_⟩
  · intro k
    exact (hC.norm k).trans (gev_mono hN hA le_rfl (hC.nonneg.trans hN) k)
  · intro i
    exact (hC.wnorm i).trans (ENNReal.ofReal_le_ofReal hN)

/-- The literal J3 mass has a positive geometric majorant without any additional
sign assumption on the chosen representative of CTeta. -/
theorem tree_literal_coefficient_mass_le (c : ℝ) (n : ℕ) :
    c^(4*n+1) ≤ (max 1 |c|)^(4*n+1) := by
  calc
    _ ≤ |c^(4*n+1)| := le_abs_self _
    _ = |c|^(4*n+1) := abs_pow _ _
    _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) (le_max_right _ _) _

end WaveTurbulence.RegAsymp
