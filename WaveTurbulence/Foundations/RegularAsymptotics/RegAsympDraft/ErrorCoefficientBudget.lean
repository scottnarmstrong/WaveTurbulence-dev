/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.CoefficientMassBudget

/-! # A common geometric budget for the actual NT and Wick coefficient masses -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR
open scoped ENNReal

/-- The actual Wick derivative/normalizer mass, including its factor4^n,
has a geometric bound before any logarithmic order exponent is chosen. -/
theorem wickCoefficientMass_le_geometric {n : ℕ} (hn : 0 < n)
    {η A Cbase : ℝ} (hη : η ≤ 1) (hA : 0 ≤ A) (hCbase : 1 ≤ Cbase) :
    (4:ℝ≥0∞)^n*((ENNReal.ofReal (Cbase^(4*n+1))*∑' k : ℕ,
      ENNReal.ofReal ((4*A)^k*((2*k).factorial:ℝ)/(4*k).factorial)) +
      (∫⁻ lam, wL η lam*ENNReal.ofReal (frequencyGaussian lam))) ≤
    ENNReal.ofReal (4*(3*(1+2*coefficientGevreyMass (4*A)+gaussianWeightedMass η)*Cbase^5))^n := by
  have hU := coefficientGevreyMass_nonneg (by positivity : 0 ≤ 4*A)
  have hV := gaussianWeightedMass_nonneg η
  have hbase : 0 ≤ Cbase := zero_le_one.trans hCbase
  have hN : 0 ≤ Cbase^(4*n+1) := pow_nonneg hbase _
  rw [← ofReal_coefficientGevreyMass (by positivity : 0 ≤ 4*A),← ofReal_gaussianWeightedMass hη,
    ← ENNReal.ofReal_mul hN,← ENNReal.ofReal_add (mul_nonneg hN hU) hV]
  have hb : Cbase^(4*n+1)*coefficientGevreyMass (4*A)+gaussianWeightedMass η ≤
      (3*(1+2*coefficientGevreyMass (4*A)+gaussianWeightedMass η)*Cbase^5)^n := by
    apply le_trans _ (coefficient_mass_le_geometric hn hU hV hCbase)
    apply add_le_add _ le_rfl
    rw [mul_comm (Cbase^(4*n+1))]
    exact mul_le_mul_of_nonneg_right (by linarith only [hU,(Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ))] : coefficientGevreyMass (4*A) ≤
      (n:ℝ)+2*coefficientGevreyMass (4*A)) hN
  calc
    _ ≤ (4:ℝ≥0∞)^n*ENNReal.ofReal ((3*(1+2*coefficientGevreyMass (4*A)+gaussianWeightedMass η)*Cbase^5)^n) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hb)
    _ = _ := by
      rw [ENNReal.ofReal_pow (by positivity),← mul_pow,
        ← ENNReal.ofReal_ofNat 4,← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]

/-- Both explicit source coefficient masses fit one constant independent
of the order and of its logarithmic growth exponent. -/
theorem exists_common_errorCoefficientMass_bound {η A Cbase : ℝ}
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hA : 0 ≤ A) (hCbase : 1 ≤ Cbase) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ J : Finset (Fin n),
      localCoefficientMass J η (Cbase^(4*n+1)) A ≤ ENNReal.ofReal C^n ∧
      (4:ℝ≥0∞)^n*((ENNReal.ofReal (Cbase^(4*n+1))*∑' k : ℕ,
        ENNReal.ofReal ((4*A)^k*((2*k).factorial:ℝ)/(4*k).factorial)) +
        (∫⁻ lam, wL η lam*ENNReal.ofReal (frequencyGaussian lam))) ≤ ENNReal.ofReal C^n := by
  let CN := 3*(1+2*coefficientGevreyMass A+
    (gaussianWeightedMass (η/4)+gaussianWeightedMass (1-η/8)))*Cbase^5
  let CW := 4*(3*(1+2*coefficientGevreyMass (4*A)+gaussianWeightedMass η)*Cbase^5)
  refine ⟨max 1 (max CN CW),le_max_left _ _,?_⟩
  intro n hn J
  constructor
  · exact (localCoefficientMass_le_geometric hn J hη0 (by linarith) hA hCbase).trans
      (pow_le_pow_left₀ (by positivity) (ENNReal.ofReal_le_ofReal
        ((le_max_left CN CW).trans (le_max_right _ _))) n)
  · exact (wickCoefficientMass_le_geometric hn hη hA hCbase).trans
      (pow_le_pow_left₀ (by positivity) (ENNReal.ofReal_le_ofReal
        ((le_max_right CN CW).trans (le_max_right _ _))) n)

end WaveTurbulence.RegAsymp
