/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LocalTimeRestriction
public import WaveTurbulence.Foundations.RegAsymp.CoefficientOrderBudget
import Mathlib.Tactic

/-! # Finite real coefficient masses and their geometric half-order budget -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR
open scoped ENNReal

/-- The fixed real mass of the derivative envelope. -/
def coefficientGevreyMass (A : ℝ) : ℝ :=
  ∑' k : ℕ, A^k*((2*k).factorial:ℝ)/(4*k).factorial

/-- The fixed real Gaussian contribution to the positive normalizer. -/
def gaussianWeightedMass (a : ℝ) : ℝ :=
  (∫⁻ lam, wL a lam*ENNReal.ofReal (frequencyGaussian lam)).toReal

theorem coefficientGevreyMass_nonneg {A : ℝ} (hA : 0 ≤ A) : 0 ≤ coefficientGevreyMass A :=
  tsum_nonneg (fun _ => by positivity)

theorem gaussianWeightedMass_nonneg (a : ℝ) : 0 ≤ gaussianWeightedMass a := ENNReal.toReal_nonneg

/-- The actual ENNReal derivative mass is the finite real series. -/
theorem ofReal_coefficientGevreyMass {A : ℝ} (hA : 0 ≤ A) :
    ENNReal.ofReal (coefficientGevreyMass A) =
      ∑' k : ℕ, ENNReal.ofReal (A^k*((2*k).factorial:ℝ)/(4*k).factorial) :=
  ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) (summable_gevrey_ratio A hA)

theorem ofReal_gaussianWeightedMass {a : ℝ} (ha : a ≤ 1) :
    ENNReal.ofReal (gaussianWeightedMass a) =
      ∫⁻ lam, wL a lam*ENNReal.ofReal (frequencyGaussian lam) :=
  ENNReal.ofReal_toReal (lintegral_wL_frequencyGaussian_lt_top ha).ne

/-- Exact real expression for the two common coefficient masses. -/
theorem localCoefficientMass_eq_ofReal {n : ℕ} (J : Finset (Fin n)) {η N A : ℝ}
    (hη0 : 0 ≤ η) (hη : η ≤ 4) (hN : 0 ≤ N) (hA : 0 ≤ A) :
    localCoefficientMass J η N A =
      ENNReal.ofReal (((2*coefficientGevreyMass A+
        (Fintype.card {j : Fin n // j ∉ J}:ℝ))*N)+
          (gaussianWeightedMass (η/4)+gaussianWeightedMass (1-η/8))) := by
  have hu := coefficientGevreyMass_nonneg hA
  have hv0 := gaussianWeightedMass_nonneg (η/4)
  have hv1 := gaussianWeightedMass_nonneg (1-η/8)
  rw [ENNReal.ofReal_add (by positivity) (add_nonneg hv0 hv1),
    ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),ENNReal.ofReal_ofNat,
    ENNReal.ofReal_natCast,ENNReal.ofReal_add hv0 hv1,
    ofReal_coefficientGevreyMass hA,
    ofReal_gaussianWeightedMass (by linarith : η/4 ≤ 1),
    ofReal_gaussianWeightedMass (by linarith : 1-η/8 ≤ 1)]
  unfold localCoefficientMass
  ring

/-- The source coefficient mass has a uniform geometric half-order budget,
including J3's extra constant exponent and both positive normalizers. -/
theorem localCoefficientMass_le_geometric {n : ℕ} (hn : 0 < n) (J : Finset (Fin n))
    {η A Cbase : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 4) (hA : 0 ≤ A) (hCbase : 1 ≤ Cbase) :
    localCoefficientMass J η (Cbase^(4*n+1)) A ≤
      ENNReal.ofReal (3*(1+2*coefficientGevreyMass A+
        (gaussianWeightedMass (η/4)+gaussianWeightedMass (1-η/8)))*Cbase^5)^n := by
  have hu := coefficientGevreyMass_nonneg hA
  have hv0 := gaussianWeightedMass_nonneg (η/4)
  have hv1 := gaussianWeightedMass_nonneg (1-η/8)
  have hCpos : 0 ≤ Cbase := zero_le_one.trans hCbase
  have hN : 0 ≤ Cbase^(4*n+1) := pow_nonneg hCpos _
  rw [localCoefficientMass_eq_ofReal J hη0 hη hN hA,
    ← ENNReal.ofReal_pow (by positivity : 0 ≤ 3*(1+2*coefficientGevreyMass A+
      (gaussianWeightedMass (η/4)+gaussianWeightedMass (1-η/8)))*Cbase^5)]
  apply ENNReal.ofReal_le_ofReal
  have hcard : (Fintype.card {j : Fin n // j ∉ J}:ℝ) ≤ (n:ℝ) := by
    exact_mod_cast (Fintype.card_subtype_le (fun j : Fin n => j ∉ J)).trans_eq (Fintype.card_fin n)
  have hh := coefficient_mass_le_geometric hn (coefficientGevreyMass_nonneg hA)
    (add_nonneg hv0 hv1) hCbase
  apply le_trans _ hh
  exact add_le_add (mul_le_mul_of_nonneg_right
    (by linarith : 2*coefficientGevreyMass A+(Fintype.card {j : Fin n // j ∉ J}:ℝ) ≤
      (n:ℝ)+2*coefficientGevreyMass A) hN) le_rfl

end WaveTurbulence.RegAsymp
