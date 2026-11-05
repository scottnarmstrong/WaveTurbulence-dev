/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Final3a
import Mathlib.Tactic
/-! The class bound as the `ofReal` of an explicit real number. -/
@[expose] public section
open Finset MeasureTheory
open scoped ENNReal
namespace WaveTurbulence.Ladder
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDisjoint
open scoped Classical

theorem classReal_eq {Q : Type} [Fintype Q] (K : Q → ℕ) (ρ : Q → ℝ) (Dt Kc _π3 : ℝ) (n m : ℕ) (pin : ℝ) :
    (2 : ℝ) ^ (∑ S, K S) * ((∏ s : (Σ S : Q, Fin (K S)), 2 * ρ s.1) *
      ((∏ S, 2 ^ (K S) * Dt ^ (K S) / (Nat.factorial (K S) : ℝ)) * (pin ^ n * 3 ^ m) * (2 * Kc) ^ m)) =
    (∏ S, (8 * ρ S * Dt) ^ (K S) / (Nat.factorial (K S) : ℝ)) * pin ^ n * (3 * (2 * Kc)) ^ m := by
  have h1 : ∏ s : (Σ S : Q, Fin (K S)), 2 * ρ s.1 = ∏ S, (2 * ρ S) ^ (K S) := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl (fun S _ => ?_)
    simp
  have h2 : (2 : ℝ) ^ (∑ S, K S) = ∏ S, (2 : ℝ) ^ (K S) := by
    rw [Finset.prod_pow_eq_pow_sum]
  have h3 : (∏ S, (8 * ρ S * Dt) ^ (K S) / (Nat.factorial (K S) : ℝ)) =
      (∏ S, (2 : ℝ) ^ (K S)) * (∏ S, (2 * ρ S) ^ (K S)) * ∏ S, 2 ^ (K S) * Dt ^ (K S) / (Nat.factorial (K S) : ℝ) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun S _ => ?_)
    rw [show 8 * ρ S * Dt = 2 * (2 * ρ S) * (2 * Dt) from by ring]
    rw [mul_pow, mul_pow, mul_pow, mul_pow]; ring
  rw [h1, h2, h3, mul_pow 3]
  ring

theorem class_E_eq {Q : Type} [Fintype Q] (K : Q → ℕ) (ρ : Q → ℝ) (hρ : ∀ S, 0 ≤ ρ S) (Dt Kc : ℝ)
    (hDt : 0 ≤ Dt) (hKc : 0 ≤ Kc) (n : ℕ) :
    (2 : ℝ≥0∞) ^ Fintype.card (Σ S : Q, Fin (K S)) *
      ((∏ s : (Σ S : Q, Fin (K S)), ENNReal.ofReal (2 * ρ s.1)) *
        ((∏ S, ENNReal.ofReal (2 ^ (K S) * Dt ^ (K S) / (Nat.factorial (K S) : ℝ))) *
          ENNReal.ofReal (Real.pi ^ n * 3 ^ (n - Fintype.card (Σ S : Q, Fin (K S)))) *
          (2 * ENNReal.ofReal Kc) ^ (n - Fintype.card (Σ S : Q, Fin (K S))))) =
    ENNReal.ofReal ((∏ S, (8 * ρ S * Dt) ^ (K S) / (Nat.factorial (K S) : ℝ)) * Real.pi ^ n *
      (3 * (2 * Kc)) ^ (n - Fintype.card (Σ S : Q, Fin (K S)))) := by
  have hcard : Fintype.card (Σ S : Q, Fin (K S)) = ∑ S, K S := by simp [Fintype.card_sigma]
  set m := n - Fintype.card (Σ S : Q, Fin (K S)) with hm
  rw [← classReal_eq K ρ Dt Kc 0 n m Real.pi]
  have hπ : 0 ≤ Real.pi := Real.pi_pos.le
  have hρ' : ∀ s : (Σ S : Q, Fin (K S)), 0 ≤ 2 * ρ s.1 := fun s => by have := hρ s.1; positivity
  have hfac : ∀ S, 0 ≤ 2 ^ (K S) * Dt ^ (K S) / (Nat.factorial (K S) : ℝ) := fun S => by positivity
  have e1 : (2 : ℝ≥0∞) ^ Fintype.card (Σ S : Q, Fin (K S)) = ENNReal.ofReal ((2 : ℝ) ^ (∑ S, K S)) := by
    rw [← hcard, ENNReal.ofReal_pow (by norm_num)]; simp
  have e2 : ∏ s : (Σ S : Q, Fin (K S)), ENNReal.ofReal (2 * ρ s.1) =
      ENNReal.ofReal (∏ s : (Σ S : Q, Fin (K S)), 2 * ρ s.1) :=
    (ENNReal.ofReal_prod_of_nonneg (fun s _ => hρ' s)).symm
  have e3 : ∏ S, ENNReal.ofReal (2 ^ (K S) * Dt ^ (K S) / (Nat.factorial (K S) : ℝ)) =
      ENNReal.ofReal (∏ S, 2 ^ (K S) * Dt ^ (K S) / (Nat.factorial (K S) : ℝ)) :=
    (ENNReal.ofReal_prod_of_nonneg (fun S _ => hfac S)).symm
  have e4 : (2 * ENNReal.ofReal Kc) ^ m = ENNReal.ofReal ((2 * Kc) ^ m) := by
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by norm_num)]; simp
  rw [e1, e2, e3, e4]
  have hC : 0 ≤ ∏ S, 2 ^ (K S) * Dt ^ (K S) / (Nat.factorial (K S) : ℝ) := Finset.prod_nonneg (fun S _ => hfac S)
  have hD : 0 ≤ Real.pi ^ n * 3 ^ m := by positivity
  have hE : 0 ≤ (2 * Kc) ^ m := by positivity
  have hB : 0 ≤ ∏ s : (Σ S : Q, Fin (K S)), 2 * ρ s.1 := Finset.prod_nonneg (fun s _ => hρ' s)
  rw [← ENNReal.ofReal_mul hC, ← ENNReal.ofReal_mul (mul_nonneg hC hD), ← ENNReal.ofReal_mul hB,
    ← ENNReal.ofReal_mul (by positivity)]

end WaveTurbulence.Ladder
