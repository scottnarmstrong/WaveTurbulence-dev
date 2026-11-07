/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MergeFiber
import Mathlib.Tactic

/-! # The two-vector count for the double bond of a merge (DH23 Lemma A.3(1))

`(+,+)`: `positive_atom_shell_threshold_bound` (thin annulus count, `γ > 1/2`);
`(+,−)`: `negative_atom_large_bound` with the large gap at `v₁`.
Both are `≤ C δ⁻¹ L^{d−γ−η/2}`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4 WaveTurbulence.MoleProp WaveTurbulence.CountLemmas

theorem pairSet_card_le (m : ℕ) (γ η : ℝ) (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) (hη : 0 < η) (hηmax : η ≤ min γ (1 - γ) / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L ≥ (1 : ℝ), ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∀ (a b : Mom (m + 2)) (nk : Fin (m + 2) → ℤ) (β : ℝ)
      (ε : ℤˣ), (ε = -1 → L ^ (-γ + η) ≤ ‖latticePoint L nk‖) →
      ((atomPairSet L a b nk β (δ⁻¹ * L ^ (-2 * γ)) ε).ncard : ℝ) ≤ C * δ⁻¹ * L ^(((m + 2 : ℕ) : ℝ) - γ - η / 2) := by
  have hmin : min γ (1 - γ) = 1 - γ := min_eq_right (by linarith [hγ.1])
  refine ⟨max (3 ^ m * (6 * Real.pi + 1924002)) (3 ^ (m + 1) * (((m + 2 : ℕ) : ℝ) + 1)), by positivity, ?_⟩
  intro L hL δ hδ a b nk β ε hgap
  have hLp : 0 < L := by linarith
  have hδ0 := hδ.1
  have hδi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ0).mpr hδ.2
  rcases Int.units_eq_one_or ε with rfl | rfl
  · -- same sign
    set g : ℝ := max (2 - 2 * γ) ((4 - 2 * γ) / 3) with hg
    set τ := δ⁻¹ * L ^ (-2 * γ) with hτ
    have hτL : τ * L ^ 2 = δ⁻¹ * L ^ (2 - 2 * γ) := by
      rw [hτ, mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hLp]; congr 2; push_cast; ring
    have h1 : 1 ≤ τ * L ^ 2 := by
      rw [hτL]
      have := Real.one_le_rpow hL (show 0 ≤ 2 - 2 * γ by linarith [hγ.2])
      nlinarith
    have hU1 : τ * L ^ 2 ≤ δ⁻¹ * L ^ g := by
      rw [hτL]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL (le_max_left _ _)) (by positivity)
    have hU2 : L ^ 2 * (τ * L ^ 2) ≤ (δ⁻¹ * L ^ g) ^ 3 := by
      have e1 : L ^ 2 * (δ⁻¹ * L ^ (2 - 2 * γ)) = δ⁻¹ * L ^ (4 - 2 * γ) := by
        rw [mul_left_comm, ← Real.rpow_natCast L 2, ← Real.rpow_add hLp]; congr 2; push_cast; ring
      have e2 : (δ⁻¹ * L ^ g) ^ 3 = δ⁻¹ ^ 3 * L ^ (3 * g) := by
        rw [mul_pow, ← Real.rpow_natCast (L ^ g) 3, ← Real.rpow_mul hLp.le]; congr 2; push_cast; ring
      rw [hτL, e1, e2]
      have h3 : 4 - 2 * γ ≤ 3 * g := by have := le_max_right (2 - 2 * γ) ((4 - 2 * γ) / 3); linarith
      have h4 : L ^ (4 - 2 * γ) ≤ L ^ (3 * g) := Real.rpow_le_rpow_of_exponent_le hL h3
      have h5 : δ⁻¹ ≤ δ⁻¹ ^ 3 := by nlinarith [pow_le_pow_right₀ hδi (show 1 ≤ 3 by norm_num)]
      exact mul_le_mul h5 h4 (by positivity) (by positivity)
    have hb := positive_atom_shell_threshold_bound (d := m) hLp (by positivity) h1 hU1 hU2 a b nk β
    refine hb.trans ?_
    have hgle : g ≤ 2 - γ - η / 2 := by
      rw [hg]; refine max_le ?_ ?_
      · nlinarith [hγ.1, min_le_left γ (1 - γ)]
      · nlinarith [hγ.2, min_le_right γ (1 - γ)]
    have hpow : L ^ ((m : ℝ) + g) ≤ L ^ (((m + 2 : ℕ) : ℝ) - γ - η / 2) :=
      Real.rpow_le_rpow_of_exponent_le hL (by push_cast; linarith)
    have hLm : L ^ m * L ^ g = L ^ ((m : ℝ) + g) := by
      rw [Real.rpow_add hLp, Real.rpow_natCast]
    have h2L : (2 * L + 1) ^ m ≤ 3 ^ m * L ^ m := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) m
    have hK : 0 ≤ 6 * Real.pi + 1924002 := by positivity
    calc (2 * L + 1) ^ m * (6 * Real.pi + 1924002) * (δ⁻¹ * L ^ g)
        ≤ (3 ^ m * L ^ m) * (6 * Real.pi + 1924002) * (δ⁻¹ * L ^ g) := by gcongr
      _ = (3 ^ m * (6 * Real.pi + 1924002)) * δ⁻¹ * L ^ ((m : ℝ) + g) := by rw [← hLm]; ring
      _ ≤ max (3 ^ m * (6 * Real.pi + 1924002)) (3 ^ (m + 1) * (((m + 2 : ℕ) : ℝ) + 1)) * δ⁻¹ *
          L ^ ((m : ℝ) + g) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (by positivity)
      _ ≤ max (3 ^ m * (6 * Real.pi + 1924002)) (3 ^ (m + 1) * (((m + 2 : ℕ) : ℝ) + 1)) * δ⁻¹ *
          L ^ (((m + 2 : ℕ) : ℝ) - γ - η / 2) := mul_le_mul_of_nonneg_left hpow (by positivity)
  · have hgap' := hgap rfl
    have hη' : η ≤ 1 - γ := by linarith [min_le_right γ (1 - γ)]
    have hb := negative_atom_large_bound (d := m + 2) (by omega) hL hδ hη' a b nk β hgap'
    refine hb.trans ?_
    have hpow : L ^ (((m + 2 : ℕ) : ℝ) - γ - η) ≤ L ^ (((m + 2 : ℕ) : ℝ) - γ - η / 2) :=
      Real.rpow_le_rpow_of_exponent_le hL (by linarith)
    have hc : 3 ^ (m + 2 - 1) * (((m + 2 : ℕ) : ℝ) + 1) = 3 ^ (m + 1) * (((m + 2 : ℕ) : ℝ) + 1) := by
      rw [show m + 2 - 1 = m + 1 by omega]
    rw [hc]
    calc 3 ^ (m + 1) * (((m + 2 : ℕ) : ℝ) + 1) * δ⁻¹ * L ^ (((m + 2 : ℕ) : ℝ) - γ - η)
        ≤ max (3 ^ m * (6 * Real.pi + 1924002)) (3 ^ (m + 1) * (((m + 2 : ℕ) : ℝ) + 1)) * δ⁻¹ *
          L ^ (((m + 2 : ℕ) : ℝ) - γ - η) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) (by positivity)
      _ ≤ max (3 ^ m * (6 * Real.pi + 1924002)) (3 ^ (m + 1) * (((m + 2 : ℕ) : ℝ) + 1)) * δ⁻¹ *
          L ^ (((m + 2 : ℕ) : ℝ) - γ - η / 2) := mul_le_mul_of_nonneg_left hpow (by positivity)

end WaveTurbulence.FinalCountG8
