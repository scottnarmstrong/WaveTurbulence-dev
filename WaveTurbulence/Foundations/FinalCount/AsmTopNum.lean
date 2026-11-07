/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmPhase2d
public import WaveTurbulence.Foundations.FinalCount.AsmArith
/-! **FINALCOUNT-ASSEMBLY (top level): the polylogarithmic node bound `N` of `chain_cover`** (`exists_N`).
Pure arithmetic: with `a = |atoms|`, `cD = #darts`, `ℓ = ⌈2 log L⌉₊ + 1`, all four size conditions hold for `N = 4096 t^13`,
`t = max (2a) (max cD ℓ)`, and `N ≤ 4096 (2 (1+log L)^(m+1))^13`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
namespace WaveTurbulence.FinalCountAsm

theorem nat_poly_aux (t : ℕ) (ht : 1 ≤ t) (x y z : ℕ) (hx : x ≤ t) (hy : y ≤ t) (hz : z ≤ t) :
    (y * (y * (y * (y * (z * (2 * (x * 2))))))) + x * (y * (y * (z * (2 * (x * 2))))) + 1 ≤ 4096 * t ^ 13 ∧
    nodeBound2 x y z + 1 ≤ 4096 * t ^ 13 ∧
    x * (y * (y * (z * (2 * (x * 2))))) + 1 ≤ 4096 * t ^ 13 ∧
    x * y * y + 1 ≤ 4096 * t ^ 13 := by
  have p : ∀ k, k ≤ 13 → t ^ k ≤ t ^ 13 := fun k hk => Nat.pow_le_pow_right ht hk
  have h1 : (y * (y * (y * (y * (z * (2 * (x * 2))))))) + x * (y * (y * (z * (2 * (x * 2))))) + 1 ≤
      t * (t * (t * (t * (t * (2 * (t * 2)))))) + t * (t * (t * (t * (2 * (t * 2))))) + 1 := by gcongr
  have h2 : nodeBound2 x y z + 1 ≤ nodeBound2 t t t + 1 := by unfold nodeBound2; gcongr
  have h3 : x * (y * (y * (z * (2 * (x * 2))))) + 1 ≤ t * (t * (t * (t * (2 * (t * 2))))) + 1 := by gcongr
  have h4 : x * y * y + 1 ≤ t * t * t + 1 := by gcongr
  have e1 : t * (t * (t * (t * (t * (2 * (t * 2)))))) + t * (t * (t * (t * (2 * (t * 2))))) + 1 = 4 * t ^ 6 + 4 * t ^ 5 + 1 := by ring
  have e2 : nodeBound2 t t t = 32 * t ^ 11 * (t + 1) ^ 2 := by unfold nodeBound2; ring
  have e2' : (t + 1) ^ 2 ≤ 4 * t ^ 2 := by nlinarith
  have e2'' : 32 * t ^ 11 * (t + 1) ^ 2 ≤ 128 * t ^ 13 := by
    calc 32 * t ^ 11 * (t + 1) ^ 2 ≤ 32 * t ^ 11 * (4 * t ^ 2) := by gcongr
      _ = 128 * t ^ 13 := by ring
  have e3 : t * (t * (t * (t * (2 * (t * 2))))) + 1 = 4 * t ^ 5 + 1 := by ring
  have e4 : t * t * t + 1 = t ^ 3 + 1 := by ring
  have q := p 0 (by omega)
  have q3 := p 3 (by omega)
  have q5 := p 5 (by omega)
  have q6 := p 6 (by omega)
  simp only [pow_zero] at q
  refine ⟨?_, ?_, ?_, ?_⟩ <;> [skip; skip; skip; skip] <;> omega


theorem exists_N (a cD m : ℕ) {L : ℝ} (hL : Real.exp 1 ≤ L) (ha : ((2 * a : ℕ) : ℝ) ≤ (1 + Real.log L) ^ m)
    (hc : cD ≤ 4 * a) :
    ∃ N : ℕ,
      (cD * (cD * (cD * (cD * ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * a) * 2))))))) +
        (2 * a) * (cD * (cD * ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * a) * 2))))) + 1 ≤ N ∧
      nodeBound2 (2 * a) cD ⌈2 * Real.log L⌉₊ + 1 ≤ N ∧
      (2 * a) * (cD * (cD * ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * a) * 2))))) + 1 ≤ N ∧
      2 * a * cD * cD + 1 ≤ N ∧
      (N : ℝ) ≤ 4096 * (2 * (1 + Real.log L) ^ (m + 1)) ^ 13 := by
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (by norm_num)) hL
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hB1 : 1 ≤ 1 + Real.log L := by linarith
  set ℓ : ℕ := ⌈2 * Real.log L⌉₊ + 1 with hℓ
  set t : ℕ := max (2 * a) (max cD ℓ) with ht
  have ht1 : 1 ≤ t := le_trans (by omega : 1 ≤ ℓ) (le_trans (le_max_right _ _) (le_max_right _ _))
  obtain ⟨h1, -, h3, h4⟩ := nat_poly_aux t ht1 (2 * a) cD ℓ (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_trans (le_max_right _ _) (le_max_right _ _))
  obtain ⟨-, h2, -, -⟩ := nat_poly_aux t ht1 (2 * a) cD ⌈2 * Real.log L⌉₊ (le_max_left _ _)
    (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_trans (by omega : ⌈2 * Real.log L⌉₊ ≤ ℓ) (le_trans (le_max_right _ _) (le_max_right _ _)))
  refine ⟨4096 * t ^ 13, h1, h2, h3, h4, ?_⟩
  set T : ℝ := 2 * (1 + Real.log L) ^ (m + 1) with hT
  have hBm : (1 + Real.log L) ^ m ≤ (1 + Real.log L) ^ (m + 1) := pow_le_pow_right₀ hB1 (by omega)
  have hBm1 : 1 ≤ (1 + Real.log L) ^ (m + 1) := one_le_pow₀ hB1
  have htT : (t : ℝ) ≤ T := by
    have e1 : ((2 * a : ℕ) : ℝ) ≤ T := by rw [hT]; linarith
    have e2 : (cD : ℝ) ≤ T := by
      have : (cD : ℝ) ≤ ((4 * a : ℕ) : ℝ) := by exact_mod_cast hc
      push_cast at this e1 ha ⊢; rw [hT]; linarith
    have e3 : (ℓ : ℝ) ≤ T := by
      have h1 : (⌈2 * Real.log L⌉₊ : ℝ) < 2 * Real.log L + 1 := Nat.ceil_lt_add_one (by linarith)
      have h2 : 1 + Real.log L ≤ (1 + Real.log L) ^ (m + 1) := by
        simpa using pow_le_pow_right₀ hB1 (show 1 ≤ m + 1 by omega)
      rw [hℓ]; push_cast; rw [hT]; linarith
    have : (t : ℝ) = max ((2 * a : ℕ) : ℝ) (max (cD : ℝ) (ℓ : ℝ)) := by rw [ht]; push_cast; rfl
    rw [this]; exact max_le e1 (max_le e2 e3)
  push_cast
  gcongr

end WaveTurbulence.FinalCountAsm
