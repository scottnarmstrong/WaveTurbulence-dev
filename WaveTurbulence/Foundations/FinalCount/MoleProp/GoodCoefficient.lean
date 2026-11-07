/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.GoodNormalization
import Mathlib.Tactic

/-! # Uniform domination of actual good-step cut-cardinality factors -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp

theorem good_coefficient_le {C C' N T δ L gain : ℝ}
    (hC0 : 0 ≤ C) (hC : C ≤ C') (hN0 : 0 ≤ N) (hN : N ≤ T)
    (hδ : 0 ≤ δ) (hL : 0 ≤ L) :
    C*N^2*(δ⁻¹)^3*L^(-gain) ≤ C'*T^2*(δ⁻¹)^3*L^(-gain) := by
  have hp := pow_le_pow_left₀ hN0 hN 2
  have hh := mul_le_mul hC hp (sq_nonneg N) (hC0.trans hC)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hh (pow_nonneg (inv_nonneg.mpr hδ) 3))
    (Real.rpow_nonneg hL _)

/-- Conditional algebra helper: a proved three-circuit local EFree count
normalizes to a graph-size bound. Actual source callers supply `hc` from
their old-star and old-cut counting theorems. -/
theorem three_loss_normalization_of_count_bound
    {V D D' : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    [Fintype D'] [DecidableEq D'] (M : Molecule V D) (M' : Molecule V D')
    {d : ℕ} {L γ δ C1 C C' N : ℝ}
    (hd : 3 ≤ d) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1)
    (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1)
    (hC1 : 1 ≤ C1) (hC : 0 ≤ C) (hC' : C+1 ≤ C')
    (hN : 1 ≤ N) (hNcard : N ≤ (M.atoms.card : ℝ)+1)
    (hs : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1)
    (hs' : ∀ a b, a ≠ b → M'.bondsBetween a b ≤ 1)
    (hj : M.circuitRank-M'.circuitRank = 3)
    (Adm : (D → (Fin d → ℤ)) → Prop) (Adm' : (D' → (Fin d → ℤ)) → Prop)
    (P : Finset V → ℝ)
    (hc : countEFree M L γ δ (0 : Mom d) Adm ≤
      (⌈C*N^2*(δ⁻¹)^2*L^(3*((d : ℝ)-γ)-min γ (1-γ))⌉₊ : ℕ∞)*
        countEFree M' L γ δ (0 : Mom d) Adm') :
    countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
      ENNReal.ofReal (C'*((M.atoms.card : ℝ)+1)^2*(δ⁻¹)^3*L^(-min γ (1-γ)))*
        countAFree M' L γ δ C1 (0 : Mom d) Adm' P := by
  have hg : min γ (1-γ) ≤ ((d : ℝ)-γ)*3 := by
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have hm := min_le_left γ (1-γ)
    linarith only [hdR,hm,hγ.2]
  have hc' : countEFree M L γ δ (0 : Mom d) Adm ≤
      (⌈C*N^2*(δ⁻¹)^2*L^(((d : ℝ)-γ)*(3 : ℕ)-min γ (1-γ))⌉₊ : ℕ∞)*
        countEFree M' L γ δ (0 : Mom d) Adm' := by
    simpa only [Nat.cast_ofNat,mul_comm ((d : ℝ)-γ) 3] using hc
  have hh := good_normalization_of_count_bound M M' hL hlog hδ hC1 hC hN
    (by decide : (2 : ℕ) ≤ 3) hg hs hs' hj Adm Adm' P hc'
  have hcoef := good_coefficient_le (gain := min γ (1-γ)) (by linarith only [hC] : 0 ≤ C+1) hC'
    (zero_le_one.trans hN) hNcard hδ.1.le (zero_le_one.trans hL)
  exact hh.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hcoef) bot_le)

end WaveTurbulence.MoleProp
