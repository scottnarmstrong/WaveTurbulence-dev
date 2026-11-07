/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVN1
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-D (numerics, part 2): the exponents of `RepresentsIntA`

`vine_mass_le_repBound`: the product of `vine_mass_numerics` is at most the right-hand side of the `RepresentsIntA`
bound once the exponent bookkeeping holds: the powers of `x = C₁ √δ` add up to `n - ord` (`hexp`), `g_sk` and `b_sk` are
at most the incoherency and bad-vine exponents of the slots and units (`L ≥ 1`, `hg`, `hb`) and the number of units is at
most the number of hinges (`hh`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Represents

theorem vine_mass_le_repBound {ιs ιj : Type*} [Fintype ιs] [Fintype ιj] {nsb R : ℕ}
    (hcard : Fintype.card ιs = 2 * nsb + R) (hJ : Fintype.card ιj ≤ nsb) (x L K Cχ b Ch C₁ e8 e2 e7 : ℝ)
    (hx0 : 0 ≤ x) (hL1 : 1 ≤ L) (hK : 1 ≤ K) (hCχ : 1 ≤ Cχ) (hb : 1 ≤ b) (hCh : 1 ≤ Ch)
    (hC : Cχ * b * (9 * K) ^ 2 * Ch ≤ C₁) (he8 : 0 ≤ e8) (he2 : 0 ≤ e2) (he7 : 0 ≤ e7)
    (μ : ιs → ℝ) (sz g : ιs → ℕ) (lf : ιs → ℝ) (hlf : ∀ s, 0 ≤ lf s)
    (hμ : ∀ s, 0 ≤ μ s ∧ μ s ≤ K * x ^ (sz s) * L ^ (-e8 * (g s : ℝ)) * lf s)
    (Mj : ιj → ℝ) (cl2 : ιj → ℕ) (gj nj : ιj → ℕ) (lfj : ιj → ℝ) (hlfj : ∀ j, 0 ≤ lfj j)
    (hM : ∀ j, 0 ≤ Mj j ∧ Mj j ≤ x ^ (cl2 j) * L ^ (-e8 * (gj j : ℝ) - e2 * (nj j : ℝ) + e7) * lfj j)
    (n ord gsk bsk nh : ℕ) (hexp : (∑ s, sz s) + ∑ j, cl2 j = n - ord) (hord : ord = nsb)
    (hg : gsk ≤ (∑ s, g s) + ∑ j, gj j) (hb' : bsk ≤ ∑ j, nj j) (hh : Fintype.card ιj ≤ nh) :
    Cχ ^ nsb * (9 ^ (2 * nsb + R) * ∏ s, μ s) * b ^ nsb * ∏ j, (Ch * Mj j) ≤
      x ^ (n - ord) * C₁ ^ (ord + 2 * R) * L ^ (-e8 * (gsk : ℝ) - e2 * (bsk : ℝ) + e7 * (nh : ℝ)) *
        ((∏ s, lf s) * ∏ j, lfj j) := by
  have hL0 : 0 < L := by linarith
  refine (vine_mass_numerics hcard hJ x L K Cχ b Ch C₁ e8 e2 e7 hx0 hL0 hK hCχ hb hCh hC μ sz g lf hlf hμ
    Mj cl2 gj nj lfj hlfj hM).trans ?_
  rw [hexp, hord]
  have h3 : 0 ≤ (∏ s, lf s) * ∏ j, lfj j :=
    mul_nonneg (Finset.prod_nonneg fun s _ => hlf s) (Finset.prod_nonneg fun j _ => hlfj j)
  have hE12 : -e8 * (((∑ s, g s : ℕ) : ℝ) + ((∑ j, gj j : ℕ) : ℝ)) - e2 * ((∑ j, nj j : ℕ) : ℝ) +
      e7 * (Fintype.card ιj : ℝ) ≤ -e8 * (gsk : ℝ) - e2 * (bsk : ℝ) + e7 * (nh : ℝ) := by
    have h1 : (gsk : ℝ) ≤ ((∑ s, g s : ℕ) : ℝ) + ((∑ j, gj j : ℕ) : ℝ) := by exact_mod_cast hg
    have h2 : (bsk : ℝ) ≤ ((∑ j, nj j : ℕ) : ℝ) := by exact_mod_cast hb'
    have h4 : (Fintype.card ιj : ℝ) ≤ (nh : ℝ) := by exact_mod_cast hh
    nlinarith [mul_le_mul_of_nonneg_left h1 he8, mul_le_mul_of_nonneg_left h2 he2,
      mul_le_mul_of_nonneg_left h4 he7]
  have hpow := Real.rpow_le_rpow_of_exponent_le hL1 hE12
  have hC1 : 1 ≤ C₁ := by
    refine le_trans ?_ hC
    have h1 : 1 ≤ Cχ * b := one_le_mul_of_one_le_of_one_le hCχ hb
    have h2 : 1 ≤ (9 * K) ^ 2 := by nlinarith
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 h2) hCh
  have hxn : 0 ≤ x ^ (n - nsb) := pow_nonneg hx0 _
  have hCp : 0 ≤ C₁ ^ (nsb + 2 * R) := by positivity
  calc C₁ ^ (nsb + 2 * R) * (x ^ (n - nsb) *
        L ^ (-e8 * (((∑ s, g s : ℕ) : ℝ) + ((∑ j, gj j : ℕ) : ℝ)) - e2 * ((∑ j, nj j : ℕ) : ℝ) +
          e7 * (Fintype.card ιj : ℝ)) * ((∏ s, lf s) * ∏ j, lfj j))
      ≤ C₁ ^ (nsb + 2 * R) * (x ^ (n - nsb) *
        L ^ (-e8 * (gsk : ℝ) - e2 * (bsk : ℝ) + e7 * (nh : ℝ)) * ((∏ s, lf s) * ∏ j, lfj j)) := by
        gcongr
    _ = _ := by ring

end WaveTurbulence.Represents
