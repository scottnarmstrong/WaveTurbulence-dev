/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepNV4
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-D (numerics): the mass of a vine piece against the `RepresentsIntA` bound

Real-number bookkeeping for the vine case (F-CONST: the piece constant `C₁` is chosen after the gate constants).  Slot
masses `μ_s ≤ K x^{sz_s} L^{-η⁸ g_s} lf_s` and unit masses `M_j ≤ x^{cl2_j} L^{A_j} lf_j` (with
`A_j = -η⁸ g_j - (η²/2) n_j + η⁷`) multiply to `C₁^{n+2R} x^{Σ} L^{Σ} Π lf` (`vine_mass_numerics`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Represents

/-- Products of masses with arbitrary real `L`-exponents and leaf factors. -/
theorem prod_masses_lf {ι : Type*} [Fintype ι] (m : ι → ℝ) (sz : ι → ℕ) (A lf : ι → ℝ) (K x L : ℝ)
    (hx0 : 0 ≤ x) (hL : 0 < L) (hlf : ∀ s, 0 ≤ lf s)
    (hm : ∀ s, 0 ≤ m s ∧ m s ≤ K * x ^ (sz s) * L ^ (A s) * lf s) :
    ∏ s, m s ≤ K ^ Fintype.card ι * x ^ (∑ s, sz s) * L ^ (∑ s, A s) * ∏ s, lf s := by
  classical
  calc ∏ s, m s ≤ ∏ s, (K * x ^ (sz s) * L ^ (A s) * lf s) :=
        Finset.prod_le_prod₀ (fun s _ => (hm s).1) (fun s _ => (hm s).2)
    _ = K ^ Fintype.card ι * x ^ (∑ s, sz s) * L ^ (∑ s, A s) * ∏ s, lf s := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
          Finset.card_univ, Finset.prod_pow_eq_pow_sum, Real.rpow_sum_of_pos hL]

/-- **The numerics of a vine piece.** -/
theorem vine_mass_numerics {ιs ιj : Type*} [Fintype ιs] [Fintype ιj] {nsb R : ℕ} (hcard : Fintype.card ιs = 2 * nsb + R)
    (hJ : Fintype.card ιj ≤ nsb) (x L K Cχ b Ch C₁ e8 e2 e7 : ℝ) (hx0 : 0 ≤ x) (hL : 0 < L) (hK : 1 ≤ K)
    (hCχ : 1 ≤ Cχ) (hb : 1 ≤ b) (hCh : 1 ≤ Ch) (hC : Cχ * b * (9 * K) ^ 2 * Ch ≤ C₁)
    (μ : ιs → ℝ) (sz g : ιs → ℕ) (lf : ιs → ℝ) (hlf : ∀ s, 0 ≤ lf s)
    (hμ : ∀ s, 0 ≤ μ s ∧ μ s ≤ K * x ^ (sz s) * L ^ (-e8 * (g s : ℝ)) * lf s)
    (Mj : ιj → ℝ) (cl2 : ιj → ℕ) (gj nj : ιj → ℕ) (lfj : ιj → ℝ) (hlfj : ∀ j, 0 ≤ lfj j)
    (hM : ∀ j, 0 ≤ Mj j ∧ Mj j ≤ x ^ (cl2 j) * L ^ (-e8 * (gj j : ℝ) - e2 * (nj j : ℝ) + e7) * lfj j) :
    Cχ ^ nsb * (9 ^ (2 * nsb + R) * ∏ s, μ s) * b ^ nsb * ∏ j, (Ch * Mj j) ≤
      C₁ ^ (nsb + 2 * R) * (x ^ ((∑ s, sz s) + ∑ j, cl2 j) *
        L ^ (-e8 * ((∑ s, g s : ℕ) + (∑ j, gj j : ℕ) : ℝ) - e2 * ((∑ j, nj j : ℕ) : ℝ) +
          e7 * (Fintype.card ιj : ℝ)) * ((∏ s, lf s) * ∏ j, lfj j)) := by
  classical
  have hK0 : 0 ≤ K := by linarith
  have hCχ0 : 0 ≤ Cχ := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hCh0 : 0 ≤ Ch := by linarith
  have hlfp : 0 ≤ ∏ s, lf s := Finset.prod_nonneg fun s _ => hlf s
  have hlfjp : 0 ≤ ∏ j, lfj j := Finset.prod_nonneg fun j _ => hlfj j
  have hLr1 : ∀ e : ℝ, 0 ≤ L ^ e := fun e => Real.rpow_nonneg hL.le e
  have hμs := prod_masses_lf μ sz (fun s => -e8 * (g s : ℝ)) lf K x L hx0 hL hlf hμ
  have hMs := prod_masses_lf (fun j => Ch * Mj j) cl2
    (fun j => -e8 * (gj j : ℝ) - e2 * (nj j : ℝ) + e7) lfj Ch x L hx0 hL hlfj (fun j => by
      refine ⟨mul_nonneg (by linarith) (hM j).1, ?_⟩
      calc Ch * Mj j ≤ Ch * (x ^ (cl2 j) * L ^ (-e8 * (gj j : ℝ) - e2 * (nj j : ℝ) + e7) * lfj j) :=
            mul_le_mul_of_nonneg_left (hM j).2 (by linarith)
        _ = _ := by ring)
  have e1 : ∑ s, -e8 * (g s : ℝ) = -e8 * ((∑ s, g s : ℕ) : ℝ) := by push_cast; rw [Finset.mul_sum]
  have e2' : ∑ j, (-e8 * (gj j : ℝ) - e2 * (nj j : ℝ) + e7) =
      -e8 * ((∑ j, gj j : ℕ) : ℝ) - e2 * ((∑ j, nj j : ℕ) : ℝ) + e7 * (Fintype.card ιj : ℝ) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    push_cast
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    simp [Finset.sum_const, mul_comm]
  rw [e1] at hμs
  rw [e2'] at hMs
  rw [hcard] at hμs
  have hKe : (K ^ (2 * nsb + R)) = K ^ (2 * nsb + R) := rfl
  set Ps := ∏ s, μ s
  set Pj := ∏ j, (Ch * Mj j)
  have hPs0 : 0 ≤ Ps := Finset.prod_nonneg fun s _ => (hμ s).1
  have hPj0 : 0 ≤ Pj := Finset.prod_nonneg fun j _ => by
    exact mul_nonneg (by linarith) (hM j).1
  have hconst : Cχ ^ nsb * 9 ^ (2 * nsb + R) * b ^ nsb * (K ^ (2 * nsb + R) * Ch ^ Fintype.card ιj) ≤
      C₁ ^ (nsb + 2 * R) := by
    have h1 : Ch ^ Fintype.card ιj ≤ Ch ^ nsb := pow_le_pow_right₀ hCh hJ
    have hca := const_absorb (Cχ * Ch) b (9 * K) C₁ nsb R
      (one_le_mul_of_one_le_of_one_le hCχ hCh) hb (by nlinarith) (by nlinarith [hC])
    calc _ ≤ Cχ ^ nsb * 9 ^ (2 * nsb + R) * b ^ nsb * (K ^ (2 * nsb + R) * Ch ^ nsb) := by gcongr
      _ = (Cχ * Ch) ^ nsb * b ^ nsb * (9 * K) ^ (2 * nsb + R) := by rw [mul_pow, mul_pow]; ring
      _ ≤ _ := hca
  have hx : 0 ≤ x ^ ((∑ s, sz s) + ∑ j, cl2 j) := pow_nonneg hx0 _
  calc Cχ ^ nsb * (9 ^ (2 * nsb + R) * Ps) * b ^ nsb * Pj
      ≤ Cχ ^ nsb * (9 ^ (2 * nsb + R) * (K ^ (2 * nsb + R) * x ^ (∑ s, sz s) * L ^ (-e8 * ((∑ s, g s : ℕ) : ℝ)) *
          ∏ s, lf s)) * b ^ nsb * (Ch ^ Fintype.card ιj * x ^ (∑ j, cl2 j) *
          L ^ (-e8 * ((∑ j, gj j : ℕ) : ℝ) - e2 * ((∑ j, nj j : ℕ) : ℝ) + e7 * (Fintype.card ιj : ℝ)) *
          ∏ j, lfj j) := by
        have hz : 0 ≤ Cχ ^ nsb * b ^ nsb := by positivity
        have := mul_le_mul hμs hMs hPj0 (by positivity)
        calc _ = (Cχ ^ nsb * b ^ nsb * 9 ^ (2 * nsb + R)) * (Ps * Pj) := by ring
          _ ≤ (Cχ ^ nsb * b ^ nsb * 9 ^ (2 * nsb + R)) * _ :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = _ := by ring
    _ = (Cχ ^ nsb * 9 ^ (2 * nsb + R) * b ^ nsb * (K ^ (2 * nsb + R) * Ch ^ Fintype.card ιj)) *
        (x ^ ((∑ s, sz s) + ∑ j, cl2 j) *
        (L ^ (-e8 * ((∑ s, g s : ℕ) : ℝ)) * L ^ (-e8 * ((∑ j, gj j : ℕ) : ℝ) - e2 * ((∑ j, nj j : ℕ) : ℝ) +
          e7 * (Fintype.card ιj : ℝ))) * ((∏ s, lf s) * ∏ j, lfj j)) := by
        rw [pow_add]; ring
    _ ≤ C₁ ^ (nsb + 2 * R) * (x ^ ((∑ s, sz s) + ∑ j, cl2 j) *
        (L ^ (-e8 * ((∑ s, g s : ℕ) : ℝ)) * L ^ (-e8 * ((∑ j, gj j : ℕ) : ℝ) - e2 * ((∑ j, nj j : ℕ) : ℝ) +
          e7 * (Fintype.card ιj : ℝ))) * ((∏ s, lf s) * ∏ j, lfj j)) := by
        refine mul_le_mul_of_nonneg_right hconst ?_
        have h1 : 0 ≤ L ^ (-e8 * ((∑ s, g s : ℕ) : ℝ)) := Real.rpow_nonneg hL.le _
        have h2 : 0 ≤ L ^ (-e8 * ((∑ j, gj j : ℕ) : ℝ) - e2 * ((∑ j, nj j : ℕ) : ℝ) +
          e7 * (Fintype.card ιj : ℝ)) := Real.rpow_nonneg hL.le _
        have h3 : 0 ≤ (∏ s, lf s) * ∏ j, lfj j := mul_nonneg (Finset.prod_nonneg fun s _ => hlf s)
          (Finset.prod_nonneg fun j _ => hlfj j)
        positivity
    _ = _ := by
        rw [← Real.rpow_add hL]
        congr 3
        push_cast; ring

end WaveTurbulence.Represents
