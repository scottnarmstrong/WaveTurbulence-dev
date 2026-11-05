/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib
public import WaveTurbulence.Foundations.WeylSums.Basic
/-! # Finite-group decoupling of a lattice constraint (S3b LADDER-DECAY)

A constraint `∑ Δ_k(P_k) = c` on a product of finite sums is an average, over the `M`-torsion
characters, of products of twisted one-rung sums, once `M` exceeds the size of both sides. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open Finset WaveTurbulence.WeylSums

/-- Orthogonality of the `M`-th roots of unity in one coordinate. -/
lemma sum_e_fin_eq (M : ℕ) (hM : 0 < M) (v : ℤ) (hv : |v| < M) :
    (∑ j : Fin M, e ((j : ℕ) * (v : ℝ) / M)) = if v = 0 then (M : ℂ) else 0 := by
  by_cases h0 : v = 0
  · subst h0; simp
  · rw [ite_eq_right h0]
    have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    set r : ℂ := e ((v : ℝ) / M) with hr
    have hpow : ∀ j : ℕ, e ((j : ℝ) * (v : ℝ) / M) = r ^ j := by
      intro j
      rw [hr, ← e_nat_mul]
      congr 1; ring
    have hr1 : r ≠ 1 := by
      intro h
      rw [hr, e, Complex.exp_eq_one_iff] at h
      obtain ⟨k, hk⟩ := h
      have h2 : ((2 * Real.pi * ((v : ℝ) / M) : ℝ) : ℂ) = ((k * (2 * Real.pi) : ℝ) : ℂ) := by
        apply mul_right_cancel₀ Complex.I_ne_zero
        push_cast at hk ⊢
        linear_combination hk
      have h2' := Complex.ofReal_injective h2
      have hpi := Real.pi_pos
      have h4' : (v : ℝ) / M = k := by
        have : 2 * Real.pi * ((v : ℝ) / M) = 2 * Real.pi * k := by linarith
        exact mul_left_cancel₀ (by positivity) this
      have h4 := h4'
      have h5 : (v : ℝ) = k * M := by field_simp at h4; linarith
      have h6 : v = k * M := by exact_mod_cast h5
      have h7 : (M : ℤ) ∣ v := ⟨k, by rw [h6]; ring⟩
      have h8 := Int.le_of_dvd (abs_pos.mpr h0) ((dvd_abs _ _).mpr h7)
      have : |v| < (M : ℤ) := hv
      omega
    have hrM : r ^ M = 1 := by
      rw [hr, ← e_nat_mul]
      have : (M : ℝ) * ((v : ℝ) / M) = (v : ℝ) := by field_simp
      rw [this, e, Complex.exp_eq_one_iff]
      exact ⟨v, by push_cast; ring⟩
    simp_rw [hpow]
    rw [Fin.sum_univ_eq_sum_range (fun j => r ^ j) M, geom_sum_eq hr1, hrM]
    simp

lemma e_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) : e (∑ i ∈ s, f i) = ∏ i ∈ s, e (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, e_add, ih]

/-- The indicator of `v = 0` as an average of characters. -/
lemma indicator_eq_avg {d : ℕ} (M : ℕ) (hM : 0 < M) (v : Fin d → ℤ) (hv : ∀ i, |v i| < M) :
    (if v = 0 then (1 : ℂ) else 0) =
      ((M : ℂ) ^ d)⁻¹ * ∑ j : Fin d → Fin M, e (∑ i, ((j i : ℕ) : ℝ) * (v i : ℝ) / M) := by
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have h1 : (∑ j : Fin d → Fin M, e (∑ i, ((j i : ℕ) : ℝ) * (v i : ℝ) / M)) =
      ∏ i, ∑ j : Fin M, e ((j : ℕ) * (v i : ℝ) / M) := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    exact Finset.sum_congr rfl (fun j _ => e_sum _ _)
  rw [h1]
  have h2 : ∀ i, (∑ j : Fin M, e ((j : ℕ) * (v i : ℝ) / M)) = if v i = 0 then (M : ℂ) else 0 :=
    fun i => sum_e_fin_eq M hM (v i) (hv i)
  simp_rw [h2]
  by_cases hz : v = 0
  · subst hz; simp; field_simp
  · obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h; push Not at h; exact hz (funext h)
    rw [ite_eq_right hz, Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])]
    simp


/-- **Constraint decoupling by finite characters.** -/
theorem constrained_sum_eq_avg {d : ℕ} {ι G : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset G) (g : ι → G → ℂ) (Δ : ι → G → (Fin d → ℤ)) (c0 : Fin d → ℤ)
    (M : ℕ) (hM : 0 < M)
    (hb : ∀ P ∈ Fintype.piFinset S, ∀ i, |(∑ k, Δ k (P k)) i - c0 i| < M) :
    ∑ P ∈ Fintype.piFinset S, (if ∑ k, Δ k (P k) = c0 then ∏ k, g k (P k) else 0) =
      ((M : ℂ) ^ d)⁻¹ * ∑ j : Fin d → Fin M,
        e (-∑ i, ((j i : ℕ) : ℝ) * (c0 i : ℝ) / M) *
          ∏ k, ∑ p ∈ S k, g k p * e (∑ i, ((j i : ℕ) : ℝ) * (Δ k p i : ℝ) / M) := by
  have hind : ∀ P ∈ Fintype.piFinset S,
      (if ∑ k, Δ k (P k) = c0 then ∏ k, g k (P k) else 0) =
        ((M : ℂ) ^ d)⁻¹ * ∑ j : Fin d → Fin M,
          e (-∑ i, ((j i : ℕ) : ℝ) * (c0 i : ℝ) / M) *
            ∏ k, (g k (P k) * e (∑ i, ((j i : ℕ) : ℝ) * (Δ k (P k) i : ℝ) / M)) := by
    intro P hP
    have h := indicator_eq_avg M hM (∑ k, Δ k (P k) - c0) (fun i => by simpa using hb P hP i)
    have h' := h
    simp only [sub_eq_zero] at h'
    have hprod : ∀ j : Fin d → Fin M,
        e (∑ i, ((j i : ℕ) : ℝ) * ((∑ k, Δ k (P k) - c0) i : ℝ) / M) =
        e (-∑ i, ((j i : ℕ) : ℝ) * (c0 i : ℝ) / M) *
          ∏ k, e (∑ i, ((j i : ℕ) : ℝ) * (Δ k (P k) i : ℝ) / M) := by
      intro j
      rw [← e_sum, ← e_add]
      congr 1
      simp only [Pi.sub_apply, Finset.sum_apply, Int.cast_sub, Int.cast_sum]
      rw [Finset.sum_comm]
      simp only [mul_sub, sub_div, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div,
        neg_add_eq_sub]
    have : (if ∑ k, Δ k (P k) = c0 then ∏ k, g k (P k) else 0) =
        (∏ k, g k (P k)) * (if ∑ k, Δ k (P k) = c0 then (1 : ℂ) else 0) := by
      split_ifs <;> simp
    rw [this, h']
    simp_rw [hprod]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.prod_mul_distrib]
    ring
  rw [Finset.sum_congr rfl hind, ← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.mul_sum, ← Finset.prod_univ_sum (fun k => S k) (fun k p => g k p * e (∑ i, ((j i : ℕ) : ℝ) * (Δ k p i : ℝ) / M))]

end WaveTurbulence.LadderDecay
