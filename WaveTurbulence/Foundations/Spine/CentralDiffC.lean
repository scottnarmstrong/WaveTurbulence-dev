/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
/-! AMEND6' (R47-FINAL F5): exact first-coefficient extraction by central differences, real and complex-valued,
and the multilinear polarization identity. For a polynomial `p(x) = sum_{s <= 2M} a_s x^s` and `lam != 0`,
`sum_k (w_k / lam) p(lam (k - M)) = a_1` with `w_k = (-1)^(k+M+1) C(2M,k) / ((k - M) C(2M,M))`, `|w_k| <= 1/|k-M|`.
(research-twistprof CentralDiff.lean, referee-checked.) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine.CentralDiff
open Finset

/-- The central-difference weight at node `k` (zero at the centre `k = M`). -/
noncomputable def cw (M k : ℕ) : ℝ :=
  if k = M then 0 else
    (-1 : ℝ) ^ (k + M + 1) * ((2 * M).choose k : ℝ) / (((k : ℝ) - M) * ((2 * M).choose M : ℝ))

/-- `∑_k (-1)^k C(2M,k) q(k) = 0` for a polynomial `q` of degree `< 2M` (the `2M`-th finite difference). -/
theorem alt_choose_poly_eq_zero (M : ℕ) (q : Polynomial ℝ) (hq : q.natDegree < 2 * M) :
    ∑ k ∈ range (2 * M + 1), (-1 : ℝ) ^ k * ((2 * M).choose k : ℝ) * q.eval (k : ℝ) = 0 := by
  have h := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (R := ℝ) hq) 0
  rw [fwdDiff_iter_eq_sum_shift] at h
  simp only [zero_add, nsmul_eq_mul, mul_one, smul_eq_mul, Pi.zero_apply] at h
  rw [← h]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ 2 * M := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hpar : (-1 : ℝ) ^ (2 * M - k) = (-1 : ℝ) ^ k := by
    have h1 : (-1 : ℝ) ^ (2 * M - k) * (-1) ^ k = 1 := by
      rw [← pow_add, Nat.sub_add_cancel hk', pow_mul]; norm_num
    have h2 : (-1 : ℝ) ^ k * (-1) ^ k = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
    calc (-1 : ℝ) ^ (2 * M - k) = (-1) ^ (2 * M - k) * ((-1) ^ k * (-1) ^ k) := by rw [h2, mul_one]
      _ = ((-1) ^ (2 * M - k) * (-1) ^ k) * (-1) ^ k := by ring
      _ = (-1) ^ k := by rw [h1, one_mul]
  rw [zsmul_eq_mul]
  push_cast
  rw [hpar]

theorem cw_symm (M k : ℕ) (hk : k ≤ 2 * M) : cw M (2 * M - k) = - cw M k := by
  unfold cw
  by_cases hkM : k = M
  · subst hkM
    have : 2 * k - k = k := by omega
    simp [this]
  · have h2 : 2 * M - k ≠ M := by omega
    rw [if_neg h2, if_neg hkM, Nat.choose_symm hk]
    have hc : ((2 * M - k : ℕ) : ℝ) - M = -((k : ℝ) - M) := by
      rw [Nat.cast_sub hk]; push_cast; ring
    rw [hc]
    have hpar : (-1 : ℝ) ^ (2 * M - k + M + 1) = (-1 : ℝ) ^ (k + M + 1) := by
      rcases Nat.even_or_odd k with ⟨a, ha⟩ | ⟨a, ha⟩
      · have e1 : 2 * M - k + M + 1 = 2 * (M - a) + M + 1 := by omega
        have e2 : k + M + 1 = 2 * a + M + 1 := by omega
        rw [e1, e2, pow_add, pow_add, pow_add, pow_add, pow_mul, pow_mul]; norm_num
      · have e1 : 2 * M - k + M + 1 = 2 * (M - a - 1) + 1 + M + 1 := by omega
        have e2 : k + M + 1 = 2 * a + 1 + M + 1 := by omega
        rw [e1, e2]; simp only [pow_add, pow_mul]; norm_num
    rw [hpar, neg_mul, div_neg]

/-- The moment identity: `∑_k w_k (k - M)^m = [m = 1]` for `m ≤ 2M`, `1 ≤ M`. -/
theorem cw_moment (M : ℕ) (hM : 1 ≤ M) (m : ℕ) (hm : m ≤ 2 * M) :
    ∑ k ∈ range (2 * M + 1), cw M k * ((k : ℝ) - M) ^ m = if m = 1 then 1 else 0 := by
  have hC : (0 : ℝ) < ((2 * M).choose M : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · -- odd symmetry under k ↦ 2M - k
    simp only [pow_zero, mul_one, show (0 : ℕ) ≠ 1 from by decide, if_false]
    have hr := Finset.sum_range_reflect (fun k => cw M k) (2 * M + 1)
    have hneg : ∑ k ∈ range (2 * M + 1), cw M (2 * M + 1 - 1 - k) = - ∑ k ∈ range (2 * M + 1), cw M k := by
      rw [← Finset.sum_neg_distrib]
      refine sum_congr rfl fun k hk => ?_
      have hk' : k ≤ 2 * M := Nat.lt_succ_iff.mp (mem_range.mp hk)
      rw [show 2 * M + 1 - 1 - k = 2 * M - k by omega, cw_symm M k hk']
    rw [hr] at hneg
    linarith
  · -- for m ≥ 1, w_k (k-M)^m = -(-1)^k C(2M,k) (k-M)^(m-1) (-1)^M / C(2M,M) off the centre
    have hterm : ∀ k ∈ range (2 * M + 1), cw M k * ((k : ℝ) - M) ^ m =
        - ((-1 : ℝ) ^ M / ((2 * M).choose M : ℝ)) *
          ((-1 : ℝ) ^ k * ((2 * M).choose k : ℝ) * ((k : ℝ) - M) ^ (m - 1)) +
        (if k = M then (if m = 1 then 1 else 0) else 0) := by
      intro k _
      unfold cw
      by_cases hkM : k = M
      · subst hkM
        simp only [if_true, zero_mul, sub_self]
        by_cases h1 : m = 1
        · subst h1; simp only [Nat.sub_self, pow_zero, mul_one, if_true]
          have h2 : ((-1 : ℝ) ^ k) * (-1) ^ k = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
          have hCne : ((2 * k).choose k : ℝ) ≠ 0 := hC.ne'
          rw [show -((-1 : ℝ) ^ k / ((2 * k).choose k : ℝ)) * ((-1) ^ k * ((2 * k).choose k : ℝ)) =
              -(((-1 : ℝ) ^ k * (-1) ^ k) * (((2 * k).choose k : ℝ) / ((2 * k).choose k : ℝ))) by ring,
            h2, div_self hCne]
          ring
        · have : m - 1 ≠ 0 := by omega
          simp [h1, zero_pow this]
      · rw [if_neg hkM, if_neg hkM, add_zero]
        have hne : ((k : ℝ) - M) ≠ 0 := by
          intro h; apply hkM; exact_mod_cast (sub_eq_zero.mp h)
        have hp : ((k : ℝ) - M) ^ m = ((k : ℝ) - M) * ((k : ℝ) - M) ^ (m - 1) := by
          rw [← pow_succ']; congr 1; omega
        rw [hp]
        have hs : (-1 : ℝ) ^ (k + M + 1) = - ((-1 : ℝ) ^ M * (-1 : ℝ) ^ k) := by
          rw [pow_add, pow_add]; ring
        rw [hs]
        field_simp
    rw [sum_congr rfl hterm, sum_add_distrib, ← mul_sum]
    have hcent : ∑ k ∈ range (2 * M + 1), (if k = M then (if m = 1 then (1 : ℝ) else 0) else 0) =
        if m = 1 then 1 else 0 := by
      rw [Finset.sum_ite_eq' (range (2 * M + 1)) M]
      simp [show M < 2 * M + 1 by omega]
    rw [hcent]
    by_cases h1 : m = 1
    · subst h1
      simp only [Nat.sub_self, pow_zero, mul_one, if_true]
      have h0 : ∑ k ∈ range (2 * M + 1), (-1 : ℝ) ^ k * ((2 * M).choose k : ℝ) = 0 := by
        have := alt_choose_poly_eq_zero M (Polynomial.C 1) (by simp; omega)
        simpa using this
      rw [h0]; ring
    · have h0 : ∑ k ∈ range (2 * M + 1), (-1 : ℝ) ^ k * ((2 * M).choose k : ℝ) * ((k : ℝ) - M) ^ (m - 1) = 0 := by
        have hq := alt_choose_poly_eq_zero M ((Polynomial.X - Polynomial.C (M : ℝ)) ^ (m - 1)) (by
          rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]; omega)
        simpa [Polynomial.eval_pow] using hq
      rw [h0, if_neg h1]; ring

/-- **Exact real extraction of the first coefficient.** -/
theorem first_coeff_extraction (M : ℕ) (hM : 1 ≤ M) (a : ℕ → ℝ) (lam : ℝ) (hlam : lam ≠ 0) :
    ∑ k ∈ range (2 * M + 1), (cw M k / lam) *
      (∑ s ∈ range (2 * M + 1), a s * (lam * ((k : ℝ) - M)) ^ s) = a 1 := by
  have e : ∀ k ∈ range (2 * M + 1), (cw M k / lam) *
      (∑ s ∈ range (2 * M + 1), a s * (lam * ((k : ℝ) - M)) ^ s) =
      ∑ s ∈ range (2 * M + 1), (a s * lam ^ s / lam) * (cw M k * ((k : ℝ) - M) ^ s) := by
    intro k _
    rw [mul_sum]
    refine sum_congr rfl fun s _ => ?_
    rw [mul_pow]; ring
  rw [sum_congr rfl e, sum_comm]
  rw [sum_congr rfl fun s hs => by rw [← mul_sum, cw_moment M hM s (Nat.lt_succ_iff.mp (mem_range.mp hs))]]
  rw [sum_eq_single 1]
  · simp only [if_true, mul_one, pow_one]; field_simp
  · intro s _ hs; simp [hs]
  · intro h; exfalso; exact h (mem_range.mpr (by omega))

/-- The weights are small: `|w_k| ≤ 1/|k - M|`, hence `∑_k |w_k| ≤ 2 (1 + log M)`-type bounds. -/
theorem abs_cw_le (M k : ℕ) (hk : k ≠ M) : |cw M k| ≤ 1 / |(k : ℝ) - M| := by
  unfold cw
  rw [if_neg hk]
  have hC : (0 : ℝ) < ((2 * M).choose M : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  have hle : ((2 * M).choose k : ℝ) ≤ ((2 * M).choose M : ℝ) := by
    exact_mod_cast Nat.choose_le_middle k (2 * M) |>.trans_eq (by rw [Nat.mul_div_cancel_left M (by norm_num)])
  have hne : ((k : ℝ) - M) ≠ 0 := by
    intro h; apply hk; exact_mod_cast (sub_eq_zero.mp h)
  rw [abs_div, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos hC, Nat.abs_cast]
  rw [div_le_div_iff₀ (mul_pos (abs_pos.mpr hne) hC) (abs_pos.mpr hne)]
  nlinarith [abs_pos.mpr hne]


/-- Complex-valued first-coefficient extraction (F5): the weights and `lam` are real. -/
theorem first_coeff_extraction_complex (M : ℕ) (hM : 1 ≤ M) (a : ℕ → ℂ) (lam : ℝ) (hlam : lam ≠ 0) :
    ∑ k ∈ range (2 * M + 1), ((cw M k / lam : ℝ) : ℂ) *
      (∑ s ∈ range (2 * M + 1), a s * (((lam * ((k : ℝ) - M) : ℝ) : ℂ)) ^ s) = a 1 := by
  have hre : ∀ k : ℕ, ((((cw M k / lam : ℝ) : ℂ)) *
      (∑ s ∈ range (2 * M + 1), a s * (((lam * ((k : ℝ) - M) : ℝ) : ℂ)) ^ s)).re =
      (cw M k / lam) * ∑ s ∈ range (2 * M + 1), (a s).re * (lam * ((k : ℝ) - M)) ^ s := by
    intro k
    rw [Complex.re_ofReal_mul, Complex.re_sum]
    congr 1
    refine sum_congr rfl fun s _ => ?_
    rw [← Complex.ofReal_pow, Complex.re_mul_ofReal]
  have him : ∀ k : ℕ, ((((cw M k / lam : ℝ) : ℂ)) *
      (∑ s ∈ range (2 * M + 1), a s * (((lam * ((k : ℝ) - M) : ℝ) : ℂ)) ^ s)).im =
      (cw M k / lam) * ∑ s ∈ range (2 * M + 1), (a s).im * (lam * ((k : ℝ) - M)) ^ s := by
    intro k
    rw [Complex.im_ofReal_mul, Complex.im_sum]
    congr 1
    refine sum_congr rfl fun s _ => ?_
    rw [← Complex.ofReal_pow, Complex.im_mul_ofReal]
  apply Complex.ext
  · rw [Complex.re_sum]
    simp_rw [hre]
    exact first_coeff_extraction M hM (fun s => (a s).re) lam hlam
  · rw [Complex.im_sum]
    simp_rw [him]
    exact first_coeff_extraction M hM (fun s => (a s).im) lam hlam

/-- Multilinear polarization: for `|S| <= 2M`, the first-order term of `prod_l (x_l + eps y_l)` is recovered from
`2M + 1` evaluations `eps = lam (k - M)`. -/
theorem polarization_extraction {ι : Type*} [DecidableEq ι] (S : Finset ι) (M : ℕ) (hM : 1 ≤ M)
    (hS : S.card ≤ 2 * M) (x y : ι → ℂ) (lam : ℝ) (hlam : lam ≠ 0) :
    ∑ a ∈ S, y a * ∏ l ∈ S.erase a, x l =
      ∑ k ∈ range (2 * M + 1), ((cw M k / lam : ℝ) : ℂ) *
        ∏ l ∈ S, (x l + ((lam * ((k : ℝ) - M) : ℝ) : ℂ) * y l) := by
  set p : Polynomial ℂ := ∏ l ∈ S, (Polynomial.C (x l) + Polynomial.C (y l) * Polynomial.X) with hp
  have hdeg : p.natDegree ≤ 2 * M := by
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ 1 fun l _ => ?_).trans (by simpa using hS)
    refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
    exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  have hev : ∀ z : ℂ, p.eval z = ∏ l ∈ S, (x l + z * y l) := by
    intro z
    rw [hp, Polynomial.eval_prod]
    refine prod_congr rfl fun l _ => ?_
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
    ring
  have hc1 : p.coeff 1 = ∑ a ∈ S, y a * ∏ l ∈ S.erase a, x l := by
    have hd : (Polynomial.derivative p).eval 0 = p.coeff 1 := by
      rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
      simp
    rw [← hd, hp, Polynomial.derivative_prod_finset, Polynomial.eval_finsetSum]
    refine sum_congr rfl fun a _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_prod]
    have hda : Polynomial.derivative (Polynomial.C (x a) + Polynomial.C (y a) * Polynomial.X) =
        Polynomial.C (y a) := by simp
    rw [hda, Polynomial.eval_C, mul_comm]
    congr 1
    refine prod_congr rfl fun l _ => ?_
    simp
  rw [← hc1, ← first_coeff_extraction_complex M hM p.coeff lam hlam]
  refine sum_congr rfl fun k _ => ?_
  congr 1
  rw [← hev, Polynomial.eval_eq_sum_range' (n := 2 * M + 1) (by omega)]

end WaveTurbulence.LGSpine.CentralDiff
