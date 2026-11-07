/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Typed.Jets
/-! # FL-TYPED: jet-constant algebra and the elementary sum bounds of the profile estimate. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.Flower.Typed
open WaveTurbulence.NormBridgeScratch Finset

variable {d : ℕ}

/-- Convolution of jet constants (the Leibniz coefficients). -/
def mulγ (Γ Γ' : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ ij ∈ antidiagonal k, (k.choose ij.1 : ℝ) * (Γ ij.1 * Γ' ij.2)

theorem mulγ_nonneg {Γ Γ' : ℕ → ℝ} (h : ∀ k, 0 ≤ Γ k) (h' : ∀ k, 0 ≤ Γ' k) (k : ℕ) :
    0 ≤ mulγ Γ Γ' k :=
  sum_nonneg fun ij _ => mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (h _) (h' _))

theorem mulγ_zero (Γ Γ' : ℕ → ℝ) : mulγ Γ Γ' 0 = Γ 0 * Γ' 0 := by
  simp [mulγ]

theorem jetMulγ {N : ℕ} {Γ Γ' : ℕ → ℝ} {τ : ℝ} {E F : Mom d → ℂ}
    (hEc : ContDiff ℝ (N : WithTop ℕ∞) E) (hFc : ContDiff ℝ (N : WithTop ℕ∞) F)
    (hE : JetW N (fun k _ => Γ k * τ ^ k) E) (hF : JetW N (fun k _ => Γ' k * τ ^ k) F) :
    JetW N (fun k _ => mulγ Γ Γ' k * τ ^ k) (fun y => E y * F y) := by
  refine (JetW.mul hEc hFc hE hF).mono (fun k x => le_of_eq ?_)
  unfold mulγ
  rw [sum_mul]
  refine sum_congr rfl fun ij hij => ?_
  have := mem_antidiagonal.mp hij
  rw [← this, pow_add]
  ring

theorem JetW.tau_mono {N : ℕ} {Γ : ℕ → ℝ} {τ τ' : ℝ} {f : Mom d → ℂ} (hΓ : ∀ k, 0 ≤ Γ k)
    (hτ : 0 ≤ τ) (hle : τ ≤ τ') (h : JetW N (fun k _ => Γ k * τ ^ k) f) :
    JetW N (fun k _ => Γ k * τ' ^ k) f :=
  h.mono fun k _ => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hτ hle k) (hΓ k)

theorem JetW.vanish {N : ℕ} {r : ℝ} {e : ℕ → Mom d → ℝ} {g : Mom d → ℂ}
    (hg : ∀ y, ‖y‖ < r → g y = 0) (h : JetW N e g) :
    JetW N (fun k x => if ‖x‖ < r then 0 else e k x) g := by
  intro l hl x
  by_cases hx : ‖x‖ < r
  · simp [hx, wordD_eq_zero_of_ball r hg l x hx]
  · simp only [hx, ite_false]
    exact h l hl x

/-- Sums over antidiagonals of functions of the first coordinate. -/
theorem sum_antidiag_fst (n : ℕ) (g : ℕ → ℝ) :
    ∑ ij ∈ antidiagonal n, g ij.1 = ∑ i ∈ range (n + 1), g i := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

theorem gain_sum_le {n m : ℕ} (hnm : n ≤ m) {g : ℕ → ℝ} (hg : ∀ i, 0 ≤ g i) :
    ∑ i ∈ range (n + 1), (n.choose i : ℝ) * g i ≤ ∑ i ∈ range (m + 1), (m.choose i : ℝ) * g i := by
  calc ∑ i ∈ range (n + 1), (n.choose i : ℝ) * g i
      ≤ ∑ i ∈ range (n + 1), (m.choose i : ℝ) * g i :=
        sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_le_choose i hnm) (hg i)
    _ ≤ ∑ i ∈ range (m + 1), (m.choose i : ℝ) * g i :=
        sum_le_sum_of_subset_of_nonneg (range_mono (by omega : _ ≤ m + 1))
          fun i _ _ => mul_nonneg (Nat.cast_nonneg _) (hg i)

/-- The leading-term sum is at most `2` once the scale is large. -/
theorem lead_sum_le {n m : ℕ} (hnm : n ≤ m) {G : ℕ → ℝ} (hG : ∀ i, 0 ≤ G i) (hG0 : G 0 ≤ 1)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hS : τ * ∑ i ∈ range (m + 1), (m.choose i : ℝ) * G i ≤ 1) :
    ∑ i ∈ range (n + 1), (n.choose i : ℝ) * (G i * τ ^ i) ≤ 2 := by
  have h1 : ∀ i ∈ range (n + 1), (n.choose i : ℝ) * (G i * τ ^ i) ≤
      (if i = 0 then 1 else 0) + τ * ((m.choose i : ℝ) * G i) := by
    intro i hi
    have hch : (n.choose i : ℝ) ≤ m.choose i := by exact_mod_cast Nat.choose_le_choose i hnm
    by_cases h0 : i = 0
    · subst h0
      simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, one_mul, ite_true]
      have : 0 ≤ τ * ((m.choose 0 : ℝ) * G 0) := mul_nonneg hτ0 (mul_nonneg (Nat.cast_nonneg _) (hG 0))
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul] at this ⊢
      linarith
    · simp only [h0, ite_false, zero_add]
      have hpow : τ ^ i ≤ τ := by
        calc τ ^ i ≤ τ ^ 1 := pow_le_pow_of_le_one hτ0 hτ1 (Nat.one_le_iff_ne_zero.mpr h0)
          _ = τ := pow_one τ
      calc (n.choose i : ℝ) * (G i * τ ^ i) ≤ (m.choose i : ℝ) * (G i * τ) :=
            mul_le_mul hch (mul_le_mul_of_nonneg_left hpow (hG i))
              (mul_nonneg (hG i) (pow_nonneg hτ0 _)) (Nat.cast_nonneg _)
        _ = τ * ((m.choose i : ℝ) * G i) := by ring
  refine (sum_le_sum h1).trans ?_
  rw [sum_add_distrib, ← mul_sum]
  have h2 : ∑ i ∈ range (n + 1), (if i = 0 then (1 : ℝ) else 0) = 1 := by
    simp
  rw [h2]
  have h3 : ∑ i ∈ range (n + 1), (m.choose i : ℝ) * G i ≤ ∑ i ∈ range (m + 1), (m.choose i : ℝ) * G i :=
    sum_le_sum_of_subset_of_nonneg (range_mono (by omega : _ ≤ m + 1))
      fun i _ _ => mul_nonneg (Nat.cast_nonneg _) (hG i)
  have := mul_le_mul_of_nonneg_left h3 hτ0
  linarith

end WaveTurbulence.Flower.Typed
