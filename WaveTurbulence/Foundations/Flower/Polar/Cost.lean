/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Polar.Defs
public import WaveTurbulence.Foundations.Spine.CentralDiffC
/-! # FL-POLAR: the polarization cost `rootPolarCost` and its `E · K^N` bound. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.Flower.Polar
open Finset

/-- The explicit bound of the total variation `∑_m |w_m / λ|` of the central-difference weights, for the
admissible step `λ`; `M = N + Pm + 1`, `R = m (2 Pm)` rounds. -/
def rootPolarT (d m Pm N : ℕ) : ℝ :=
  ((2 * (N + Pm + 1) + 1 : ℕ) : ℝ) * ((N + Pm + 1 : ℕ) : ℝ) *
    ((2 : ℝ) ^ (40 * d) * (d : ℝ) ^ (40 * d)) * (4 * (((m * (2 * Pm) : ℕ) : ℝ) + 1))

/-- The cost of the root decay by polarization: one factor `1 + d T²` per round. -/
def rootPolarCost (d m Pm N : ℕ) : ℝ := (1 + d * rootPolarT d m Pm N ^ 2) ^ (m * (2 * Pm))

/-- The `N`-independent prefactor. -/
def rootPolarE (d m Pm : ℕ) : ℝ :=
  (1 + 144 * d * (((m * (2 * Pm) : ℕ) : ℝ) + 1) ^ 2 * ((2 : ℝ) ^ (40 * d) * (d : ℝ) ^ (40 * d)) ^ 2) ^
      (m * (2 * Pm)) * ((Nat.factorial (4 * (m * (2 * Pm))) : ℕ) : ℝ) * 3 ^ (Pm + 1)

/-- The exponential base (independent of `δ`, and of `d`). -/
def rootPolarK (_d : ℕ) : ℝ := 3

theorem abs_cw_le_one (M k : ℕ) : |LGSpine.CentralDiff.cw M k| ≤ 1 := by
  by_cases hk : k = M
  · simp [LGSpine.CentralDiff.cw, hk]
  · refine (LGSpine.CentralDiff.abs_cw_le M k hk).trans ?_
    have h1 : (1 : ℤ) ≤ |(k : ℤ) - M| := Int.one_le_abs (by omega)
    have h2 : (1 : ℝ) ≤ |(k : ℝ) - M| := by exact_mod_cast h1
    rw [div_le_one (by linarith)]
    exact h2

theorem sum_abs_cw_div_le (M : ℕ) (lam : ℝ) (hlam : 0 < lam) :
    ∑ m ∈ range (2 * M + 1), |LGSpine.CentralDiff.cw M m / lam| ≤ ((2 * M + 1 : ℕ) : ℝ) / lam := by
  calc _ ≤ ∑ _m ∈ range (2 * M + 1), (1 / lam) := by
        refine sum_le_sum fun m _ => ?_
        rw [abs_div, abs_of_pos hlam]
        exact div_le_div_of_nonneg_right (abs_cw_le_one M m) hlam.le
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

theorem rootPolarCost_le (d m Pm N : ℕ) :
    rootPolarCost d m Pm N ≤ rootPolarE d m Pm * rootPolarK d ^ N := by
  set R : ℕ := m * (2 * Pm) with hR
  set E0 : ℝ := (2 : ℝ) ^ (40 * d) * (d : ℝ) ^ (40 * d) with hE0
  set Mr : ℝ := ((N + Pm + 1 : ℕ) : ℝ) with hMr
  have hM1 : (1 : ℝ) ≤ Mr := by rw [hMr]; exact_mod_cast Nat.le_add_left 1 (N + Pm)
  have hE0nn : 0 ≤ E0 := by positivity
  have hRr : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg _
  have h2M : ((2 * (N + Pm + 1) + 1 : ℕ) : ℝ) ≤ 3 * Mr := by
    rw [hMr]; push_cast; nlinarith
  have hT : rootPolarT d m Pm N ≤ 12 * ((R : ℝ) + 1) * E0 * Mr ^ 2 := by
    unfold rootPolarT
    rw [← hR, ← hE0, ← hMr]
    have h3 : ((2 * (N + Pm + 1) + 1 : ℕ) : ℝ) * Mr ≤ 3 * Mr ^ 2 := by nlinarith
    calc ((2 * (N + Pm + 1) + 1 : ℕ) : ℝ) * Mr * E0 * (4 * ((R : ℝ) + 1))
        = (((2 * (N + Pm + 1) + 1 : ℕ) : ℝ) * Mr) * (E0 * (4 * ((R : ℝ) + 1))) := by ring
      _ ≤ (3 * Mr ^ 2) * (E0 * (4 * ((R : ℝ) + 1))) := by gcongr
      _ = _ := by ring
  have hT0 : 0 ≤ rootPolarT d m Pm N := by
    unfold rootPolarT; positivity
  set c1 : ℝ := 1 + 144 * d * ((R : ℝ) + 1) ^ 2 * E0 ^ 2 with hc1
  have hc10 : 0 ≤ c1 := by positivity
  have hbase : 1 + d * rootPolarT d m Pm N ^ 2 ≤ c1 * Mr ^ 4 := by
    have h1 : rootPolarT d m Pm N ^ 2 ≤ (12 * ((R : ℝ) + 1) * E0 * Mr ^ 2) ^ 2 :=
      pow_le_pow_left₀ hT0 hT 2
    have h4 : (1 : ℝ) ≤ Mr ^ 4 := one_le_pow₀ hM1
    calc 1 + d * rootPolarT d m Pm N ^ 2 ≤ 1 + d * (12 * ((R : ℝ) + 1) * E0 * Mr ^ 2) ^ 2 := by gcongr
      _ = 1 + 144 * d * ((R : ℝ) + 1) ^ 2 * E0 ^ 2 * Mr ^ 4 := by ring
      _ ≤ c1 * Mr ^ 4 := by rw [hc1]; nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 144) (Nat.cast_nonneg d)) (sq_nonneg ((R : ℝ) + 1))) (sq_nonneg E0)]
  have hpow : rootPolarCost d m Pm N ≤ c1 ^ R * Mr ^ (4 * R) := by
    unfold rootPolarCost
    rw [← hR]
    calc _ ≤ (c1 * Mr ^ 4) ^ R := pow_le_pow_left₀ (by positivity) hbase R
      _ = _ := by rw [mul_pow, ← pow_mul]
  have hfac : Mr ^ (4 * R) ≤ ((Nat.factorial (4 * R) : ℕ) : ℝ) * Real.exp Mr := by
    have := Real.pow_div_factorial_le_exp Mr (by linarith) (4 * R)
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have hexp : Real.exp Mr ≤ 3 ^ (Pm + 1) * 3 ^ N := by
    have hsplit : Mr = ((Pm + 1 : ℕ) : ℝ) + (N : ℝ) := by rw [hMr]; push_cast; ring
    have he1 : Real.exp 1 ≤ 3 := (Real.exp_one_lt_d9.le).trans (by norm_num)
    have hk : ∀ k : ℕ, Real.exp (k : ℝ) ≤ 3 ^ k := by
      intro k
      have : Real.exp (k : ℝ) = Real.exp 1 ^ k := by
        rw [← Real.exp_nat_mul]; ring_nf
      rw [this]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le he1 k
    rw [hsplit, Real.exp_add]
    exact mul_le_mul (hk _) (hk _) (Real.exp_pos _).le (by positivity)
  calc rootPolarCost d m Pm N ≤ c1 ^ R * Mr ^ (4 * R) := hpow
    _ ≤ c1 ^ R * (((Nat.factorial (4 * R) : ℕ) : ℝ) * (3 ^ (Pm + 1) * 3 ^ N)) := by
        gcongr
        exact hfac.trans (by gcongr)
    _ = rootPolarE d m Pm * rootPolarK d ^ N := by
        unfold rootPolarE rootPolarK
        rw [← hR, ← hE0, ← hc1]
        ring

end WaveTurbulence.Flower.Polar
