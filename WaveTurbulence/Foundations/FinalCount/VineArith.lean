/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.Prop94Cut
/-! Vine removal, part 7 (FINALCOUNT-G2): the real inequality of DH23 L1801,
`R^d L^{2γ} (log L)^C ≲ L^{-η³} R² L^{γ+3η}` (here with the label `κ`, `a = κη`, and the gap radius `ρ ≤ 2 L^{-a} R`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
namespace WaveTurbulence.FinalCount

theorem rpow_sq (L x : ℝ) (hL : 0 < L) : (L ^ x) ^ 2 = L ^ (2 * x) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]; congr 1; push_cast; ring

/-- **The Step 1 arithmetic** (L1801). -/
theorem vine_arith (d : ℕ) {L γ η a R ρ : ℝ} (E : ℕ) (hd : 3 ≤ d) (hη : 0 < η) (hη1 : η < 1) (hηγ : η ≤ γ)
    (ha : 0 ≤ a) (hL : Real.exp 1 ≤ L) (hR0 : 0 ≤ R) (hRu : R ≤ L ^ (-γ + η)) (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ 2 * L ^ (-a) * R) :
    ρ ^ d * L ^ (2 * γ) * Real.log L ^ E ≤
      (2 ^ d * (((E + 1 : ℕ) : ℝ) / (2 * η - η ^ 3)) ^ (E + 1)) *
        (L ^ (-η ^ 3) * (L ^ ((γ + 3 * η) / 2 - a) * R) ^ 2) := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  have hlog1 : 1 ≤ Real.log L := by
    have := Real.log_le_log (Real.exp_pos 1) hL
    rwa [Real.log_exp] at this
  have hε : 0 < 2 * η - η ^ 3 := by nlinarith [pow_pos hη 2, pow_pos hη 3]
  have hLa : L ^ (-a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  have hLa0 : 0 ≤ L ^ (-a) := Real.rpow_nonneg hL0.le _
  have hR1 : R ≤ 1 := hRu.trans (Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith))
  -- R^d
  have hRd : R ^ d ≤ R ^ 2 * L ^ (-γ + η) := by
    have h1 : R ^ d ≤ R ^ 3 := pow_le_pow_of_le_one hR0 hR1 hd
    have h2 : R ^ 3 = R ^ 2 * R := by ring
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hRu (by positivity))
  -- ρ^d
  have hρd : ρ ^ d ≤ 2 ^ d * (L ^ (-a)) ^ 3 * R ^ d := by
    have h1 : ρ ^ d ≤ (2 * L ^ (-a) * R) ^ d := pow_le_pow_left₀ hρ0 hρ d
    have h2 : (L ^ (-a)) ^ d ≤ (L ^ (-a)) ^ 3 := pow_le_pow_of_le_one hLa0 hLa hd
    calc ρ ^ d ≤ (2 * L ^ (-a) * R) ^ d := h1
      _ = 2 ^ d * (L ^ (-a)) ^ d * R ^ d := by rw [mul_pow, mul_pow]
      _ ≤ 2 ^ d * (L ^ (-a)) ^ 3 * R ^ d := by gcongr
  have hlogp : Real.log L ^ E ≤ (((E + 1 : ℕ) : ℝ) / (2 * η - η ^ 3)) ^ (E + 1) * L ^ (2 * η - η ^ 3) := by
    refine (pow_le_pow_right₀ hlog1 (Nat.le_succ E)).trans ?_
    exact log_pow_le (E + 1) (by omega) L _ hL1 hε
  set K : ℝ := (((E + 1 : ℕ) : ℝ) / (2 * η - η ^ 3)) ^ (E + 1) with hK
  have hK0 : 0 ≤ K := by positivity
  -- exponent bookkeeping
  have e1 : (L ^ (-a)) ^ 3 = L ^ (-3 * a) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; push_cast; ring
  have e2 : (L ^ ((γ + 3 * η) / 2 - a)) ^ 2 = L ^ (γ + 3 * η - 2 * a) := by
    rw [rpow_sq L _ hL0]; ring_nf
  have key : L ^ (-3 * a) * (L ^ (-γ + η) * L ^ (2 * γ)) * L ^ (2 * η - η ^ 3) ≤
      L ^ (-η ^ 3) * L ^ (γ + 3 * η - 2 * a) := by
    rw [← Real.rpow_add hL0 (-γ + η) (2 * γ), ← Real.rpow_add hL0 (-3 * a) _,
      ← Real.rpow_add hL0 _ (2 * η - η ^ 3), ← Real.rpow_add hL0 (-η ^ 3) (γ + 3 * η - 2 * a)]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by nlinarith)
  have hρd' : ρ ^ d ≤ 2 ^ d * (L ^ (-a)) ^ 3 * (R ^ 2 * L ^ (-γ + η)) :=
    hρd.trans (mul_le_mul_of_nonneg_left hRd (by positivity))
  calc ρ ^ d * L ^ (2 * γ) * Real.log L ^ E
      ≤ (2 ^ d * (L ^ (-a)) ^ 3 * (R ^ 2 * L ^ (-γ + η))) * L ^ (2 * γ) * (K * L ^ (2 * η - η ^ 3)) := by
        gcongr
    _ = (2 ^ d * K) * (R ^ 2 * (L ^ (-3 * a) * (L ^ (-γ + η) * L ^ (2 * γ)) * L ^ (2 * η - η ^ 3))) := by
        rw [e1]; ring
    _ ≤ (2 ^ d * K) * (R ^ 2 * (L ^ (-η ^ 3) * L ^ (γ + 3 * η - 2 * a))) := by gcongr
    _ = (2 ^ d * K) * (L ^ (-η ^ 3) * (L ^ ((γ + 3 * η) / 2 - a) * R) ^ 2) := by
        rw [mul_pow, e2]; ring

end WaveTurbulence.FinalCount
