/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.CompMK.Defs

/-! # C5b COMP-MK: the numerics of the component bound

* `markedExtra_le`: with `m ≤ 6·nProt` (`SoundMK`), `markedExtra cP π ≤ nProt·(cP·d + 840d + 40)` (B0's per-protected-
  vertex total `(60d+2)·14 + 12 + cP·d`).
* `bracket_le`: the class-sum bracket of `MarkedSumBoundAt(Sel)` is at most `δ^{7νn}` (main's `stage1_core_bound_int`
  numerics, plus `cθ^{40ν}δ^ν ≤ 1` for the filter constant).
* `budget_le`: R175's per-tree computation. With `|Π| ≤ 25R`, `a ≤ 2R` selected trees and the `2^a` grouping factor,
  `2^a·L^{25R(cP d+840d+40)}·L^{400d·a} ≤ L^{B·d·2R}` once `25(cP d + 840d + 40) + 800d + 2 ≤ 2Bd`.
* `budget_17999`: that inequality at `B = 17999` for `cP ≤ 500`, `d ≥ 1`
  (`25·1340d + 1000 + 800d + 2 = 34300d + 1002 ≤ 35998d`; B4 uses `cP = 452`, ruling R177). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs

namespace WaveTurbulence.Flower.CompMK

theorem markedExtra_le {P : WTParams} {R : ℕ} {cP : ℝ} (hcP : 0 ≤ cP) (π : Stage1PieceMK P.d R) {p : ℕ}
    (hπ : SoundMK (P := P) π p) {K : ℕ} (hK : π.nProt ≤ K) :
    markedExtra cP π ≤ (K : ℝ) * (cP * P.d + 840 * P.d + 40) := by
  unfold markedExtra
  have hm : (π.surv.m : ℝ) ≤ 6 * (π.nProt : ℝ) := by exact_mod_cast hπ.survivors_card
  have hn : (π.nProt : ℝ) ≤ K := by exact_mod_cast hK
  have hd : (0 : ℝ) ≤ P.d := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ π.nProt := Nat.cast_nonneg _
  have hc : 0 ≤ cP * P.d + 840 * P.d + 40 := by positivity
  have h1 : (60 * (P.d : ℝ) + 2) * (2 * (π.surv.m : ℝ) + 2 * (π.nProt : ℝ)) ≤
      (60 * (P.d : ℝ) + 2) * (14 * (π.nProt : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  calc cP * P.d * (π.nProt : ℝ) + (60 * P.d + 2) * (2 * (π.surv.m : ℝ) + 2 * (π.nProt : ℝ)) + 2 * (π.surv.m : ℝ)
      ≤ cP * P.d * (π.nProt : ℝ) + (60 * P.d + 2) * (14 * (π.nProt : ℝ)) + 12 * (π.nProt : ℝ) := by linarith
    _ = (π.nProt : ℝ) * (cP * P.d + 840 * P.d + 40) := by ring
    _ ≤ (K : ℝ) * (cP * P.d + 840 * P.d + 40) := mul_le_mul_of_nonneg_right hn hc

/-- **The class-sum bracket is at most `δ^{7νn}`.** -/
theorem bracket_le {P : WTParams} (hs : PieceSmall P) {C₀ : ℕ} {cθ : ℝ} (hcθ : 0 ≤ cθ) {n R : ℕ} (hR : 1 ≤ R)
    (hδ : ((6 * C₀ : ℕ) : ℝ) * P.C₁ ^ 6 * P.δ ^ (2 * P.ν) ≤ 1)
    (hθδ : cθ ^ (40 * P.ν) * P.δ ^ P.ν ≤ 1)
    (hL : 4 * (P.C₂ * ((((6 * C₀) * R).factorial : ℕ) : ℝ) *
        ((((6 * C₀) * n : ℕ) : ℝ) ^ (6 * C₀) * P.C₂ * P.L ^ (-P.η ^ 6 / 4)) *
        P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60))) ≤
      P.L ^ (-P.η ^ 7) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 70))) :
    4 * (P.C₂ * (cθ ^ (40 * P.ν) * P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) *
        ((6 * C₀ : ℕ) : ℝ) ^ n * ((((6 * C₀) * R).factorial : ℕ) : ℝ) *
        ((((6 * C₀) * n : ℕ) : ℝ) ^ (6 * C₀) * P.C₂ * P.L ^ (-P.η ^ 6 / 4))) ≤ P.δ ^ (7 * P.ν * n) := by
  have hδ0 := hs.delta_pos
  have hL1 : 1 ≤ P.L := by linarith [hs.L_ge]
  have hC₁ := hs.c1_ge
  set Y : ℝ := 4 * (P.C₂ * ((((6 * C₀) * R).factorial : ℕ) : ℝ) *
        ((((6 * C₀) * n : ℕ) : ℝ) ^ (6 * C₀) * P.C₂ * P.L ^ (-P.η ^ 6 / 4)) *
        P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60))) with hY
  have hY1 : Y ≤ 1 := by
    refine hL.trans ?_
    have h1 : P.L ^ (-P.η ^ 7) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hL1 (by have := hs.eta_pos; nlinarith [pow_pos this 7])
    have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
    have h2 : P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 70)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hL1 (by nlinarith)
    calc P.L ^ (-P.η ^ 7) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 70)) ≤ 1 * 1 :=
          mul_le_mul h1 h2 (Real.rpow_nonneg (by linarith) _) zero_le_one
      _ = 1 := by ring
  set A : ℝ := cθ ^ (40 * P.ν) * P.δ ^ P.ν with hA
  set Bq : ℝ := ((6 * C₀ : ℕ) : ℝ) * P.C₁ ^ 6 * P.δ ^ (2 * P.ν) with hBq
  have hA0 : 0 ≤ A := mul_nonneg (Real.rpow_nonneg hcθ _) (Real.rpow_nonneg hδ0.le _)
  have hB0 : 0 ≤ Bq := by rw [hBq]; positivity
  have hpow : (cθ ^ (40 * P.ν) * P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n * ((6 * C₀ : ℕ) : ℝ) ^ n =
      (A * Bq) ^ n * P.δ ^ (7 * P.ν * n) := by
    have h7 : P.δ ^ (7 * P.ν * (n : ℝ)) = (P.δ ^ (7 * P.ν)) ^ n := Real.rpow_mul_natCast hδ0.le _ _
    have h10 : P.δ ^ (10 * P.ν) = P.δ ^ P.ν * P.δ ^ (2 * P.ν) * P.δ ^ (7 * P.ν) := by
      rw [← Real.rpow_add hδ0, ← Real.rpow_add hδ0]; ring_nf
    rw [h7, ← mul_pow, ← mul_pow, h10, hA, hBq]
    congr 1; ring
  have hrearr : 4 * (P.C₂ * (cθ ^ (40 * P.ν) * P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n *
        P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) * ((6 * C₀ : ℕ) : ℝ) ^ n *
        ((((6 * C₀) * R).factorial : ℕ) : ℝ) *
        ((((6 * C₀) * n : ℕ) : ℝ) ^ (6 * C₀) * P.C₂ * P.L ^ (-P.η ^ 6 / 4))) =
      ((cθ ^ (40 * P.ν) * P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n * ((6 * C₀ : ℕ) : ℝ) ^ n) * Y := by
    rw [hY]; ring
  rw [hrearr, hpow]
  have hAB : (A * Bq) ^ n ≤ 1 := pow_le_one₀ (mul_nonneg hA0 hB0) (by
    calc A * Bq ≤ 1 * 1 := mul_le_mul hθδ hδ hB0 zero_le_one
      _ = 1 := by ring)
  have hδ7 : 0 ≤ P.δ ^ (7 * P.ν * (n : ℝ)) := Real.rpow_nonneg hδ0.le _
  have hY0 : 0 ≤ Y := by
    have hC₂ : 0 ≤ P.C₂ := by linarith [hs.c1_ge, hs.c1_le_c2]
    have hL0 : 0 < P.L := by linarith [hs.L_ge]
    rw [hY]; positivity
  calc (A * Bq) ^ n * P.δ ^ (7 * P.ν * (n : ℝ)) * Y ≤ 1 * P.δ ^ (7 * P.ν * (n : ℝ)) * 1 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hAB hδ7) hY1 hY0 (by positivity)
    _ = P.δ ^ (7 * P.ν * n) := by ring

/-- **The `L`-budget** (R175, per tree). -/
theorem budget_le {P : WTParams} (hL : 2 ≤ P.L) {cP B : ℝ} {R Tc : ℕ} (hT : Tc ≤ 2 * R) (hcP : 0 ≤ cP)
    (hbud : 25 * (cP * P.d + 840 * P.d + 40) + 800 * P.d + 2 ≤ 2 * B * P.d) :
    (2 : ℝ) ^ Tc * (P.L ^ ((25 * R : ℕ) * (cP * P.d + 840 * P.d + 40)) * P.L ^ (400 * (P.d : ℝ) * (Tc : ℝ))) ≤
      P.L ^ (B * P.d * ((2 * R : ℕ) : ℝ)) := by
  have hL0 : 0 < P.L := by linarith
  have hL1 : 1 ≤ P.L := by linarith
  have h2 : (2 : ℝ) ^ Tc ≤ P.L ^ (Tc : ℝ) := by
    rw [Real.rpow_natCast]; exact pow_le_pow_left₀ (by norm_num) hL _
  have hd : (0 : ℝ) ≤ P.d := Nat.cast_nonneg _
  have hTR : (Tc : ℝ) ≤ 2 * (R : ℝ) := by exact_mod_cast hT
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have hexp : (Tc : ℝ) + (((25 * R : ℕ) : ℝ) * (cP * P.d + 840 * P.d + 40) + 400 * (P.d : ℝ) * (Tc : ℝ)) ≤
      B * P.d * ((2 * R : ℕ) : ℝ) := by
    push_cast
    have h1 : 400 * (P.d : ℝ) * (Tc : ℝ) ≤ 400 * (P.d : ℝ) * (2 * R) :=
      mul_le_mul_of_nonneg_left hTR (by positivity)
    have h3 := mul_le_mul_of_nonneg_left hbud hR0
    nlinarith
  calc (2 : ℝ) ^ Tc * (P.L ^ (((25 * R : ℕ) : ℝ) * (cP * P.d + 840 * P.d + 40)) *
        P.L ^ (400 * (P.d : ℝ) * (Tc : ℝ)))
      ≤ P.L ^ (Tc : ℝ) * (P.L ^ (((25 * R : ℕ) : ℝ) * (cP * P.d + 840 * P.d + 40)) *
        P.L ^ (400 * (P.d : ℝ) * (Tc : ℝ))) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = P.L ^ ((Tc : ℝ) + (((25 * R : ℕ) : ℝ) * (cP * P.d + 840 * P.d + 40) + 400 * (P.d : ℝ) * (Tc : ℝ))) := by
        rw [Real.rpow_add hL0, Real.rpow_add hL0]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL1 hexp

/-- R175's arithmetic at `B = 17999` (one unit of slack below `18000` for the regular/non-regular split). -/
theorem budget_17999 {cP : ℝ} (hcP : cP ≤ 500) {d : ℕ} (hd : 1 ≤ d) :
    25 * (cP * d + 840 * d + 40) + 800 * d + 2 ≤ 2 * 17999 * (d : ℝ) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have : cP * d ≤ 500 * d := mul_le_mul_of_nonneg_right hcP (by linarith)
  nlinarith

end WaveTurbulence.Flower.CompMK
