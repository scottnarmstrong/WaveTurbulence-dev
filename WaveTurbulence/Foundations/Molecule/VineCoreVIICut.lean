/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-! # Core masks with cut at most two, type VII

The outer joints are absent. Explicit integer flows add directed edge
inequalities before the final arithmetic step. No bounded search replaces
a proof: every flow sum is checked by the Lean kernel. -/

public section
namespace WaveTurbulence.Vine

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreVII_cut_relation_2_zero (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+2*c 8+c 9+c 10+c 11+c 12+c 13+c 14+2*c 15 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 9+c 2 ∧ b 9 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 10+c 3 ∧ b 10 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 7+c 5 ∧ b 7 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 8+c 6 ∧ b 8 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 5 ≤ b 6+c 9 ∧ b 6 ≤ b 5+c 9)
    (_hd10 : b 5 ≤ b 7+c 10 ∧ b 7 ≤ b 5+c 10)
    (_hd11 : b 6 ≤ b 8+c 11 ∧ b 8 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 8+c 12 ∧ b 8 ≤ b 7+c 12)
    (_hd13 : b 7 ≤ b 9+c 13 ∧ b 9 ≤ b 7+c 13)
    (_hd14 : b 8 ≤ b 10+c 14 ∧ b 10 ≤ b 8+c 14)
    (_hd15 : b 9 ≤ b 10+c 15 ∧ b 10 ≤ b 9+c 15)
    : b 2=0 := by
  have hflow := (Nat.add_le_add _hd0.2 (Nat.add_le_add _hd1.2 (Nat.add_le_add _hd2.2 (Nat.add_le_add _hd4.1 (Nat.add_le_add _hd5.1 _hd13.1)))))
  have hbound : 3*b 2 ≤ (c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+2*c 8+c 9+c 10+c 11+c 12+c 13+c 14+2*c 15) := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreVII_cut_relation_3_zero (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+2*c 8+c 9+c 10+c 11+c 12+c 13+c 14+2*c 15 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 9+c 2 ∧ b 9 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 10+c 3 ∧ b 10 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 7+c 5 ∧ b 7 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 8+c 6 ∧ b 8 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 5 ≤ b 6+c 9 ∧ b 6 ≤ b 5+c 9)
    (_hd10 : b 5 ≤ b 7+c 10 ∧ b 7 ≤ b 5+c 10)
    (_hd11 : b 6 ≤ b 8+c 11 ∧ b 8 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 8+c 12 ∧ b 8 ≤ b 7+c 12)
    (_hd13 : b 7 ≤ b 9+c 13 ∧ b 9 ≤ b 7+c 13)
    (_hd14 : b 8 ≤ b 10+c 14 ∧ b 10 ≤ b 8+c 14)
    (_hd15 : b 9 ≤ b 10+c 15 ∧ b 10 ≤ b 9+c 15)
    : b 3=0 := by
  have hflow := (Nat.add_le_add _hd0.2 (Nat.add_le_add _hd1.2 (Nat.add_le_add _hd3.2 (Nat.add_le_add _hd4.2 (Nat.add_le_add _hd6.1 _hd14.1)))))
  have hbound : 3*b 3 ≤ (c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+2*c 8+c 9+c 10+c 11+c 12+c 13+c 14+2*c 15) := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreVII_cut_relation_5_4 (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+2*c 8+c 9+c 10+c 11+c 12+c 13+c 14+2*c 15 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 9+c 2 ∧ b 9 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 10+c 3 ∧ b 10 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 7+c 5 ∧ b 7 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 8+c 6 ∧ b 8 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 5 ≤ b 6+c 9 ∧ b 6 ≤ b 5+c 9)
    (_hd10 : b 5 ≤ b 7+c 10 ∧ b 7 ≤ b 5+c 10)
    (_hd11 : b 6 ≤ b 8+c 11 ∧ b 8 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 8+c 12 ∧ b 8 ≤ b 7+c 12)
    (_hd13 : b 7 ≤ b 9+c 13 ∧ b 9 ≤ b 7+c 13)
    (_hd14 : b 8 ≤ b 10+c 14 ∧ b 10 ≤ b 8+c 14)
    (_hd15 : b 9 ≤ b 10+c 15 ∧ b 10 ≤ b 9+c 15)
    : b 5 ≤ b 4 := by
  have hflow := (Nat.add_le_add _hd7.2 (Nat.add_le_add _hd7.2 (Nat.add_le_add _hd8.2 _hd9.1)))
  have hbound : 3*b 5 ≤ (c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+2*c 8+c 9+c 10+c 11+c 12+c 13+c 14+2*c 15)+3*b 4 := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreVII_cut_relation_4_5 (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+2*c 8+c 9+c 10+c 11+c 12+c 13+c 14+2*c 15 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 9+c 2 ∧ b 9 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 10+c 3 ∧ b 10 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 7+c 5 ∧ b 7 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 8+c 6 ∧ b 8 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 5 ≤ b 6+c 9 ∧ b 6 ≤ b 5+c 9)
    (_hd10 : b 5 ≤ b 7+c 10 ∧ b 7 ≤ b 5+c 10)
    (_hd11 : b 6 ≤ b 8+c 11 ∧ b 8 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 8+c 12 ∧ b 8 ≤ b 7+c 12)
    (_hd13 : b 7 ≤ b 9+c 13 ∧ b 9 ≤ b 7+c 13)
    (_hd14 : b 8 ≤ b 10+c 14 ∧ b 10 ≤ b 8+c 14)
    (_hd15 : b 9 ≤ b 10+c 15 ∧ b 10 ≤ b 9+c 15)
    : b 4 ≤ b 5 := by
  have hflow := (Nat.add_le_add _hd7.1 (Nat.add_le_add _hd7.1 (Nat.add_le_add _hd8.1 _hd9.2)))
  have hbound : 3*b 4 ≤ (c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+2*c 8+c 9+c 10+c 11+c 12+c 13+c 14+2*c 15)+3*b 5 := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreVII_cut_relation_6_4 (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+2*c 8+c 9+c 10+c 11+c 12+c 13+c 14+2*c 15 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 9+c 2 ∧ b 9 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 10+c 3 ∧ b 10 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 7+c 5 ∧ b 7 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 8+c 6 ∧ b 8 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 5 ≤ b 6+c 9 ∧ b 6 ≤ b 5+c 9)
    (_hd10 : b 5 ≤ b 7+c 10 ∧ b 7 ≤ b 5+c 10)
    (_hd11 : b 6 ≤ b 8+c 11 ∧ b 8 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 8+c 12 ∧ b 8 ≤ b 7+c 12)
    (_hd13 : b 7 ≤ b 9+c 13 ∧ b 9 ≤ b 7+c 13)
    (_hd14 : b 8 ≤ b 10+c 14 ∧ b 10 ≤ b 8+c 14)
    (_hd15 : b 9 ≤ b 10+c 15 ∧ b 10 ≤ b 9+c 15)
    : b 6 ≤ b 4 := by
  have hflow := (Nat.add_le_add _hd7.2 (Nat.add_le_add _hd8.2 (Nat.add_le_add _hd8.2 _hd9.2)))
  have hbound : 3*b 6 ≤ (c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+2*c 8+c 9+c 10+c 11+c 12+c 13+c 14+2*c 15)+3*b 4 := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreVII_cut_relation_4_6 (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+2*c 8+c 9+c 10+c 11+c 12+c 13+c 14+2*c 15 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 9+c 2 ∧ b 9 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 10+c 3 ∧ b 10 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 7+c 5 ∧ b 7 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 8+c 6 ∧ b 8 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 5 ≤ b 6+c 9 ∧ b 6 ≤ b 5+c 9)
    (_hd10 : b 5 ≤ b 7+c 10 ∧ b 7 ≤ b 5+c 10)
    (_hd11 : b 6 ≤ b 8+c 11 ∧ b 8 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 8+c 12 ∧ b 8 ≤ b 7+c 12)
    (_hd13 : b 7 ≤ b 9+c 13 ∧ b 9 ≤ b 7+c 13)
    (_hd14 : b 8 ≤ b 10+c 14 ∧ b 10 ≤ b 8+c 14)
    (_hd15 : b 9 ≤ b 10+c 15 ∧ b 10 ≤ b 9+c 15)
    : b 4 ≤ b 6 := by
  have hflow := (Nat.add_le_add _hd7.1 (Nat.add_le_add _hd8.1 (Nat.add_le_add _hd8.1 _hd9.1)))
  have hbound : 3*b 4 ≤ (c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+2*c 8+c 9+c 10+c 11+c 12+c 13+c 14+2*c 15)+3*b 6 := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreVII_cut_relation_7_zero (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+2*c 8+c 9+c 10+c 11+c 12+c 13+c 14+2*c 15 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 9+c 2 ∧ b 9 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 10+c 3 ∧ b 10 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 7+c 5 ∧ b 7 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 8+c 6 ∧ b 8 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 5 ≤ b 6+c 9 ∧ b 6 ≤ b 5+c 9)
    (_hd10 : b 5 ≤ b 7+c 10 ∧ b 7 ≤ b 5+c 10)
    (_hd11 : b 6 ≤ b 8+c 11 ∧ b 8 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 8+c 12 ∧ b 8 ≤ b 7+c 12)
    (_hd13 : b 7 ≤ b 9+c 13 ∧ b 9 ≤ b 7+c 13)
    (_hd14 : b 8 ≤ b 10+c 14 ∧ b 10 ≤ b 8+c 14)
    (_hd15 : b 9 ≤ b 10+c 15 ∧ b 10 ≤ b 9+c 15)
    : b 7=0 := by
  have hflow := (Nat.add_le_add _hd0.2 (Nat.add_le_add _hd1.2 (Nat.add_le_add _hd2.2 (Nat.add_le_add _hd5.2 (Nat.add_le_add _hd6.2 (Nat.add_le_add _hd12.1 _hd13.1))))))
  have hbound : 3*b 7 ≤ (c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+2*c 8+c 9+c 10+c 11+c 12+c 13+c 14+2*c 15) := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreVII_cut_relation_8_zero (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+2*c 8+c 9+c 10+c 11+c 12+c 13+c 14+2*c 15 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 9+c 2 ∧ b 9 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 10+c 3 ∧ b 10 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 7+c 5 ∧ b 7 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 8+c 6 ∧ b 8 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 5 ≤ b 6+c 9 ∧ b 6 ≤ b 5+c 9)
    (_hd10 : b 5 ≤ b 7+c 10 ∧ b 7 ≤ b 5+c 10)
    (_hd11 : b 6 ≤ b 8+c 11 ∧ b 8 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 8+c 12 ∧ b 8 ≤ b 7+c 12)
    (_hd13 : b 7 ≤ b 9+c 13 ∧ b 9 ≤ b 7+c 13)
    (_hd14 : b 8 ≤ b 10+c 14 ∧ b 10 ≤ b 8+c 14)
    (_hd15 : b 9 ≤ b 10+c 15 ∧ b 10 ≤ b 9+c 15)
    : b 8=0 := by
  have hflow := (Nat.add_le_add _hd0.2 (Nat.add_le_add _hd1.2 (Nat.add_le_add _hd3.2 (Nat.add_le_add _hd5.2 (Nat.add_le_add _hd6.2 (Nat.add_le_add _hd12.2 _hd14.1))))))
  have hbound : 3*b 8 ≤ (c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+2*c 8+c 9+c 10+c 11+c 12+c 13+c 14+2*c 15) := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreVII_cut_relation_9_zero (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+2*c 8+c 9+c 10+c 11+c 12+c 13+c 14+2*c 15 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 9+c 2 ∧ b 9 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 10+c 3 ∧ b 10 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 7+c 5 ∧ b 7 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 8+c 6 ∧ b 8 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 5 ≤ b 6+c 9 ∧ b 6 ≤ b 5+c 9)
    (_hd10 : b 5 ≤ b 7+c 10 ∧ b 7 ≤ b 5+c 10)
    (_hd11 : b 6 ≤ b 8+c 11 ∧ b 8 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 8+c 12 ∧ b 8 ≤ b 7+c 12)
    (_hd13 : b 7 ≤ b 9+c 13 ∧ b 9 ≤ b 7+c 13)
    (_hd14 : b 8 ≤ b 10+c 14 ∧ b 10 ≤ b 8+c 14)
    (_hd15 : b 9 ≤ b 10+c 15 ∧ b 10 ≤ b 9+c 15)
    : b 9=0 := by
  have hflow := (Nat.add_le_add _hd0.2 (Nat.add_le_add _hd2.2 (Nat.add_le_add _hd3.2 (Nat.add_le_add _hd5.2 (Nat.add_le_add _hd13.2 _hd15.1)))))
  have hbound : 3*b 9 ≤ (c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+2*c 8+c 9+c 10+c 11+c 12+c 13+c 14+2*c 15) := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreVII_cut_relation_10_zero (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+2*c 8+c 9+c 10+c 11+c 12+c 13+c 14+2*c 15 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 9+c 2 ∧ b 9 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 10+c 3 ∧ b 10 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 7+c 5 ∧ b 7 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 8+c 6 ∧ b 8 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 5 ≤ b 6+c 9 ∧ b 6 ≤ b 5+c 9)
    (_hd10 : b 5 ≤ b 7+c 10 ∧ b 7 ≤ b 5+c 10)
    (_hd11 : b 6 ≤ b 8+c 11 ∧ b 8 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 8+c 12 ∧ b 8 ≤ b 7+c 12)
    (_hd13 : b 7 ≤ b 9+c 13 ∧ b 9 ≤ b 7+c 13)
    (_hd14 : b 8 ≤ b 10+c 14 ∧ b 10 ≤ b 8+c 14)
    (_hd15 : b 9 ≤ b 10+c 15 ∧ b 10 ≤ b 9+c 15)
    : b 10=0 := by
  have hflow := (Nat.add_le_add _hd1.2 (Nat.add_le_add _hd2.2 (Nat.add_le_add _hd3.2 (Nat.add_le_add _hd6.2 (Nat.add_le_add _hd14.2 _hd15.2)))))
  have hbound : 3*b 10 ≤ (c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+2*c 8+c 9+c 10+c 11+c 12+c 13+c 14+2*c 15) := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 hflow
  omega

/-- The literal type-VII core has only these two-edge cut masks away from its joints. -/
theorem coreVII_cut_masks (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hb : ∀ i < 11,b i ≤ 1) (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+2*c 8+c 9+c 10+c 11+c 12+c 13+c 14+2*c 15 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 9+c 2 ∧ b 9 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 10+c 3 ∧ b 10 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 7+c 5 ∧ b 7 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 8+c 6 ∧ b 8 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 5 ≤ b 6+c 9 ∧ b 6 ≤ b 5+c 9)
    (_hd10 : b 5 ≤ b 7+c 10 ∧ b 7 ≤ b 5+c 10)
    (_hd11 : b 6 ≤ b 8+c 11 ∧ b 8 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 8+c 12 ∧ b 8 ≤ b 7+c 12)
    (_hd13 : b 7 ≤ b 9+c 13 ∧ b 9 ≤ b 7+c 13)
    (_hd14 : b 8 ≤ b 10+c 14 ∧ b 10 ≤ b 8+c 14)
    (_hd15 : b 9 ≤ b 10+c 15 ∧ b 10 ≤ b 9+c 15)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9,b 10] ∈ ([[0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,1,1,1,0,0,0,0]] : List (List ℕ)) := by
  have hrel2_zero := coreVII_cut_relation_2_zero b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15
  have hrel3_zero := coreVII_cut_relation_3_zero b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15
  have hrel5_4 := coreVII_cut_relation_5_4 b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15
  have hrel4_5 := coreVII_cut_relation_4_5 b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15
  have hrel6_4 := coreVII_cut_relation_6_4 b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15
  have hrel4_6 := coreVII_cut_relation_4_6 b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15
  have hrel7_zero := coreVII_cut_relation_7_zero b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15
  have hrel8_zero := coreVII_cut_relation_8_zero b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15
  have hrel9_zero := coreVII_cut_relation_9_zero b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15
  have hrel10_zero := coreVII_cut_relation_10_zero b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15
  have hb4 := _hb 4 (by decide)
  clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 c _hb
  simp only [List.mem_cons,List.not_mem_nil,or_false,List.cons.injEq,and_true]
  omega

end WaveTurbulence.Vine
