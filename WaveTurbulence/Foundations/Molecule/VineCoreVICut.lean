/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-! # Core masks with cut at most two, type VI

The outer joints are absent. Explicit integer flows add directed edge
inequalities before the final arithmetic step. No bounded search replaces
a proof: every flow sum is checked by the Lean kernel. -/

public section
namespace WaveTurbulence.Vine

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreVI_cut_relation_2_zero (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+c 8+c 9+2*c 10+c 11+c 12+c 13+2*c 14+c 15+c 16+c 17+2*c 18+2*c 19+2*c 20 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 13+c 2 ∧ b 13 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 14+c 3 ∧ b 14 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 4+c 5 ∧ b 4 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 5+c 6 ∧ b 5 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 5 ≤ b 8+c 9 ∧ b 8 ≤ b 5+c 9)
    (_hd10 : b 6 ≤ b 7+c 10 ∧ b 7 ≤ b 6+c 10)
    (_hd11 : b 6 ≤ b 13+c 11 ∧ b 13 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 9+c 12 ∧ b 9 ≤ b 7+c 12)
    (_hd13 : b 7 ≤ b 14+c 13 ∧ b 14 ≤ b 7+c 13)
    (_hd14 : b 8 ≤ b 9+c 14 ∧ b 9 ≤ b 8+c 14)
    (_hd15 : b 8 ≤ b 10+c 15 ∧ b 10 ≤ b 8+c 15)
    (_hd16 : b 9 ≤ b 11+c 16 ∧ b 11 ≤ b 9+c 16)
    (_hd17 : b 10 ≤ b 11+c 17 ∧ b 11 ≤ b 10+c 17)
    (_hd18 : b 10 ≤ b 12+c 18 ∧ b 12 ≤ b 10+c 18)
    (_hd19 : b 11 ≤ b 12+c 19 ∧ b 12 ≤ b 11+c 19)
    (_hd20 : b 13 ≤ b 14+c 20 ∧ b 14 ≤ b 13+c 20)
    : b 2=0 := by
  have hflow := (Nat.add_le_add _hd0.2 (Nat.add_le_add _hd1.2 (Nat.add_le_add _hd2.2 (Nat.add_le_add _hd4.1 (Nat.add_le_add _hd5.1 (Nat.add_le_add _hd8.1 _hd11.1))))))
  have hbound : 3*b 2 ≤ (c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+c 8+c 9+2*c 10+c 11+c 12+c 13+2*c 14+c 15+c 16+c 17+2*c 18+2*c 19+2*c 20) := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreVI_cut_relation_3_zero (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+c 8+c 9+2*c 10+c 11+c 12+c 13+2*c 14+c 15+c 16+c 17+2*c 18+2*c 19+2*c 20 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 13+c 2 ∧ b 13 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 14+c 3 ∧ b 14 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 4+c 5 ∧ b 4 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 5+c 6 ∧ b 5 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 5 ≤ b 8+c 9 ∧ b 8 ≤ b 5+c 9)
    (_hd10 : b 6 ≤ b 7+c 10 ∧ b 7 ≤ b 6+c 10)
    (_hd11 : b 6 ≤ b 13+c 11 ∧ b 13 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 9+c 12 ∧ b 9 ≤ b 7+c 12)
    (_hd13 : b 7 ≤ b 14+c 13 ∧ b 14 ≤ b 7+c 13)
    (_hd14 : b 8 ≤ b 9+c 14 ∧ b 9 ≤ b 8+c 14)
    (_hd15 : b 8 ≤ b 10+c 15 ∧ b 10 ≤ b 8+c 15)
    (_hd16 : b 9 ≤ b 11+c 16 ∧ b 11 ≤ b 9+c 16)
    (_hd17 : b 10 ≤ b 11+c 17 ∧ b 11 ≤ b 10+c 17)
    (_hd18 : b 10 ≤ b 12+c 18 ∧ b 12 ≤ b 10+c 18)
    (_hd19 : b 11 ≤ b 12+c 19 ∧ b 12 ≤ b 11+c 19)
    (_hd20 : b 13 ≤ b 14+c 20 ∧ b 14 ≤ b 13+c 20)
    : b 3=0 := by
  have hflow := (Nat.add_le_add _hd0.2 (Nat.add_le_add _hd1.2 (Nat.add_le_add _hd2.2 (Nat.add_le_add _hd4.2 (Nat.add_le_add _hd4.2 (Nat.add_le_add _hd5.1 (Nat.add_le_add _hd8.1 _hd11.1)))))))
  have hbound : 3*b 3 ≤ (c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+c 8+c 9+2*c 10+c 11+c 12+c 13+2*c 14+c 15+c 16+c 17+2*c 18+2*c 19+2*c 20) := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreVI_cut_relation_4_zero (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+c 8+c 9+2*c 10+c 11+c 12+c 13+2*c 14+c 15+c 16+c 17+2*c 18+2*c 19+2*c 20 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 13+c 2 ∧ b 13 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 14+c 3 ∧ b 14 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 4+c 5 ∧ b 4 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 5+c 6 ∧ b 5 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 5 ≤ b 8+c 9 ∧ b 8 ≤ b 5+c 9)
    (_hd10 : b 6 ≤ b 7+c 10 ∧ b 7 ≤ b 6+c 10)
    (_hd11 : b 6 ≤ b 13+c 11 ∧ b 13 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 9+c 12 ∧ b 9 ≤ b 7+c 12)
    (_hd13 : b 7 ≤ b 14+c 13 ∧ b 14 ≤ b 7+c 13)
    (_hd14 : b 8 ≤ b 9+c 14 ∧ b 9 ≤ b 8+c 14)
    (_hd15 : b 8 ≤ b 10+c 15 ∧ b 10 ≤ b 8+c 15)
    (_hd16 : b 9 ≤ b 11+c 16 ∧ b 11 ≤ b 9+c 16)
    (_hd17 : b 10 ≤ b 11+c 17 ∧ b 11 ≤ b 10+c 17)
    (_hd18 : b 10 ≤ b 12+c 18 ∧ b 12 ≤ b 10+c 18)
    (_hd19 : b 11 ≤ b 12+c 19 ∧ b 12 ≤ b 11+c 19)
    (_hd20 : b 13 ≤ b 14+c 20 ∧ b 14 ≤ b 13+c 20)
    : b 4=0 := by
  have hflow := (Nat.add_le_add _hd0.2 (Nat.add_le_add _hd1.2 (Nat.add_le_add _hd2.2 (Nat.add_le_add _hd5.2 (Nat.add_le_add _hd6.2 (Nat.add_le_add _hd7.1 (Nat.add_le_add _hd8.1 _hd11.1)))))))
  have hbound : 3*b 4 ≤ (c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+c 8+c 9+2*c 10+c 11+c 12+c 13+2*c 14+c 15+c 16+c 17+2*c 18+2*c 19+2*c 20) := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreVI_cut_relation_5_zero (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+c 8+c 9+2*c 10+c 11+c 12+c 13+2*c 14+c 15+c 16+c 17+2*c 18+2*c 19+2*c 20 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 13+c 2 ∧ b 13 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 14+c 3 ∧ b 14 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 4+c 5 ∧ b 4 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 5+c 6 ∧ b 5 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 5 ≤ b 8+c 9 ∧ b 8 ≤ b 5+c 9)
    (_hd10 : b 6 ≤ b 7+c 10 ∧ b 7 ≤ b 6+c 10)
    (_hd11 : b 6 ≤ b 13+c 11 ∧ b 13 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 9+c 12 ∧ b 9 ≤ b 7+c 12)
    (_hd13 : b 7 ≤ b 14+c 13 ∧ b 14 ≤ b 7+c 13)
    (_hd14 : b 8 ≤ b 9+c 14 ∧ b 9 ≤ b 8+c 14)
    (_hd15 : b 8 ≤ b 10+c 15 ∧ b 10 ≤ b 8+c 15)
    (_hd16 : b 9 ≤ b 11+c 16 ∧ b 11 ≤ b 9+c 16)
    (_hd17 : b 10 ≤ b 11+c 17 ∧ b 11 ≤ b 10+c 17)
    (_hd18 : b 10 ≤ b 12+c 18 ∧ b 12 ≤ b 10+c 18)
    (_hd19 : b 11 ≤ b 12+c 19 ∧ b 12 ≤ b 11+c 19)
    (_hd20 : b 13 ≤ b 14+c 20 ∧ b 14 ≤ b 13+c 20)
    : b 5=0 := by
  have hflow := (Nat.add_le_add _hd0.2 (Nat.add_le_add _hd1.2 (Nat.add_le_add _hd2.2 (Nat.add_le_add _hd5.2 (Nat.add_le_add _hd6.2 (Nat.add_le_add _hd7.2 (Nat.add_le_add _hd7.2 (Nat.add_le_add _hd8.1 _hd11.1))))))))
  have hbound : 3*b 5 ≤ (c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+c 8+c 9+2*c 10+c 11+c 12+c 13+2*c 14+c 15+c 16+c 17+2*c 18+2*c 19+2*c 20) := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreVI_cut_relation_6_zero (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+c 8+c 9+2*c 10+c 11+c 12+c 13+2*c 14+c 15+c 16+c 17+2*c 18+2*c 19+2*c 20 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 13+c 2 ∧ b 13 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 14+c 3 ∧ b 14 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 4+c 5 ∧ b 4 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 5+c 6 ∧ b 5 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 5 ≤ b 8+c 9 ∧ b 8 ≤ b 5+c 9)
    (_hd10 : b 6 ≤ b 7+c 10 ∧ b 7 ≤ b 6+c 10)
    (_hd11 : b 6 ≤ b 13+c 11 ∧ b 13 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 9+c 12 ∧ b 9 ≤ b 7+c 12)
    (_hd13 : b 7 ≤ b 14+c 13 ∧ b 14 ≤ b 7+c 13)
    (_hd14 : b 8 ≤ b 9+c 14 ∧ b 9 ≤ b 8+c 14)
    (_hd15 : b 8 ≤ b 10+c 15 ∧ b 10 ≤ b 8+c 15)
    (_hd16 : b 9 ≤ b 11+c 16 ∧ b 11 ≤ b 9+c 16)
    (_hd17 : b 10 ≤ b 11+c 17 ∧ b 11 ≤ b 10+c 17)
    (_hd18 : b 10 ≤ b 12+c 18 ∧ b 12 ≤ b 10+c 18)
    (_hd19 : b 11 ≤ b 12+c 19 ∧ b 12 ≤ b 11+c 19)
    (_hd20 : b 13 ≤ b 14+c 20 ∧ b 14 ≤ b 13+c 20)
    : b 6=0 := by
  have hflow := (Nat.add_le_add _hd0.2 (Nat.add_le_add _hd2.2 (Nat.add_le_add _hd3.2 (Nat.add_le_add _hd5.2 (Nat.add_le_add _hd8.2 (Nat.add_le_add _hd10.1 (Nat.add_le_add _hd11.1 _hd13.1)))))))
  have hbound : 3*b 6 ≤ (c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+c 8+c 9+2*c 10+c 11+c 12+c 13+2*c 14+c 15+c 16+c 17+2*c 18+2*c 19+2*c 20) := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreVI_cut_relation_7_zero (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+c 8+c 9+2*c 10+c 11+c 12+c 13+2*c 14+c 15+c 16+c 17+2*c 18+2*c 19+2*c 20 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 13+c 2 ∧ b 13 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 14+c 3 ∧ b 14 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 4+c 5 ∧ b 4 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 5+c 6 ∧ b 5 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 5 ≤ b 8+c 9 ∧ b 8 ≤ b 5+c 9)
    (_hd10 : b 6 ≤ b 7+c 10 ∧ b 7 ≤ b 6+c 10)
    (_hd11 : b 6 ≤ b 13+c 11 ∧ b 13 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 9+c 12 ∧ b 9 ≤ b 7+c 12)
    (_hd13 : b 7 ≤ b 14+c 13 ∧ b 14 ≤ b 7+c 13)
    (_hd14 : b 8 ≤ b 9+c 14 ∧ b 9 ≤ b 8+c 14)
    (_hd15 : b 8 ≤ b 10+c 15 ∧ b 10 ≤ b 8+c 15)
    (_hd16 : b 9 ≤ b 11+c 16 ∧ b 11 ≤ b 9+c 16)
    (_hd17 : b 10 ≤ b 11+c 17 ∧ b 11 ≤ b 10+c 17)
    (_hd18 : b 10 ≤ b 12+c 18 ∧ b 12 ≤ b 10+c 18)
    (_hd19 : b 11 ≤ b 12+c 19 ∧ b 12 ≤ b 11+c 19)
    (_hd20 : b 13 ≤ b 14+c 20 ∧ b 14 ≤ b 13+c 20)
    : b 7=0 := by
  have hflow := (Nat.add_le_add _hd0.2 (Nat.add_le_add _hd2.2 (Nat.add_le_add _hd3.2 (Nat.add_le_add _hd5.2 (Nat.add_le_add _hd8.2 (Nat.add_le_add _hd10.2 (Nat.add_le_add _hd10.2 (Nat.add_le_add _hd11.1 _hd13.1))))))))
  have hbound : 3*b 7 ≤ (c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+c 8+c 9+2*c 10+c 11+c 12+c 13+2*c 14+c 15+c 16+c 17+2*c 18+2*c 19+2*c 20) := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreVI_cut_relation_9_8 (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+c 8+c 9+2*c 10+c 11+c 12+c 13+2*c 14+c 15+c 16+c 17+2*c 18+2*c 19+2*c 20 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 13+c 2 ∧ b 13 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 14+c 3 ∧ b 14 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 4+c 5 ∧ b 4 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 5+c 6 ∧ b 5 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 5 ≤ b 8+c 9 ∧ b 8 ≤ b 5+c 9)
    (_hd10 : b 6 ≤ b 7+c 10 ∧ b 7 ≤ b 6+c 10)
    (_hd11 : b 6 ≤ b 13+c 11 ∧ b 13 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 9+c 12 ∧ b 9 ≤ b 7+c 12)
    (_hd13 : b 7 ≤ b 14+c 13 ∧ b 14 ≤ b 7+c 13)
    (_hd14 : b 8 ≤ b 9+c 14 ∧ b 9 ≤ b 8+c 14)
    (_hd15 : b 8 ≤ b 10+c 15 ∧ b 10 ≤ b 8+c 15)
    (_hd16 : b 9 ≤ b 11+c 16 ∧ b 11 ≤ b 9+c 16)
    (_hd17 : b 10 ≤ b 11+c 17 ∧ b 11 ≤ b 10+c 17)
    (_hd18 : b 10 ≤ b 12+c 18 ∧ b 12 ≤ b 10+c 18)
    (_hd19 : b 11 ≤ b 12+c 19 ∧ b 12 ≤ b 11+c 19)
    (_hd20 : b 13 ≤ b 14+c 20 ∧ b 14 ≤ b 13+c 20)
    : b 9 ≤ b 8 := by
  have hflow := (Nat.add_le_add _hd3.2 (Nat.add_le_add _hd12.2 (Nat.add_le_add _hd13.1 (Nat.add_le_add _hd14.2 _hd14.2))))
  have hbound : 3*b 9 ≤ (c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+c 8+c 9+2*c 10+c 11+c 12+c 13+2*c 14+c 15+c 16+c 17+2*c 18+2*c 19+2*c 20)+3*b 8 := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreVI_cut_relation_8_9 (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+c 8+c 9+2*c 10+c 11+c 12+c 13+2*c 14+c 15+c 16+c 17+2*c 18+2*c 19+2*c 20 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 13+c 2 ∧ b 13 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 14+c 3 ∧ b 14 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 4+c 5 ∧ b 4 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 5+c 6 ∧ b 5 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 5 ≤ b 8+c 9 ∧ b 8 ≤ b 5+c 9)
    (_hd10 : b 6 ≤ b 7+c 10 ∧ b 7 ≤ b 6+c 10)
    (_hd11 : b 6 ≤ b 13+c 11 ∧ b 13 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 9+c 12 ∧ b 9 ≤ b 7+c 12)
    (_hd13 : b 7 ≤ b 14+c 13 ∧ b 14 ≤ b 7+c 13)
    (_hd14 : b 8 ≤ b 9+c 14 ∧ b 9 ≤ b 8+c 14)
    (_hd15 : b 8 ≤ b 10+c 15 ∧ b 10 ≤ b 8+c 15)
    (_hd16 : b 9 ≤ b 11+c 16 ∧ b 11 ≤ b 9+c 16)
    (_hd17 : b 10 ≤ b 11+c 17 ∧ b 11 ≤ b 10+c 17)
    (_hd18 : b 10 ≤ b 12+c 18 ∧ b 12 ≤ b 10+c 18)
    (_hd19 : b 11 ≤ b 12+c 19 ∧ b 12 ≤ b 11+c 19)
    (_hd20 : b 13 ≤ b 14+c 20 ∧ b 14 ≤ b 13+c 20)
    : b 8 ≤ b 9 := by
  have hflow := (Nat.add_le_add _hd1.2 (Nat.add_le_add _hd6.2 (Nat.add_le_add _hd9.2 (Nat.add_le_add _hd14.1 _hd14.1))))
  have hbound : 3*b 8 ≤ (c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+c 8+c 9+2*c 10+c 11+c 12+c 13+2*c 14+c 15+c 16+c 17+2*c 18+2*c 19+2*c 20)+3*b 9 := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreVI_cut_relation_11_10 (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+c 8+c 9+2*c 10+c 11+c 12+c 13+2*c 14+c 15+c 16+c 17+2*c 18+2*c 19+2*c 20 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 13+c 2 ∧ b 13 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 14+c 3 ∧ b 14 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 4+c 5 ∧ b 4 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 5+c 6 ∧ b 5 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 5 ≤ b 8+c 9 ∧ b 8 ≤ b 5+c 9)
    (_hd10 : b 6 ≤ b 7+c 10 ∧ b 7 ≤ b 6+c 10)
    (_hd11 : b 6 ≤ b 13+c 11 ∧ b 13 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 9+c 12 ∧ b 9 ≤ b 7+c 12)
    (_hd13 : b 7 ≤ b 14+c 13 ∧ b 14 ≤ b 7+c 13)
    (_hd14 : b 8 ≤ b 9+c 14 ∧ b 9 ≤ b 8+c 14)
    (_hd15 : b 8 ≤ b 10+c 15 ∧ b 10 ≤ b 8+c 15)
    (_hd16 : b 9 ≤ b 11+c 16 ∧ b 11 ≤ b 9+c 16)
    (_hd17 : b 10 ≤ b 11+c 17 ∧ b 11 ≤ b 10+c 17)
    (_hd18 : b 10 ≤ b 12+c 18 ∧ b 12 ≤ b 10+c 18)
    (_hd19 : b 11 ≤ b 12+c 19 ∧ b 12 ≤ b 11+c 19)
    (_hd20 : b 13 ≤ b 14+c 20 ∧ b 14 ≤ b 13+c 20)
    : b 11 ≤ b 10 := by
  have hflow := (Nat.add_le_add _hd17.2 (Nat.add_le_add _hd18.2 (Nat.add_le_add _hd18.2 (Nat.add_le_add _hd19.1 _hd19.1))))
  have hbound : 3*b 11 ≤ (c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+c 8+c 9+2*c 10+c 11+c 12+c 13+2*c 14+c 15+c 16+c 17+2*c 18+2*c 19+2*c 20)+3*b 10 := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreVI_cut_relation_10_11 (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+c 8+c 9+2*c 10+c 11+c 12+c 13+2*c 14+c 15+c 16+c 17+2*c 18+2*c 19+2*c 20 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 13+c 2 ∧ b 13 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 14+c 3 ∧ b 14 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 4+c 5 ∧ b 4 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 5+c 6 ∧ b 5 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 5 ≤ b 8+c 9 ∧ b 8 ≤ b 5+c 9)
    (_hd10 : b 6 ≤ b 7+c 10 ∧ b 7 ≤ b 6+c 10)
    (_hd11 : b 6 ≤ b 13+c 11 ∧ b 13 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 9+c 12 ∧ b 9 ≤ b 7+c 12)
    (_hd13 : b 7 ≤ b 14+c 13 ∧ b 14 ≤ b 7+c 13)
    (_hd14 : b 8 ≤ b 9+c 14 ∧ b 9 ≤ b 8+c 14)
    (_hd15 : b 8 ≤ b 10+c 15 ∧ b 10 ≤ b 8+c 15)
    (_hd16 : b 9 ≤ b 11+c 16 ∧ b 11 ≤ b 9+c 16)
    (_hd17 : b 10 ≤ b 11+c 17 ∧ b 11 ≤ b 10+c 17)
    (_hd18 : b 10 ≤ b 12+c 18 ∧ b 12 ≤ b 10+c 18)
    (_hd19 : b 11 ≤ b 12+c 19 ∧ b 12 ≤ b 11+c 19)
    (_hd20 : b 13 ≤ b 14+c 20 ∧ b 14 ≤ b 13+c 20)
    : b 10 ≤ b 11 := by
  have hflow := (Nat.add_le_add _hd17.1 (Nat.add_le_add _hd18.1 (Nat.add_le_add _hd18.1 (Nat.add_le_add _hd19.2 _hd19.2))))
  have hbound : 3*b 10 ≤ (c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+c 8+c 9+2*c 10+c 11+c 12+c 13+2*c 14+c 15+c 16+c 17+2*c 18+2*c 19+2*c 20)+3*b 11 := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreVI_cut_relation_12_10 (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+c 8+c 9+2*c 10+c 11+c 12+c 13+2*c 14+c 15+c 16+c 17+2*c 18+2*c 19+2*c 20 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 13+c 2 ∧ b 13 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 14+c 3 ∧ b 14 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 4+c 5 ∧ b 4 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 5+c 6 ∧ b 5 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 5 ≤ b 8+c 9 ∧ b 8 ≤ b 5+c 9)
    (_hd10 : b 6 ≤ b 7+c 10 ∧ b 7 ≤ b 6+c 10)
    (_hd11 : b 6 ≤ b 13+c 11 ∧ b 13 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 9+c 12 ∧ b 9 ≤ b 7+c 12)
    (_hd13 : b 7 ≤ b 14+c 13 ∧ b 14 ≤ b 7+c 13)
    (_hd14 : b 8 ≤ b 9+c 14 ∧ b 9 ≤ b 8+c 14)
    (_hd15 : b 8 ≤ b 10+c 15 ∧ b 10 ≤ b 8+c 15)
    (_hd16 : b 9 ≤ b 11+c 16 ∧ b 11 ≤ b 9+c 16)
    (_hd17 : b 10 ≤ b 11+c 17 ∧ b 11 ≤ b 10+c 17)
    (_hd18 : b 10 ≤ b 12+c 18 ∧ b 12 ≤ b 10+c 18)
    (_hd19 : b 11 ≤ b 12+c 19 ∧ b 12 ≤ b 11+c 19)
    (_hd20 : b 13 ≤ b 14+c 20 ∧ b 14 ≤ b 13+c 20)
    : b 12 ≤ b 10 := by
  have hflow := (Nat.add_le_add _hd17.2 (Nat.add_le_add _hd18.2 (Nat.add_le_add _hd18.2 _hd19.2)))
  have hbound : 3*b 12 ≤ (c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+c 8+c 9+2*c 10+c 11+c 12+c 13+2*c 14+c 15+c 16+c 17+2*c 18+2*c 19+2*c 20)+3*b 10 := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreVI_cut_relation_10_12 (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+c 8+c 9+2*c 10+c 11+c 12+c 13+2*c 14+c 15+c 16+c 17+2*c 18+2*c 19+2*c 20 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 13+c 2 ∧ b 13 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 14+c 3 ∧ b 14 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 4+c 5 ∧ b 4 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 5+c 6 ∧ b 5 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 5 ≤ b 8+c 9 ∧ b 8 ≤ b 5+c 9)
    (_hd10 : b 6 ≤ b 7+c 10 ∧ b 7 ≤ b 6+c 10)
    (_hd11 : b 6 ≤ b 13+c 11 ∧ b 13 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 9+c 12 ∧ b 9 ≤ b 7+c 12)
    (_hd13 : b 7 ≤ b 14+c 13 ∧ b 14 ≤ b 7+c 13)
    (_hd14 : b 8 ≤ b 9+c 14 ∧ b 9 ≤ b 8+c 14)
    (_hd15 : b 8 ≤ b 10+c 15 ∧ b 10 ≤ b 8+c 15)
    (_hd16 : b 9 ≤ b 11+c 16 ∧ b 11 ≤ b 9+c 16)
    (_hd17 : b 10 ≤ b 11+c 17 ∧ b 11 ≤ b 10+c 17)
    (_hd18 : b 10 ≤ b 12+c 18 ∧ b 12 ≤ b 10+c 18)
    (_hd19 : b 11 ≤ b 12+c 19 ∧ b 12 ≤ b 11+c 19)
    (_hd20 : b 13 ≤ b 14+c 20 ∧ b 14 ≤ b 13+c 20)
    : b 10 ≤ b 12 := by
  have hflow := (Nat.add_le_add _hd17.1 (Nat.add_le_add _hd18.1 (Nat.add_le_add _hd18.1 _hd19.1)))
  have hbound : 3*b 10 ≤ (c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+c 8+c 9+2*c 10+c 11+c 12+c 13+2*c 14+c 15+c 16+c 17+2*c 18+2*c 19+2*c 20)+3*b 12 := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreVI_cut_relation_13_zero (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+c 8+c 9+2*c 10+c 11+c 12+c 13+2*c 14+c 15+c 16+c 17+2*c 18+2*c 19+2*c 20 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 13+c 2 ∧ b 13 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 14+c 3 ∧ b 14 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 4+c 5 ∧ b 4 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 5+c 6 ∧ b 5 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 5 ≤ b 8+c 9 ∧ b 8 ≤ b 5+c 9)
    (_hd10 : b 6 ≤ b 7+c 10 ∧ b 7 ≤ b 6+c 10)
    (_hd11 : b 6 ≤ b 13+c 11 ∧ b 13 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 9+c 12 ∧ b 9 ≤ b 7+c 12)
    (_hd13 : b 7 ≤ b 14+c 13 ∧ b 14 ≤ b 7+c 13)
    (_hd14 : b 8 ≤ b 9+c 14 ∧ b 9 ≤ b 8+c 14)
    (_hd15 : b 8 ≤ b 10+c 15 ∧ b 10 ≤ b 8+c 15)
    (_hd16 : b 9 ≤ b 11+c 16 ∧ b 11 ≤ b 9+c 16)
    (_hd17 : b 10 ≤ b 11+c 17 ∧ b 11 ≤ b 10+c 17)
    (_hd18 : b 10 ≤ b 12+c 18 ∧ b 12 ≤ b 10+c 18)
    (_hd19 : b 11 ≤ b 12+c 19 ∧ b 12 ≤ b 11+c 19)
    (_hd20 : b 13 ≤ b 14+c 20 ∧ b 14 ≤ b 13+c 20)
    : b 13=0 := by
  have hflow := (Nat.add_le_add _hd0.2 (Nat.add_le_add _hd2.2 (Nat.add_le_add _hd3.2 (Nat.add_le_add _hd5.2 (Nat.add_le_add _hd8.2 (Nat.add_le_add _hd11.2 _hd20.1))))))
  have hbound : 3*b 13 ≤ (c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+c 8+c 9+2*c 10+c 11+c 12+c 13+2*c 14+c 15+c 16+c 17+2*c 18+2*c 19+2*c 20) := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreVI_cut_relation_14_zero (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+c 8+c 9+2*c 10+c 11+c 12+c 13+2*c 14+c 15+c 16+c 17+2*c 18+2*c 19+2*c 20 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 13+c 2 ∧ b 13 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 14+c 3 ∧ b 14 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 4+c 5 ∧ b 4 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 5+c 6 ∧ b 5 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 5 ≤ b 8+c 9 ∧ b 8 ≤ b 5+c 9)
    (_hd10 : b 6 ≤ b 7+c 10 ∧ b 7 ≤ b 6+c 10)
    (_hd11 : b 6 ≤ b 13+c 11 ∧ b 13 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 9+c 12 ∧ b 9 ≤ b 7+c 12)
    (_hd13 : b 7 ≤ b 14+c 13 ∧ b 14 ≤ b 7+c 13)
    (_hd14 : b 8 ≤ b 9+c 14 ∧ b 9 ≤ b 8+c 14)
    (_hd15 : b 8 ≤ b 10+c 15 ∧ b 10 ≤ b 8+c 15)
    (_hd16 : b 9 ≤ b 11+c 16 ∧ b 11 ≤ b 9+c 16)
    (_hd17 : b 10 ≤ b 11+c 17 ∧ b 11 ≤ b 10+c 17)
    (_hd18 : b 10 ≤ b 12+c 18 ∧ b 12 ≤ b 10+c 18)
    (_hd19 : b 11 ≤ b 12+c 19 ∧ b 12 ≤ b 11+c 19)
    (_hd20 : b 13 ≤ b 14+c 20 ∧ b 14 ≤ b 13+c 20)
    : b 14=0 := by
  have hflow := (Nat.add_le_add _hd0.2 (Nat.add_le_add _hd2.2 (Nat.add_le_add _hd3.2 (Nat.add_le_add _hd5.2 (Nat.add_le_add _hd8.2 (Nat.add_le_add _hd10.2 (Nat.add_le_add _hd13.2 _hd20.2)))))))
  have hbound : 3*b 14 ≤ (c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+c 8+c 9+2*c 10+c 11+c 12+c 13+2*c 14+c 15+c 16+c 17+2*c 18+2*c 19+2*c 20) := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreVI_cut_relation_8_10 (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+c 8+c 9+2*c 10+c 11+c 12+c 13+2*c 14+c 15+c 16+c 17+2*c 18+2*c 19+2*c 20 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 13+c 2 ∧ b 13 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 14+c 3 ∧ b 14 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 4+c 5 ∧ b 4 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 5+c 6 ∧ b 5 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 5 ≤ b 8+c 9 ∧ b 8 ≤ b 5+c 9)
    (_hd10 : b 6 ≤ b 7+c 10 ∧ b 7 ≤ b 6+c 10)
    (_hd11 : b 6 ≤ b 13+c 11 ∧ b 13 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 9+c 12 ∧ b 9 ≤ b 7+c 12)
    (_hd13 : b 7 ≤ b 14+c 13 ∧ b 14 ≤ b 7+c 13)
    (_hd14 : b 8 ≤ b 9+c 14 ∧ b 9 ≤ b 8+c 14)
    (_hd15 : b 8 ≤ b 10+c 15 ∧ b 10 ≤ b 8+c 15)
    (_hd16 : b 9 ≤ b 11+c 16 ∧ b 11 ≤ b 9+c 16)
    (_hd17 : b 10 ≤ b 11+c 17 ∧ b 11 ≤ b 10+c 17)
    (_hd18 : b 10 ≤ b 12+c 18 ∧ b 12 ≤ b 10+c 18)
    (_hd19 : b 11 ≤ b 12+c 19 ∧ b 12 ≤ b 11+c 19)
    (_hd20 : b 13 ≤ b 14+c 20 ∧ b 14 ≤ b 13+c 20)
    : b 8 ≤ b 10 := by
  have hflow := (Nat.add_le_add _hd1.2 (Nat.add_le_add _hd6.2 (Nat.add_le_add _hd9.2 (Nat.add_le_add _hd14.1 (Nat.add_le_add _hd15.1 (Nat.add_le_add _hd16.1 _hd17.2))))))
  have hbound : 3*b 8 ≤ (c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+c 8+c 9+2*c 10+c 11+c 12+c 13+2*c 14+c 15+c 16+c 17+2*c 18+2*c 19+2*c 20)+3*b 10 := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20 hflow
  omega

/-- The literal type-VI core has only these two-edge cut masks away from its joints. -/
theorem coreVI_cut_masks (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hb : ∀ i < 15,b i ≤ 1) (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+2*c 7+c 8+c 9+2*c 10+c 11+c 12+c 13+2*c 14+c 15+c 16+c 17+2*c 18+2*c 19+2*c 20 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 13+c 2 ∧ b 13 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 14+c 3 ∧ b 14 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 4+c 5 ∧ b 4 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 5+c 6 ∧ b 5 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 5 ≤ b 8+c 9 ∧ b 8 ≤ b 5+c 9)
    (_hd10 : b 6 ≤ b 7+c 10 ∧ b 7 ≤ b 6+c 10)
    (_hd11 : b 6 ≤ b 13+c 11 ∧ b 13 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 9+c 12 ∧ b 9 ≤ b 7+c 12)
    (_hd13 : b 7 ≤ b 14+c 13 ∧ b 14 ≤ b 7+c 13)
    (_hd14 : b 8 ≤ b 9+c 14 ∧ b 9 ≤ b 8+c 14)
    (_hd15 : b 8 ≤ b 10+c 15 ∧ b 10 ≤ b 8+c 15)
    (_hd16 : b 9 ≤ b 11+c 16 ∧ b 11 ≤ b 9+c 16)
    (_hd17 : b 10 ≤ b 11+c 17 ∧ b 11 ≤ b 10+c 17)
    (_hd18 : b 10 ≤ b 12+c 18 ∧ b 12 ≤ b 10+c 18)
    (_hd19 : b 11 ≤ b 12+c 19 ∧ b 12 ≤ b 11+c 19)
    (_hd20 : b 13 ≤ b 14+c 20 ∧ b 14 ≤ b 13+c 20)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9,b 10,b 11,b 12,b 13,b 14] ∈ ([[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,1,1,1,0,0],[0,0,0,0,0,0,0,0,1,1,1,1,1,0,0]] : List (List ℕ)) := by
  have hrel2_zero := coreVI_cut_relation_2_zero b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20
  have hrel3_zero := coreVI_cut_relation_3_zero b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20
  have hrel4_zero := coreVI_cut_relation_4_zero b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20
  have hrel5_zero := coreVI_cut_relation_5_zero b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20
  have hrel6_zero := coreVI_cut_relation_6_zero b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20
  have hrel7_zero := coreVI_cut_relation_7_zero b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20
  have hrel9_8 := coreVI_cut_relation_9_8 b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20
  have hrel8_9 := coreVI_cut_relation_8_9 b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20
  have hrel11_10 := coreVI_cut_relation_11_10 b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20
  have hrel10_11 := coreVI_cut_relation_10_11 b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20
  have hrel12_10 := coreVI_cut_relation_12_10 b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20
  have hrel10_12 := coreVI_cut_relation_10_12 b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20
  have hrel13_zero := coreVI_cut_relation_13_zero b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20
  have hrel14_zero := coreVI_cut_relation_14_zero b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20
  have hrel8_10 := coreVI_cut_relation_8_10 b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20
  have hb8 := _hb 8 (by decide)
  have hb10 := _hb 10 (by decide)
  clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14 _hd15 _hd16 _hd17 _hd18 _hd19 _hd20 c _hb
  simp only [List.mem_cons,List.not_mem_nil,or_false,List.cons.injEq,and_true]
  omega

end WaveTurbulence.Vine
