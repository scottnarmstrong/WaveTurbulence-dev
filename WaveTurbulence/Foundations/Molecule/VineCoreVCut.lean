/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-! # Core masks with cut at most two, type V

The outer joints are absent. Explicit integer flows add directed edge
inequalities before the final arithmetic step. No bounded search replaces
a proof: every flow sum is checked by the Lean kernel. -/

public section
namespace WaveTurbulence.Vine

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreV_cut_relation_3_2 (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+2*c 3+c 4+c 5+2*c 6+c 7+c 8+c 9+2*c 10+2*c 11 ≤ 2)
    (_hd0 : b 0 ≤ b 1+c 0 ∧ b 1 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 2+c 1 ∧ b 2 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 3+c 2 ∧ b 3 ≤ b 1+c 2)
    (_hd3 : b 2 ≤ b 3+c 3 ∧ b 3 ≤ b 2+c 3)
    (_hd4 : b 2 ≤ b 4+c 4 ∧ b 4 ≤ b 2+c 4)
    (_hd5 : b 3 ≤ b 5+c 5 ∧ b 5 ≤ b 3+c 5)
    (_hd6 : b 4 ≤ b 5+c 6 ∧ b 5 ≤ b 4+c 6)
    (_hd7 : b 4 ≤ b 6+c 7 ∧ b 6 ≤ b 4+c 7)
    (_hd8 : b 5 ≤ b 7+c 8 ∧ b 7 ≤ b 5+c 8)
    (_hd9 : b 6 ≤ b 7+c 9 ∧ b 7 ≤ b 6+c 9)
    (_hd10 : b 6 ≤ b 8+c 10 ∧ b 8 ≤ b 6+c 10)
    (_hd11 : b 7 ≤ b 8+c 11 ∧ b 8 ≤ b 7+c 11)
    : b 3 ≤ b 2 := by
  have hflow := (Nat.add_le_add _hd2.2 (Nat.add_le_add _hd3.2 _hd3.2))
  have hbound : 3*b 3 ≤ (c 0+c 1+c 2+2*c 3+c 4+c 5+2*c 6+c 7+c 8+c 9+2*c 10+2*c 11)+3*b 2 := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreV_cut_relation_2_3 (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+2*c 3+c 4+c 5+2*c 6+c 7+c 8+c 9+2*c 10+2*c 11 ≤ 2)
    (_hd0 : b 0 ≤ b 1+c 0 ∧ b 1 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 2+c 1 ∧ b 2 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 3+c 2 ∧ b 3 ≤ b 1+c 2)
    (_hd3 : b 2 ≤ b 3+c 3 ∧ b 3 ≤ b 2+c 3)
    (_hd4 : b 2 ≤ b 4+c 4 ∧ b 4 ≤ b 2+c 4)
    (_hd5 : b 3 ≤ b 5+c 5 ∧ b 5 ≤ b 3+c 5)
    (_hd6 : b 4 ≤ b 5+c 6 ∧ b 5 ≤ b 4+c 6)
    (_hd7 : b 4 ≤ b 6+c 7 ∧ b 6 ≤ b 4+c 7)
    (_hd8 : b 5 ≤ b 7+c 8 ∧ b 7 ≤ b 5+c 8)
    (_hd9 : b 6 ≤ b 7+c 9 ∧ b 7 ≤ b 6+c 9)
    (_hd10 : b 6 ≤ b 8+c 10 ∧ b 8 ≤ b 6+c 10)
    (_hd11 : b 7 ≤ b 8+c 11 ∧ b 8 ≤ b 7+c 11)
    : b 2 ≤ b 3 := by
  have hflow := (Nat.add_le_add _hd1.2 (Nat.add_le_add _hd3.1 _hd3.1))
  have hbound : 3*b 2 ≤ (c 0+c 1+c 2+2*c 3+c 4+c 5+2*c 6+c 7+c 8+c 9+2*c 10+2*c 11)+3*b 3 := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreV_cut_relation_5_4 (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+2*c 3+c 4+c 5+2*c 6+c 7+c 8+c 9+2*c 10+2*c 11 ≤ 2)
    (_hd0 : b 0 ≤ b 1+c 0 ∧ b 1 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 2+c 1 ∧ b 2 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 3+c 2 ∧ b 3 ≤ b 1+c 2)
    (_hd3 : b 2 ≤ b 3+c 3 ∧ b 3 ≤ b 2+c 3)
    (_hd4 : b 2 ≤ b 4+c 4 ∧ b 4 ≤ b 2+c 4)
    (_hd5 : b 3 ≤ b 5+c 5 ∧ b 5 ≤ b 3+c 5)
    (_hd6 : b 4 ≤ b 5+c 6 ∧ b 5 ≤ b 4+c 6)
    (_hd7 : b 4 ≤ b 6+c 7 ∧ b 6 ≤ b 4+c 7)
    (_hd8 : b 5 ≤ b 7+c 8 ∧ b 7 ≤ b 5+c 8)
    (_hd9 : b 6 ≤ b 7+c 9 ∧ b 7 ≤ b 6+c 9)
    (_hd10 : b 6 ≤ b 8+c 10 ∧ b 8 ≤ b 6+c 10)
    (_hd11 : b 7 ≤ b 8+c 11 ∧ b 8 ≤ b 7+c 11)
    : b 5 ≤ b 4 := by
  have hflow := (Nat.add_le_add _hd2.2 (Nat.add_le_add _hd5.2 (Nat.add_le_add _hd6.2 _hd6.2)))
  have hbound : 3*b 5 ≤ (c 0+c 1+c 2+2*c 3+c 4+c 5+2*c 6+c 7+c 8+c 9+2*c 10+2*c 11)+3*b 4 := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreV_cut_relation_4_5 (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+2*c 3+c 4+c 5+2*c 6+c 7+c 8+c 9+2*c 10+2*c 11 ≤ 2)
    (_hd0 : b 0 ≤ b 1+c 0 ∧ b 1 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 2+c 1 ∧ b 2 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 3+c 2 ∧ b 3 ≤ b 1+c 2)
    (_hd3 : b 2 ≤ b 3+c 3 ∧ b 3 ≤ b 2+c 3)
    (_hd4 : b 2 ≤ b 4+c 4 ∧ b 4 ≤ b 2+c 4)
    (_hd5 : b 3 ≤ b 5+c 5 ∧ b 5 ≤ b 3+c 5)
    (_hd6 : b 4 ≤ b 5+c 6 ∧ b 5 ≤ b 4+c 6)
    (_hd7 : b 4 ≤ b 6+c 7 ∧ b 6 ≤ b 4+c 7)
    (_hd8 : b 5 ≤ b 7+c 8 ∧ b 7 ≤ b 5+c 8)
    (_hd9 : b 6 ≤ b 7+c 9 ∧ b 7 ≤ b 6+c 9)
    (_hd10 : b 6 ≤ b 8+c 10 ∧ b 8 ≤ b 6+c 10)
    (_hd11 : b 7 ≤ b 8+c 11 ∧ b 8 ≤ b 7+c 11)
    : b 4 ≤ b 5 := by
  have hflow := (Nat.add_le_add _hd1.2 (Nat.add_le_add _hd4.2 (Nat.add_le_add _hd6.1 _hd6.1)))
  have hbound : 3*b 4 ≤ (c 0+c 1+c 2+2*c 3+c 4+c 5+2*c 6+c 7+c 8+c 9+2*c 10+2*c 11)+3*b 5 := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreV_cut_relation_7_6 (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+2*c 3+c 4+c 5+2*c 6+c 7+c 8+c 9+2*c 10+2*c 11 ≤ 2)
    (_hd0 : b 0 ≤ b 1+c 0 ∧ b 1 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 2+c 1 ∧ b 2 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 3+c 2 ∧ b 3 ≤ b 1+c 2)
    (_hd3 : b 2 ≤ b 3+c 3 ∧ b 3 ≤ b 2+c 3)
    (_hd4 : b 2 ≤ b 4+c 4 ∧ b 4 ≤ b 2+c 4)
    (_hd5 : b 3 ≤ b 5+c 5 ∧ b 5 ≤ b 3+c 5)
    (_hd6 : b 4 ≤ b 5+c 6 ∧ b 5 ≤ b 4+c 6)
    (_hd7 : b 4 ≤ b 6+c 7 ∧ b 6 ≤ b 4+c 7)
    (_hd8 : b 5 ≤ b 7+c 8 ∧ b 7 ≤ b 5+c 8)
    (_hd9 : b 6 ≤ b 7+c 9 ∧ b 7 ≤ b 6+c 9)
    (_hd10 : b 6 ≤ b 8+c 10 ∧ b 8 ≤ b 6+c 10)
    (_hd11 : b 7 ≤ b 8+c 11 ∧ b 8 ≤ b 7+c 11)
    : b 7 ≤ b 6 := by
  have hflow := (Nat.add_le_add _hd9.2 (Nat.add_le_add _hd10.2 (Nat.add_le_add _hd10.2 (Nat.add_le_add _hd11.1 _hd11.1))))
  have hbound : 3*b 7 ≤ (c 0+c 1+c 2+2*c 3+c 4+c 5+2*c 6+c 7+c 8+c 9+2*c 10+2*c 11)+3*b 6 := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreV_cut_relation_6_7 (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+2*c 3+c 4+c 5+2*c 6+c 7+c 8+c 9+2*c 10+2*c 11 ≤ 2)
    (_hd0 : b 0 ≤ b 1+c 0 ∧ b 1 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 2+c 1 ∧ b 2 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 3+c 2 ∧ b 3 ≤ b 1+c 2)
    (_hd3 : b 2 ≤ b 3+c 3 ∧ b 3 ≤ b 2+c 3)
    (_hd4 : b 2 ≤ b 4+c 4 ∧ b 4 ≤ b 2+c 4)
    (_hd5 : b 3 ≤ b 5+c 5 ∧ b 5 ≤ b 3+c 5)
    (_hd6 : b 4 ≤ b 5+c 6 ∧ b 5 ≤ b 4+c 6)
    (_hd7 : b 4 ≤ b 6+c 7 ∧ b 6 ≤ b 4+c 7)
    (_hd8 : b 5 ≤ b 7+c 8 ∧ b 7 ≤ b 5+c 8)
    (_hd9 : b 6 ≤ b 7+c 9 ∧ b 7 ≤ b 6+c 9)
    (_hd10 : b 6 ≤ b 8+c 10 ∧ b 8 ≤ b 6+c 10)
    (_hd11 : b 7 ≤ b 8+c 11 ∧ b 8 ≤ b 7+c 11)
    : b 6 ≤ b 7 := by
  have hflow := (Nat.add_le_add _hd9.1 (Nat.add_le_add _hd10.1 (Nat.add_le_add _hd10.1 (Nat.add_le_add _hd11.2 _hd11.2))))
  have hbound : 3*b 6 ≤ (c 0+c 1+c 2+2*c 3+c 4+c 5+2*c 6+c 7+c 8+c 9+2*c 10+2*c 11)+3*b 7 := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreV_cut_relation_8_6 (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+2*c 3+c 4+c 5+2*c 6+c 7+c 8+c 9+2*c 10+2*c 11 ≤ 2)
    (_hd0 : b 0 ≤ b 1+c 0 ∧ b 1 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 2+c 1 ∧ b 2 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 3+c 2 ∧ b 3 ≤ b 1+c 2)
    (_hd3 : b 2 ≤ b 3+c 3 ∧ b 3 ≤ b 2+c 3)
    (_hd4 : b 2 ≤ b 4+c 4 ∧ b 4 ≤ b 2+c 4)
    (_hd5 : b 3 ≤ b 5+c 5 ∧ b 5 ≤ b 3+c 5)
    (_hd6 : b 4 ≤ b 5+c 6 ∧ b 5 ≤ b 4+c 6)
    (_hd7 : b 4 ≤ b 6+c 7 ∧ b 6 ≤ b 4+c 7)
    (_hd8 : b 5 ≤ b 7+c 8 ∧ b 7 ≤ b 5+c 8)
    (_hd9 : b 6 ≤ b 7+c 9 ∧ b 7 ≤ b 6+c 9)
    (_hd10 : b 6 ≤ b 8+c 10 ∧ b 8 ≤ b 6+c 10)
    (_hd11 : b 7 ≤ b 8+c 11 ∧ b 8 ≤ b 7+c 11)
    : b 8 ≤ b 6 := by
  have hflow := (Nat.add_le_add _hd9.2 (Nat.add_le_add _hd10.2 (Nat.add_le_add _hd10.2 _hd11.2)))
  have hbound : 3*b 8 ≤ (c 0+c 1+c 2+2*c 3+c 4+c 5+2*c 6+c 7+c 8+c 9+2*c 10+2*c 11)+3*b 6 := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreV_cut_relation_6_8 (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+2*c 3+c 4+c 5+2*c 6+c 7+c 8+c 9+2*c 10+2*c 11 ≤ 2)
    (_hd0 : b 0 ≤ b 1+c 0 ∧ b 1 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 2+c 1 ∧ b 2 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 3+c 2 ∧ b 3 ≤ b 1+c 2)
    (_hd3 : b 2 ≤ b 3+c 3 ∧ b 3 ≤ b 2+c 3)
    (_hd4 : b 2 ≤ b 4+c 4 ∧ b 4 ≤ b 2+c 4)
    (_hd5 : b 3 ≤ b 5+c 5 ∧ b 5 ≤ b 3+c 5)
    (_hd6 : b 4 ≤ b 5+c 6 ∧ b 5 ≤ b 4+c 6)
    (_hd7 : b 4 ≤ b 6+c 7 ∧ b 6 ≤ b 4+c 7)
    (_hd8 : b 5 ≤ b 7+c 8 ∧ b 7 ≤ b 5+c 8)
    (_hd9 : b 6 ≤ b 7+c 9 ∧ b 7 ≤ b 6+c 9)
    (_hd10 : b 6 ≤ b 8+c 10 ∧ b 8 ≤ b 6+c 10)
    (_hd11 : b 7 ≤ b 8+c 11 ∧ b 8 ≤ b 7+c 11)
    : b 6 ≤ b 8 := by
  have hflow := (Nat.add_le_add _hd9.1 (Nat.add_le_add _hd10.1 (Nat.add_le_add _hd10.1 _hd11.1)))
  have hbound : 3*b 6 ≤ (c 0+c 1+c 2+2*c 3+c 4+c 5+2*c 6+c 7+c 8+c 9+2*c 10+2*c 11)+3*b 8 := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreV_cut_relation_2_4 (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+2*c 3+c 4+c 5+2*c 6+c 7+c 8+c 9+2*c 10+2*c 11 ≤ 2)
    (_hd0 : b 0 ≤ b 1+c 0 ∧ b 1 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 2+c 1 ∧ b 2 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 3+c 2 ∧ b 3 ≤ b 1+c 2)
    (_hd3 : b 2 ≤ b 3+c 3 ∧ b 3 ≤ b 2+c 3)
    (_hd4 : b 2 ≤ b 4+c 4 ∧ b 4 ≤ b 2+c 4)
    (_hd5 : b 3 ≤ b 5+c 5 ∧ b 5 ≤ b 3+c 5)
    (_hd6 : b 4 ≤ b 5+c 6 ∧ b 5 ≤ b 4+c 6)
    (_hd7 : b 4 ≤ b 6+c 7 ∧ b 6 ≤ b 4+c 7)
    (_hd8 : b 5 ≤ b 7+c 8 ∧ b 7 ≤ b 5+c 8)
    (_hd9 : b 6 ≤ b 7+c 9 ∧ b 7 ≤ b 6+c 9)
    (_hd10 : b 6 ≤ b 8+c 10 ∧ b 8 ≤ b 6+c 10)
    (_hd11 : b 7 ≤ b 8+c 11 ∧ b 8 ≤ b 7+c 11)
    : b 2 ≤ b 4 := by
  have hflow := (Nat.add_le_add _hd1.2 (Nat.add_le_add _hd2.2 (Nat.add_le_add _hd3.1 _hd4.1)))
  have hbound : 3*b 2 ≤ (c 0+c 1+c 2+2*c 3+c 4+c 5+2*c 6+c 7+c 8+c 9+2*c 10+2*c 11)+3*b 4 := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreV_cut_relation_2_6 (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+2*c 3+c 4+c 5+2*c 6+c 7+c 8+c 9+2*c 10+2*c 11 ≤ 2)
    (_hd0 : b 0 ≤ b 1+c 0 ∧ b 1 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 2+c 1 ∧ b 2 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 3+c 2 ∧ b 3 ≤ b 1+c 2)
    (_hd3 : b 2 ≤ b 3+c 3 ∧ b 3 ≤ b 2+c 3)
    (_hd4 : b 2 ≤ b 4+c 4 ∧ b 4 ≤ b 2+c 4)
    (_hd5 : b 3 ≤ b 5+c 5 ∧ b 5 ≤ b 3+c 5)
    (_hd6 : b 4 ≤ b 5+c 6 ∧ b 5 ≤ b 4+c 6)
    (_hd7 : b 4 ≤ b 6+c 7 ∧ b 6 ≤ b 4+c 7)
    (_hd8 : b 5 ≤ b 7+c 8 ∧ b 7 ≤ b 5+c 8)
    (_hd9 : b 6 ≤ b 7+c 9 ∧ b 7 ≤ b 6+c 9)
    (_hd10 : b 6 ≤ b 8+c 10 ∧ b 8 ≤ b 6+c 10)
    (_hd11 : b 7 ≤ b 8+c 11 ∧ b 8 ≤ b 7+c 11)
    : b 2 ≤ b 6 := by
  have hflow := (Nat.add_le_add _hd1.2 (Nat.add_le_add _hd2.2 (Nat.add_le_add _hd3.1 (Nat.add_le_add _hd4.1 _hd7.1))))
  have hbound : 3*b 2 ≤ (c 0+c 1+c 2+2*c 3+c 4+c 5+2*c 6+c 7+c 8+c 9+2*c 10+2*c 11)+3*b 6 := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreV_cut_relation_4_6 (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+2*c 3+c 4+c 5+2*c 6+c 7+c 8+c 9+2*c 10+2*c 11 ≤ 2)
    (_hd0 : b 0 ≤ b 1+c 0 ∧ b 1 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 2+c 1 ∧ b 2 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 3+c 2 ∧ b 3 ≤ b 1+c 2)
    (_hd3 : b 2 ≤ b 3+c 3 ∧ b 3 ≤ b 2+c 3)
    (_hd4 : b 2 ≤ b 4+c 4 ∧ b 4 ≤ b 2+c 4)
    (_hd5 : b 3 ≤ b 5+c 5 ∧ b 5 ≤ b 3+c 5)
    (_hd6 : b 4 ≤ b 5+c 6 ∧ b 5 ≤ b 4+c 6)
    (_hd7 : b 4 ≤ b 6+c 7 ∧ b 6 ≤ b 4+c 7)
    (_hd8 : b 5 ≤ b 7+c 8 ∧ b 7 ≤ b 5+c 8)
    (_hd9 : b 6 ≤ b 7+c 9 ∧ b 7 ≤ b 6+c 9)
    (_hd10 : b 6 ≤ b 8+c 10 ∧ b 8 ≤ b 6+c 10)
    (_hd11 : b 7 ≤ b 8+c 11 ∧ b 8 ≤ b 7+c 11)
    : b 4 ≤ b 6 := by
  have hflow := (Nat.add_le_add _hd1.2 (Nat.add_le_add _hd2.2 (Nat.add_le_add _hd4.2 (Nat.add_le_add _hd5.2 (Nat.add_le_add _hd6.1 _hd7.1)))))
  have hbound : 3*b 4 ≤ (c 0+c 1+c 2+2*c 3+c 4+c 5+2*c 6+c 7+c 8+c 9+2*c 10+2*c 11)+3*b 6 := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 hflow
  omega

/-- The literal type-V core has only these two-edge cut masks away from its joints. -/
theorem coreV_cut_masks (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hb : ∀ i < 9,b i ≤ 1) (_hcut : c 0+c 1+c 2+2*c 3+c 4+c 5+2*c 6+c 7+c 8+c 9+2*c 10+2*c 11 ≤ 2)
    (_hd0 : b 0 ≤ b 1+c 0 ∧ b 1 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 2+c 1 ∧ b 2 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 3+c 2 ∧ b 3 ≤ b 1+c 2)
    (_hd3 : b 2 ≤ b 3+c 3 ∧ b 3 ≤ b 2+c 3)
    (_hd4 : b 2 ≤ b 4+c 4 ∧ b 4 ≤ b 2+c 4)
    (_hd5 : b 3 ≤ b 5+c 5 ∧ b 5 ≤ b 3+c 5)
    (_hd6 : b 4 ≤ b 5+c 6 ∧ b 5 ≤ b 4+c 6)
    (_hd7 : b 4 ≤ b 6+c 7 ∧ b 6 ≤ b 4+c 7)
    (_hd8 : b 5 ≤ b 7+c 8 ∧ b 7 ≤ b 5+c 8)
    (_hd9 : b 6 ≤ b 7+c 9 ∧ b 7 ≤ b 6+c 9)
    (_hd10 : b 6 ≤ b 8+c 10 ∧ b 8 ≤ b 6+c 10)
    (_hd11 : b 7 ≤ b 8+c 11 ∧ b 8 ≤ b 7+c 11)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8] ∈ ([[0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,1,1,1],[0,0,0,0,1,1,1,1,1],[0,0,1,1,1,1,1,1,1]] : List (List ℕ)) := by
  have hrel3_2 := coreV_cut_relation_3_2 b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11
  have hrel2_3 := coreV_cut_relation_2_3 b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11
  have hrel5_4 := coreV_cut_relation_5_4 b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11
  have hrel4_5 := coreV_cut_relation_4_5 b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11
  have hrel7_6 := coreV_cut_relation_7_6 b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11
  have hrel6_7 := coreV_cut_relation_6_7 b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11
  have hrel8_6 := coreV_cut_relation_8_6 b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11
  have hrel6_8 := coreV_cut_relation_6_8 b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11
  have hrel2_4 := coreV_cut_relation_2_4 b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11
  have hrel2_6 := coreV_cut_relation_2_6 b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11
  have hrel4_6 := coreV_cut_relation_4_6 b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11
  have hb2 := _hb 2 (by decide)
  have hb4 := _hb 4 (by decide)
  have hb6 := _hb 6 (by decide)
  clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 c _hb
  simp only [List.mem_cons,List.not_mem_nil,or_false,List.cons.injEq,and_true]
  omega

end WaveTurbulence.Vine
