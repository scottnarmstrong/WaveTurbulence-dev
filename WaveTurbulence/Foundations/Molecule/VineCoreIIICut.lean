/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-! # Core masks with cut at most two, type III

The outer joints are absent. Explicit integer flows add directed edge
inequalities before the final arithmetic step. No bounded search replaces
a proof: every flow sum is checked by the Lean kernel. -/

public section
namespace WaveTurbulence.Vine

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreIII_cut_relation_2_zero (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+c 7+c 8+c 9+2*c 10+c 11+2*c 12 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 7+c 2 ∧ b 7 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 8+c 3 ∧ b 8 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 4+c 5 ∧ b 4 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 5+c 6 ∧ b 5 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 4 ≤ b 7+c 9 ∧ b 7 ≤ b 4+c 9)
    (_hd10 : b 5 ≤ b 6+c 10 ∧ b 6 ≤ b 5+c 10)
    (_hd11 : b 6 ≤ b 8+c 11 ∧ b 8 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 8+c 12 ∧ b 8 ≤ b 7+c 12)
    : b 2=0 := by
  have hflow := (Nat.add_le_add _hd0.2 (Nat.add_le_add _hd1.2 (Nat.add_le_add _hd2.2 (Nat.add_le_add _hd4.1 (Nat.add_le_add _hd5.1 _hd9.1)))))
  have hbound : 3*b 2 ≤ (c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+c 7+c 8+c 9+2*c 10+c 11+2*c 12) := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreIII_cut_relation_3_zero (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+c 7+c 8+c 9+2*c 10+c 11+2*c 12 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 7+c 2 ∧ b 7 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 8+c 3 ∧ b 8 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 4+c 5 ∧ b 4 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 5+c 6 ∧ b 5 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 4 ≤ b 7+c 9 ∧ b 7 ≤ b 4+c 9)
    (_hd10 : b 5 ≤ b 6+c 10 ∧ b 6 ≤ b 5+c 10)
    (_hd11 : b 6 ≤ b 8+c 11 ∧ b 8 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 8+c 12 ∧ b 8 ≤ b 7+c 12)
    : b 3=0 := by
  have hflow := (Nat.add_le_add _hd0.2 (Nat.add_le_add _hd1.2 (Nat.add_le_add _hd2.2 (Nat.add_le_add _hd4.2 (Nat.add_le_add _hd4.2 (Nat.add_le_add _hd5.1 _hd9.1))))))
  have hbound : 3*b 3 ≤ (c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+c 7+c 8+c 9+2*c 10+c 11+2*c 12) := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreIII_cut_relation_4_zero (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+c 7+c 8+c 9+2*c 10+c 11+2*c 12 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 7+c 2 ∧ b 7 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 8+c 3 ∧ b 8 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 4+c 5 ∧ b 4 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 5+c 6 ∧ b 5 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 4 ≤ b 7+c 9 ∧ b 7 ≤ b 4+c 9)
    (_hd10 : b 5 ≤ b 6+c 10 ∧ b 6 ≤ b 5+c 10)
    (_hd11 : b 6 ≤ b 8+c 11 ∧ b 8 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 8+c 12 ∧ b 8 ≤ b 7+c 12)
    : b 4=0 := by
  have hflow := (Nat.add_le_add _hd0.2 (Nat.add_le_add _hd1.2 (Nat.add_le_add _hd2.2 (Nat.add_le_add _hd5.2 (Nat.add_le_add _hd6.2 (Nat.add_le_add _hd7.1 _hd9.1))))))
  have hbound : 3*b 4 ≤ (c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+c 7+c 8+c 9+2*c 10+c 11+2*c 12) := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreIII_cut_relation_5_zero (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+c 7+c 8+c 9+2*c 10+c 11+2*c 12 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 7+c 2 ∧ b 7 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 8+c 3 ∧ b 8 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 4+c 5 ∧ b 4 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 5+c 6 ∧ b 5 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 4 ≤ b 7+c 9 ∧ b 7 ≤ b 4+c 9)
    (_hd10 : b 5 ≤ b 6+c 10 ∧ b 6 ≤ b 5+c 10)
    (_hd11 : b 6 ≤ b 8+c 11 ∧ b 8 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 8+c 12 ∧ b 8 ≤ b 7+c 12)
    : b 5=0 := by
  have hflow := (Nat.add_le_add _hd0.2 (Nat.add_le_add _hd1.2 (Nat.add_le_add _hd3.2 (Nat.add_le_add _hd5.2 (Nat.add_le_add _hd6.2 (Nat.add_le_add _hd7.2 (Nat.add_le_add _hd10.1 _hd11.1)))))))
  have hbound : 3*b 5 ≤ (c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+c 7+c 8+c 9+2*c 10+c 11+2*c 12) := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreIII_cut_relation_6_zero (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+c 7+c 8+c 9+2*c 10+c 11+2*c 12 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 7+c 2 ∧ b 7 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 8+c 3 ∧ b 8 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 4+c 5 ∧ b 4 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 5+c 6 ∧ b 5 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 4 ≤ b 7+c 9 ∧ b 7 ≤ b 4+c 9)
    (_hd10 : b 5 ≤ b 6+c 10 ∧ b 6 ≤ b 5+c 10)
    (_hd11 : b 6 ≤ b 8+c 11 ∧ b 8 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 8+c 12 ∧ b 8 ≤ b 7+c 12)
    : b 6=0 := by
  have hflow := (Nat.add_le_add _hd0.2 (Nat.add_le_add _hd1.2 (Nat.add_le_add _hd3.2 (Nat.add_le_add _hd5.2 (Nat.add_le_add _hd6.2 (Nat.add_le_add _hd8.2 (Nat.add_le_add _hd10.2 _hd11.1)))))))
  have hbound : 3*b 6 ≤ (c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+c 7+c 8+c 9+2*c 10+c 11+2*c 12) := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreIII_cut_relation_7_zero (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+c 7+c 8+c 9+2*c 10+c 11+2*c 12 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 7+c 2 ∧ b 7 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 8+c 3 ∧ b 8 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 4+c 5 ∧ b 4 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 5+c 6 ∧ b 5 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 4 ≤ b 7+c 9 ∧ b 7 ≤ b 4+c 9)
    (_hd10 : b 5 ≤ b 6+c 10 ∧ b 6 ≤ b 5+c 10)
    (_hd11 : b 6 ≤ b 8+c 11 ∧ b 8 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 8+c 12 ∧ b 8 ≤ b 7+c 12)
    : b 7=0 := by
  have hflow := (Nat.add_le_add _hd0.2 (Nat.add_le_add _hd2.2 (Nat.add_le_add _hd3.2 (Nat.add_le_add _hd5.2 (Nat.add_le_add _hd9.2 _hd12.1)))))
  have hbound : 3*b 7 ≤ (c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+c 7+c 8+c 9+2*c 10+c 11+2*c 12) := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreIII_cut_relation_8_zero (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+c 7+c 8+c 9+2*c 10+c 11+2*c 12 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 7+c 2 ∧ b 7 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 8+c 3 ∧ b 8 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 4+c 5 ∧ b 4 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 5+c 6 ∧ b 5 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 4 ≤ b 7+c 9 ∧ b 7 ≤ b 4+c 9)
    (_hd10 : b 5 ≤ b 6+c 10 ∧ b 6 ≤ b 5+c 10)
    (_hd11 : b 6 ≤ b 8+c 11 ∧ b 8 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 8+c 12 ∧ b 8 ≤ b 7+c 12)
    : b 8=0 := by
  have hflow := (Nat.add_le_add _hd0.2 (Nat.add_le_add _hd2.2 (Nat.add_le_add _hd3.2 (Nat.add_le_add _hd5.2 (Nat.add_le_add _hd8.2 (Nat.add_le_add _hd11.2 _hd12.2))))))
  have hbound : 3*b 8 ≤ (c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+c 7+c 8+c 9+2*c 10+c 11+2*c 12) := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 hflow
  omega

/-- The literal type-III core has only these two-edge cut masks away from its joints. -/
theorem coreIII_cut_masks (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hb : ∀ i < 9,b i ≤ 1) (_hcut : c 0+c 1+c 2+c 3+2*c 4+c 5+c 6+c 7+c 8+c 9+2*c 10+c 11+2*c 12 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 7+c 2 ∧ b 7 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 8+c 3 ∧ b 8 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    (_hd5 : b 2 ≤ b 4+c 5 ∧ b 4 ≤ b 2+c 5)
    (_hd6 : b 3 ≤ b 5+c 6 ∧ b 5 ≤ b 3+c 6)
    (_hd7 : b 4 ≤ b 5+c 7 ∧ b 5 ≤ b 4+c 7)
    (_hd8 : b 4 ≤ b 6+c 8 ∧ b 6 ≤ b 4+c 8)
    (_hd9 : b 4 ≤ b 7+c 9 ∧ b 7 ≤ b 4+c 9)
    (_hd10 : b 5 ≤ b 6+c 10 ∧ b 6 ≤ b 5+c 10)
    (_hd11 : b 6 ≤ b 8+c 11 ∧ b 8 ≤ b 6+c 11)
    (_hd12 : b 7 ≤ b 8+c 12 ∧ b 8 ≤ b 7+c 12)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8] ∈ ([[0,0,0,0,0,0,0,0,0]] : List (List ℕ)) := by
  have hrel2_zero := coreIII_cut_relation_2_zero b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12
  have hrel3_zero := coreIII_cut_relation_3_zero b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12
  have hrel4_zero := coreIII_cut_relation_4_zero b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12
  have hrel5_zero := coreIII_cut_relation_5_zero b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12
  have hrel6_zero := coreIII_cut_relation_6_zero b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12
  have hrel7_zero := coreIII_cut_relation_7_zero b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12
  have hrel8_zero := coreIII_cut_relation_8_zero b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12
  clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 c _hb
  simp only [List.mem_cons,List.not_mem_nil,or_false,List.cons.injEq,and_true]
  omega

end WaveTurbulence.Vine
