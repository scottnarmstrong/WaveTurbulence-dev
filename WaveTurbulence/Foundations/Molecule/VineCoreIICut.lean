/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-! # Core masks with cut at most two, type II

The outer joints are absent. Explicit integer flows add directed edge
inequalities before the final arithmetic step. No bounded search replaces
a proof: every flow sum is checked by the Lean kernel. -/

public section
namespace WaveTurbulence.Vine

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreII_cut_relation_2_zero (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+c 3+2*c 4 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 2+c 2 ∧ b 2 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 3+c 3 ∧ b 3 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    : b 2=0 := by
  have hflow := (Nat.add_le_add _hd0.2 (Nat.add_le_add _hd1.2 (Nat.add_le_add _hd2.2 _hd4.1)))
  have hbound : 3*b 2 ≤ (c 0+c 1+c 2+c 3+2*c 4) := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 hflow
  omega

/-- Three units of explicit integer flow certify this necessary core-mask relation. -/
theorem coreII_cut_relation_3_zero (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hcut : c 0+c 1+c 2+c 3+2*c 4 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 2+c 2 ∧ b 2 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 3+c 3 ∧ b 3 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    : b 3=0 := by
  have hflow := (Nat.add_le_add _hd0.2 (Nat.add_le_add _hd1.2 (Nat.add_le_add _hd3.2 _hd4.2)))
  have hbound : 3*b 3 ≤ (c 0+c 1+c 2+c 3+2*c 4) := by
    clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4
    omega
  clear _hd0 _hd1 _hd2 _hd3 _hd4 hflow
  omega

/-- The literal type-II core has only these two-edge cut masks away from its joints. -/
theorem coreII_cut_masks (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hb : ∀ i < 4,b i ≤ 1) (_hcut : c 0+c 1+c 2+c 3+2*c 4 ≤ 2)
    (_hd0 : b 0 ≤ b 2+c 0 ∧ b 2 ≤ b 0+c 0)
    (_hd1 : b 0 ≤ b 3+c 1 ∧ b 3 ≤ b 0+c 1)
    (_hd2 : b 1 ≤ b 2+c 2 ∧ b 2 ≤ b 1+c 2)
    (_hd3 : b 1 ≤ b 3+c 3 ∧ b 3 ≤ b 1+c 3)
    (_hd4 : b 2 ≤ b 3+c 4 ∧ b 3 ≤ b 2+c 4)
    : [b 0,b 1,b 2,b 3] ∈ ([[0,0,0,0]] : List (List ℕ)) := by
  have hrel2_zero := coreII_cut_relation_2_zero b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4
  have hrel3_zero := coreII_cut_relation_3_zero b c _h0 _h1 _hcut _hd0 _hd1 _hd2 _hd3 _hd4
  clear _hcut _hd0 _hd1 _hd2 _hd3 _hd4 c _hb
  simp only [List.mem_cons,List.not_mem_nil,or_false,List.cons.injEq,and_true]
  omega

end WaveTurbulence.Vine
