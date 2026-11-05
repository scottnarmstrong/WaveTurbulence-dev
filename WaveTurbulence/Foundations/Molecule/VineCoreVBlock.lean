/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-! # Exhaustive degree masks for the pinned type V core (TARGET subsetvc)

Each theorem fixes the smaller joint. The equations are the actual adjacency
matrix of the pinned template; the proof is kernel-checked integer arithmetic.
These are degree masks, not yet the vine-like containment classification. -/

public section
namespace WaveTurbulence.Vine

/-- Exhaustive finite-core masks with smaller joint 0. -/
theorem coreV_block_0 (b : ℕ → ℕ) (j : ℕ)
    (hj0 : 0<j) (hj1 : j<9) (_ha : b 0=1) (hj : b j=1)
    (_hb : ∀ i<9,b i≤1)
    (_hd0 : b 0=1 → b 1+b 2=if 0=0 ∨ 0=j then 2 else 4)
    (_hd1 : b 1=1 → b 0+b 3=if 1=0 ∨ 1=j then 2 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 4=if 2=0 ∨ 2=j then 2 else 4)
    (_hd3 : b 3=1 → b 1+2*b 2+b 5=if 3=0 ∨ 3=j then 2 else 4)
    (_hd4 : b 4=1 → b 2+2*b 5+b 6=if 4=0 ∨ 4=j then 2 else 4)
    (_hd5 : b 5=1 → b 3+2*b 4+b 7=if 5=0 ∨ 5=j then 2 else 4)
    (_hd6 : b 6=1 → b 4+b 7+2*b 8=if 6=0 ∨ 6=j then 2 else 4)
    (_hd7 : b 7=1 → b 5+b 6+2*b 8=if 7=0 ∨ 7=j then 2 else 4)
    (_hd8 : b 8=1 → 2*b 6+2*b 7=if 8=0 ∨ 8=j then 2 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8] ∈ ([[1,1,1,1,1,1,1,1,1]] : List (List ℕ)) := by
  have hb0 := _hb 0 (by decide)
  have hb1 := _hb 1 (by decide)
  have hb2 := _hb 2 (by decide)
  have hb3 := _hb 3 (by decide)
  have hb4 := _hb 4 (by decide)
  have hb5 := _hb 5 (by decide)
  have hb6 := _hb 6 (by decide)
  have hb7 := _hb 7 (by decide)
  have hb8 := _hb 8 (by decide)
  interval_cases j
  all_goals norm_num at hj _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 ⊢
  all_goals omega

/-- Exhaustive finite-core masks with smaller joint 1. -/
theorem coreV_block_1 (b : ℕ → ℕ) (j : ℕ)
    (hj0 : 1<j) (hj1 : j<9) (_ha : b 1=1) (hj : b j=1)
    (_hb : ∀ i<9,b i≤1)
    (_hd0 : b 0=1 → b 1+b 2=if 0=1 ∨ 0=j then 2 else 4)
    (_hd1 : b 1=1 → b 0+b 3=if 1=1 ∨ 1=j then 2 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 4=if 2=1 ∨ 2=j then 2 else 4)
    (_hd3 : b 3=1 → b 1+2*b 2+b 5=if 3=1 ∨ 3=j then 2 else 4)
    (_hd4 : b 4=1 → b 2+2*b 5+b 6=if 4=1 ∨ 4=j then 2 else 4)
    (_hd5 : b 5=1 → b 3+2*b 4+b 7=if 5=1 ∨ 5=j then 2 else 4)
    (_hd6 : b 6=1 → b 4+b 7+2*b 8=if 6=1 ∨ 6=j then 2 else 4)
    (_hd7 : b 7=1 → b 5+b 6+2*b 8=if 7=1 ∨ 7=j then 2 else 4)
    (_hd8 : b 8=1 → 2*b 6+2*b 7=if 8=1 ∨ 8=j then 2 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8] ∈ ([] : List (List ℕ)) := by
  have hb0 := _hb 0 (by decide)
  have hb1 := _hb 1 (by decide)
  have hb2 := _hb 2 (by decide)
  have hb3 := _hb 3 (by decide)
  have hb4 := _hb 4 (by decide)
  have hb5 := _hb 5 (by decide)
  have hb6 := _hb 6 (by decide)
  have hb7 := _hb 7 (by decide)
  have hb8 := _hb 8 (by decide)
  interval_cases j
  all_goals norm_num at hj _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 ⊢
  all_goals omega

/-- Exhaustive finite-core masks with smaller joint 2. -/
theorem coreV_block_2 (b : ℕ → ℕ) (j : ℕ)
    (hj0 : 2<j) (hj1 : j<9) (_ha : b 2=1) (hj : b j=1)
    (_hb : ∀ i<9,b i≤1)
    (_hd0 : b 0=1 → b 1+b 2=if 0=2 ∨ 0=j then 2 else 4)
    (_hd1 : b 1=1 → b 0+b 3=if 1=2 ∨ 1=j then 2 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 4=if 2=2 ∨ 2=j then 2 else 4)
    (_hd3 : b 3=1 → b 1+2*b 2+b 5=if 3=2 ∨ 3=j then 2 else 4)
    (_hd4 : b 4=1 → b 2+2*b 5+b 6=if 4=2 ∨ 4=j then 2 else 4)
    (_hd5 : b 5=1 → b 3+2*b 4+b 7=if 5=2 ∨ 5=j then 2 else 4)
    (_hd6 : b 6=1 → b 4+b 7+2*b 8=if 6=2 ∨ 6=j then 2 else 4)
    (_hd7 : b 7=1 → b 5+b 6+2*b 8=if 7=2 ∨ 7=j then 2 else 4)
    (_hd8 : b 8=1 → 2*b 6+2*b 7=if 8=2 ∨ 8=j then 2 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8] ∈ ([[0,0,1,1,0,0,0,0,0]] : List (List ℕ)) := by
  have hb0 := _hb 0 (by decide)
  have hb1 := _hb 1 (by decide)
  have hb2 := _hb 2 (by decide)
  have hb3 := _hb 3 (by decide)
  have hb4 := _hb 4 (by decide)
  have hb5 := _hb 5 (by decide)
  have hb6 := _hb 6 (by decide)
  have hb7 := _hb 7 (by decide)
  have hb8 := _hb 8 (by decide)
  interval_cases j
  all_goals norm_num at hj _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 ⊢
  all_goals omega

/-- Exhaustive finite-core masks with smaller joint 3. -/
theorem coreV_block_3 (b : ℕ → ℕ) (j : ℕ)
    (hj0 : 3<j) (hj1 : j<9) (_ha : b 3=1) (hj : b j=1)
    (_hb : ∀ i<9,b i≤1)
    (_hd0 : b 0=1 → b 1+b 2=if 0=3 ∨ 0=j then 2 else 4)
    (_hd1 : b 1=1 → b 0+b 3=if 1=3 ∨ 1=j then 2 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 4=if 2=3 ∨ 2=j then 2 else 4)
    (_hd3 : b 3=1 → b 1+2*b 2+b 5=if 3=3 ∨ 3=j then 2 else 4)
    (_hd4 : b 4=1 → b 2+2*b 5+b 6=if 4=3 ∨ 4=j then 2 else 4)
    (_hd5 : b 5=1 → b 3+2*b 4+b 7=if 5=3 ∨ 5=j then 2 else 4)
    (_hd6 : b 6=1 → b 4+b 7+2*b 8=if 6=3 ∨ 6=j then 2 else 4)
    (_hd7 : b 7=1 → b 5+b 6+2*b 8=if 7=3 ∨ 7=j then 2 else 4)
    (_hd8 : b 8=1 → 2*b 6+2*b 7=if 8=3 ∨ 8=j then 2 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8] ∈ ([] : List (List ℕ)) := by
  have hb0 := _hb 0 (by decide)
  have hb1 := _hb 1 (by decide)
  have hb2 := _hb 2 (by decide)
  have hb3 := _hb 3 (by decide)
  have hb4 := _hb 4 (by decide)
  have hb5 := _hb 5 (by decide)
  have hb6 := _hb 6 (by decide)
  have hb7 := _hb 7 (by decide)
  have hb8 := _hb 8 (by decide)
  interval_cases j
  all_goals norm_num at hj _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 ⊢
  all_goals omega

/-- Exhaustive finite-core masks with smaller joint 4. -/
theorem coreV_block_4 (b : ℕ → ℕ) (j : ℕ)
    (hj0 : 4<j) (hj1 : j<9) (_ha : b 4=1) (hj : b j=1)
    (_hb : ∀ i<9,b i≤1)
    (_hd0 : b 0=1 → b 1+b 2=if 0=4 ∨ 0=j then 2 else 4)
    (_hd1 : b 1=1 → b 0+b 3=if 1=4 ∨ 1=j then 2 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 4=if 2=4 ∨ 2=j then 2 else 4)
    (_hd3 : b 3=1 → b 1+2*b 2+b 5=if 3=4 ∨ 3=j then 2 else 4)
    (_hd4 : b 4=1 → b 2+2*b 5+b 6=if 4=4 ∨ 4=j then 2 else 4)
    (_hd5 : b 5=1 → b 3+2*b 4+b 7=if 5=4 ∨ 5=j then 2 else 4)
    (_hd6 : b 6=1 → b 4+b 7+2*b 8=if 6=4 ∨ 6=j then 2 else 4)
    (_hd7 : b 7=1 → b 5+b 6+2*b 8=if 7=4 ∨ 7=j then 2 else 4)
    (_hd8 : b 8=1 → 2*b 6+2*b 7=if 8=4 ∨ 8=j then 2 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8] ∈ ([[0,0,0,0,1,1,0,0,0]] : List (List ℕ)) := by
  have hb0 := _hb 0 (by decide)
  have hb1 := _hb 1 (by decide)
  have hb2 := _hb 2 (by decide)
  have hb3 := _hb 3 (by decide)
  have hb4 := _hb 4 (by decide)
  have hb5 := _hb 5 (by decide)
  have hb6 := _hb 6 (by decide)
  have hb7 := _hb 7 (by decide)
  have hb8 := _hb 8 (by decide)
  interval_cases j
  all_goals norm_num at hj _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 ⊢
  all_goals omega

/-- Exhaustive finite-core masks with smaller joint 5. -/
theorem coreV_block_5 (b : ℕ → ℕ) (j : ℕ)
    (hj0 : 5<j) (hj1 : j<9) (_ha : b 5=1) (hj : b j=1)
    (_hb : ∀ i<9,b i≤1)
    (_hd0 : b 0=1 → b 1+b 2=if 0=5 ∨ 0=j then 2 else 4)
    (_hd1 : b 1=1 → b 0+b 3=if 1=5 ∨ 1=j then 2 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 4=if 2=5 ∨ 2=j then 2 else 4)
    (_hd3 : b 3=1 → b 1+2*b 2+b 5=if 3=5 ∨ 3=j then 2 else 4)
    (_hd4 : b 4=1 → b 2+2*b 5+b 6=if 4=5 ∨ 4=j then 2 else 4)
    (_hd5 : b 5=1 → b 3+2*b 4+b 7=if 5=5 ∨ 5=j then 2 else 4)
    (_hd6 : b 6=1 → b 4+b 7+2*b 8=if 6=5 ∨ 6=j then 2 else 4)
    (_hd7 : b 7=1 → b 5+b 6+2*b 8=if 7=5 ∨ 7=j then 2 else 4)
    (_hd8 : b 8=1 → 2*b 6+2*b 7=if 8=5 ∨ 8=j then 2 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8] ∈ ([] : List (List ℕ)) := by
  have hb0 := _hb 0 (by decide)
  have hb1 := _hb 1 (by decide)
  have hb2 := _hb 2 (by decide)
  have hb3 := _hb 3 (by decide)
  have hb4 := _hb 4 (by decide)
  have hb5 := _hb 5 (by decide)
  have hb6 := _hb 6 (by decide)
  have hb7 := _hb 7 (by decide)
  have hb8 := _hb 8 (by decide)
  interval_cases j
  all_goals norm_num at hj _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 ⊢
  all_goals omega

/-- Exhaustive finite-core masks with smaller joint 6. -/
theorem coreV_block_6 (b : ℕ → ℕ) (j : ℕ)
    (hj0 : 6<j) (hj1 : j<9) (_ha : b 6=1) (hj : b j=1)
    (_hb : ∀ i<9,b i≤1)
    (_hd0 : b 0=1 → b 1+b 2=if 0=6 ∨ 0=j then 2 else 4)
    (_hd1 : b 1=1 → b 0+b 3=if 1=6 ∨ 1=j then 2 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 4=if 2=6 ∨ 2=j then 2 else 4)
    (_hd3 : b 3=1 → b 1+2*b 2+b 5=if 3=6 ∨ 3=j then 2 else 4)
    (_hd4 : b 4=1 → b 2+2*b 5+b 6=if 4=6 ∨ 4=j then 2 else 4)
    (_hd5 : b 5=1 → b 3+2*b 4+b 7=if 5=6 ∨ 5=j then 2 else 4)
    (_hd6 : b 6=1 → b 4+b 7+2*b 8=if 6=6 ∨ 6=j then 2 else 4)
    (_hd7 : b 7=1 → b 5+b 6+2*b 8=if 7=6 ∨ 7=j then 2 else 4)
    (_hd8 : b 8=1 → 2*b 6+2*b 7=if 8=6 ∨ 8=j then 2 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8] ∈ ([[0,0,0,0,0,0,1,0,1]] : List (List ℕ)) := by
  have hb0 := _hb 0 (by decide)
  have hb1 := _hb 1 (by decide)
  have hb2 := _hb 2 (by decide)
  have hb3 := _hb 3 (by decide)
  have hb4 := _hb 4 (by decide)
  have hb5 := _hb 5 (by decide)
  have hb6 := _hb 6 (by decide)
  have hb7 := _hb 7 (by decide)
  have hb8 := _hb 8 (by decide)
  interval_cases j
  all_goals norm_num at hj _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 ⊢
  all_goals omega

/-- Exhaustive finite-core masks with smaller joint 7. -/
theorem coreV_block_7 (b : ℕ → ℕ) (j : ℕ)
    (hj0 : 7<j) (hj1 : j<9) (_ha : b 7=1) (hj : b j=1)
    (_hb : ∀ i<9,b i≤1)
    (_hd0 : b 0=1 → b 1+b 2=if 0=7 ∨ 0=j then 2 else 4)
    (_hd1 : b 1=1 → b 0+b 3=if 1=7 ∨ 1=j then 2 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 4=if 2=7 ∨ 2=j then 2 else 4)
    (_hd3 : b 3=1 → b 1+2*b 2+b 5=if 3=7 ∨ 3=j then 2 else 4)
    (_hd4 : b 4=1 → b 2+2*b 5+b 6=if 4=7 ∨ 4=j then 2 else 4)
    (_hd5 : b 5=1 → b 3+2*b 4+b 7=if 5=7 ∨ 5=j then 2 else 4)
    (_hd6 : b 6=1 → b 4+b 7+2*b 8=if 6=7 ∨ 6=j then 2 else 4)
    (_hd7 : b 7=1 → b 5+b 6+2*b 8=if 7=7 ∨ 7=j then 2 else 4)
    (_hd8 : b 8=1 → 2*b 6+2*b 7=if 8=7 ∨ 8=j then 2 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8] ∈ ([[0,0,0,0,0,0,0,1,1]] : List (List ℕ)) := by
  have hb0 := _hb 0 (by decide)
  have hb1 := _hb 1 (by decide)
  have hb2 := _hb 2 (by decide)
  have hb3 := _hb 3 (by decide)
  have hb4 := _hb 4 (by decide)
  have hb5 := _hb 5 (by decide)
  have hb6 := _hb 6 (by decide)
  have hb7 := _hb 7 (by decide)
  have hb8 := _hb 8 (by decide)
  interval_cases j
  all_goals norm_num at hj _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 ⊢
  all_goals omega

end WaveTurbulence.Vine
