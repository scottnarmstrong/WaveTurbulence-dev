/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-! # Exhaustive degree masks for the pinned type VII core (TARGET subsetvc)

Each theorem fixes the smaller joint. The equations are the actual adjacency
matrix of the pinned template; the proof is kernel-checked integer arithmetic.
These are degree masks, not yet the vine-like containment classification. -/

public section
namespace WaveTurbulence.Vine

/-- The finite core with joints 6, 7. -/
theorem coreVII_block_6_7 (b : ℕ → ℕ)
    (_ha : b 6=1) (hj : b 7=1) (_hb : ∀ i<11,b i≤1)
    (_hd0 : b 0=1 → b 2+b 3=if 0=6 ∨ 0=7 then 2 else 4)
    (_hd1 : b 1=1 → b 9+b 10=if 1=6 ∨ 1=7 then 2 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 7=if 2=6 ∨ 2=7 then 2 else 4)
    (_hd3 : b 3=1 → b 0+2*b 2+b 8=if 3=6 ∨ 3=7 then 2 else 4)
    (_hd4 : b 4=1 → 2*b 5+2*b 6=if 4=6 ∨ 4=7 then 2 else 4)
    (_hd5 : b 5=1 → 2*b 4+b 6+b 7=if 5=6 ∨ 5=7 then 2 else 4)
    (_hd6 : b 6=1 → 2*b 4+b 5+b 8=if 6=6 ∨ 6=7 then 2 else 4)
    (_hd7 : b 7=1 → b 2+b 5+b 8+b 9=if 7=6 ∨ 7=7 then 2 else 4)
    (_hd8 : b 8=1 → b 3+b 6+b 7+b 10=if 8=6 ∨ 8=7 then 2 else 4)
    (_hd9 : b 9=1 → b 1+b 7+2*b 10=if 9=6 ∨ 9=7 then 2 else 4)
    (_hd10 : b 10=1 → b 1+b 8+2*b 9=if 10=6 ∨ 10=7 then 2 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9,b 10] ∈ ([] : List (List ℕ)) := by
  have hb0 := _hb 0 (by decide)
  have hb1 := _hb 1 (by decide)
  have hb2 := _hb 2 (by decide)
  have hb3 := _hb 3 (by decide)
  have hb4 := _hb 4 (by decide)
  have hb5 := _hb 5 (by decide)
  have hb6 := _hb 6 (by decide)
  have hb7 := _hb 7 (by decide)
  have hb8 := _hb 8 (by decide)
  have hb9 := _hb 9 (by decide)
  have hb10 := _hb 10 (by decide)
  norm_num at hj _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 ⊢
  all_goals omega

/-- The finite core with joints 6, 8. -/
theorem coreVII_block_6_8 (b : ℕ → ℕ)
    (_ha : b 6=1) (hj : b 8=1) (_hb : ∀ i<11,b i≤1)
    (_hd0 : b 0=1 → b 2+b 3=if 0=6 ∨ 0=8 then 2 else 4)
    (_hd1 : b 1=1 → b 9+b 10=if 1=6 ∨ 1=8 then 2 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 7=if 2=6 ∨ 2=8 then 2 else 4)
    (_hd3 : b 3=1 → b 0+2*b 2+b 8=if 3=6 ∨ 3=8 then 2 else 4)
    (_hd4 : b 4=1 → 2*b 5+2*b 6=if 4=6 ∨ 4=8 then 2 else 4)
    (_hd5 : b 5=1 → 2*b 4+b 6+b 7=if 5=6 ∨ 5=8 then 2 else 4)
    (_hd6 : b 6=1 → 2*b 4+b 5+b 8=if 6=6 ∨ 6=8 then 2 else 4)
    (_hd7 : b 7=1 → b 2+b 5+b 8+b 9=if 7=6 ∨ 7=8 then 2 else 4)
    (_hd8 : b 8=1 → b 3+b 6+b 7+b 10=if 8=6 ∨ 8=8 then 2 else 4)
    (_hd9 : b 9=1 → b 1+b 7+2*b 10=if 9=6 ∨ 9=8 then 2 else 4)
    (_hd10 : b 10=1 → b 1+b 8+2*b 9=if 10=6 ∨ 10=8 then 2 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9,b 10] ∈ ([] : List (List ℕ)) := by
  have hb0 := _hb 0 (by decide)
  have hb1 := _hb 1 (by decide)
  have hb2 := _hb 2 (by decide)
  have hb3 := _hb 3 (by decide)
  have hb4 := _hb 4 (by decide)
  have hb5 := _hb 5 (by decide)
  have hb6 := _hb 6 (by decide)
  have hb7 := _hb 7 (by decide)
  have hb8 := _hb 8 (by decide)
  have hb9 := _hb 9 (by decide)
  have hb10 := _hb 10 (by decide)
  norm_num at hj _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 ⊢
  all_goals omega

/-- The finite core with joints 6, 9. -/
theorem coreVII_block_6_9 (b : ℕ → ℕ)
    (_ha : b 6=1) (hj : b 9=1) (_hb : ∀ i<11,b i≤1)
    (_hd0 : b 0=1 → b 2+b 3=if 0=6 ∨ 0=9 then 2 else 4)
    (_hd1 : b 1=1 → b 9+b 10=if 1=6 ∨ 1=9 then 2 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 7=if 2=6 ∨ 2=9 then 2 else 4)
    (_hd3 : b 3=1 → b 0+2*b 2+b 8=if 3=6 ∨ 3=9 then 2 else 4)
    (_hd4 : b 4=1 → 2*b 5+2*b 6=if 4=6 ∨ 4=9 then 2 else 4)
    (_hd5 : b 5=1 → 2*b 4+b 6+b 7=if 5=6 ∨ 5=9 then 2 else 4)
    (_hd6 : b 6=1 → 2*b 4+b 5+b 8=if 6=6 ∨ 6=9 then 2 else 4)
    (_hd7 : b 7=1 → b 2+b 5+b 8+b 9=if 7=6 ∨ 7=9 then 2 else 4)
    (_hd8 : b 8=1 → b 3+b 6+b 7+b 10=if 8=6 ∨ 8=9 then 2 else 4)
    (_hd9 : b 9=1 → b 1+b 7+2*b 10=if 9=6 ∨ 9=9 then 2 else 4)
    (_hd10 : b 10=1 → b 1+b 8+2*b 9=if 10=6 ∨ 10=9 then 2 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9,b 10] ∈ ([] : List (List ℕ)) := by
  have hb0 := _hb 0 (by decide)
  have hb1 := _hb 1 (by decide)
  have hb2 := _hb 2 (by decide)
  have hb3 := _hb 3 (by decide)
  have hb4 := _hb 4 (by decide)
  have hb5 := _hb 5 (by decide)
  have hb6 := _hb 6 (by decide)
  have hb7 := _hb 7 (by decide)
  have hb8 := _hb 8 (by decide)
  have hb9 := _hb 9 (by decide)
  have hb10 := _hb 10 (by decide)
  norm_num at hj _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 ⊢
  all_goals omega

/-- The finite core with joints 6, 10. -/
theorem coreVII_block_6_10 (b : ℕ → ℕ)
    (_ha : b 6=1) (hj : b 10=1) (_hb : ∀ i<11,b i≤1)
    (_hd0 : b 0=1 → b 2+b 3=if 0=6 ∨ 0=10 then 2 else 4)
    (_hd1 : b 1=1 → b 9+b 10=if 1=6 ∨ 1=10 then 2 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 7=if 2=6 ∨ 2=10 then 2 else 4)
    (_hd3 : b 3=1 → b 0+2*b 2+b 8=if 3=6 ∨ 3=10 then 2 else 4)
    (_hd4 : b 4=1 → 2*b 5+2*b 6=if 4=6 ∨ 4=10 then 2 else 4)
    (_hd5 : b 5=1 → 2*b 4+b 6+b 7=if 5=6 ∨ 5=10 then 2 else 4)
    (_hd6 : b 6=1 → 2*b 4+b 5+b 8=if 6=6 ∨ 6=10 then 2 else 4)
    (_hd7 : b 7=1 → b 2+b 5+b 8+b 9=if 7=6 ∨ 7=10 then 2 else 4)
    (_hd8 : b 8=1 → b 3+b 6+b 7+b 10=if 8=6 ∨ 8=10 then 2 else 4)
    (_hd9 : b 9=1 → b 1+b 7+2*b 10=if 9=6 ∨ 9=10 then 2 else 4)
    (_hd10 : b 10=1 → b 1+b 8+2*b 9=if 10=6 ∨ 10=10 then 2 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9,b 10] ∈ ([] : List (List ℕ)) := by
  have hb0 := _hb 0 (by decide)
  have hb1 := _hb 1 (by decide)
  have hb2 := _hb 2 (by decide)
  have hb3 := _hb 3 (by decide)
  have hb4 := _hb 4 (by decide)
  have hb5 := _hb 5 (by decide)
  have hb6 := _hb 6 (by decide)
  have hb7 := _hb 7 (by decide)
  have hb8 := _hb 8 (by decide)
  have hb9 := _hb 9 (by decide)
  have hb10 := _hb 10 (by decide)
  norm_num at hj _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 ⊢
  all_goals omega

end WaveTurbulence.Vine
