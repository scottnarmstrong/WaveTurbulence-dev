/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-! # Exhaustive degree masks for the pinned type VIII core (TARGET subsetvc)

Each theorem fixes the smaller joint. The equations are the actual adjacency
matrix of the pinned template; the proof is kernel-checked integer arithmetic.
These are degree masks, not yet the vine-like containment classification. -/

public section
namespace WaveTurbulence.Vine

/-- The finite core with joints 4, 5. -/
theorem coreVIII_hyper_4_5 (b : ℕ → ℕ)
    (_ha : b 4=1) (hj : b 5=1) (_hb : ∀ i<11,b i≤1)
    (_hd0 : b 0=1 → b 2+b 6=if 0=4 ∨ 0=5 then 3 else 4)
    (_hd1 : b 1=1 → b 4+b 5=if 1=4 ∨ 1=5 then 3 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 4=if 2=4 ∨ 2=5 then 3 else 4)
    (_hd3 : b 3=1 → 2*b 2+b 5+b 7=if 3=4 ∨ 3=5 then 3 else 4)
    (_hd4 : b 4=1 → b 1+b 2+2*b 5=if 4=4 ∨ 4=5 then 3 else 4)
    (_hd5 : b 5=1 → b 1+b 3+2*b 4=if 5=4 ∨ 5=5 then 3 else 4)
    (_hd6 : b 6=1 → b 0+2*b 7+b 8=if 6=4 ∨ 6=5 then 3 else 4)
    (_hd7 : b 7=1 → b 3+2*b 6+b 9=if 7=4 ∨ 7=5 then 3 else 4)
    (_hd8 : b 8=1 → b 6+b 9+2*b 10=if 8=4 ∨ 8=5 then 3 else 4)
    (_hd9 : b 9=1 → b 7+b 8+2*b 10=if 9=4 ∨ 9=5 then 3 else 4)
    (_hd10 : b 10=1 → 2*b 8+2*b 9=if 10=4 ∨ 10=5 then 3 else 4)
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

/-- The finite core with joints 4, 6. -/
theorem coreVIII_hyper_4_6 (b : ℕ → ℕ)
    (_ha : b 4=1) (hj : b 6=1) (_hb : ∀ i<11,b i≤1)
    (_hd0 : b 0=1 → b 2+b 6=if 0=4 ∨ 0=6 then 3 else 4)
    (_hd1 : b 1=1 → b 4+b 5=if 1=4 ∨ 1=6 then 3 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 4=if 2=4 ∨ 2=6 then 3 else 4)
    (_hd3 : b 3=1 → 2*b 2+b 5+b 7=if 3=4 ∨ 3=6 then 3 else 4)
    (_hd4 : b 4=1 → b 1+b 2+2*b 5=if 4=4 ∨ 4=6 then 3 else 4)
    (_hd5 : b 5=1 → b 1+b 3+2*b 4=if 5=4 ∨ 5=6 then 3 else 4)
    (_hd6 : b 6=1 → b 0+2*b 7+b 8=if 6=4 ∨ 6=6 then 3 else 4)
    (_hd7 : b 7=1 → b 3+2*b 6+b 9=if 7=4 ∨ 7=6 then 3 else 4)
    (_hd8 : b 8=1 → b 6+b 9+2*b 10=if 8=4 ∨ 8=6 then 3 else 4)
    (_hd9 : b 9=1 → b 7+b 8+2*b 10=if 9=4 ∨ 9=6 then 3 else 4)
    (_hd10 : b 10=1 → 2*b 8+2*b 9=if 10=4 ∨ 10=6 then 3 else 4)
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

/-- The finite core with joints 4, 7. -/
theorem coreVIII_hyper_4_7 (b : ℕ → ℕ)
    (_ha : b 4=1) (hj : b 7=1) (_hb : ∀ i<11,b i≤1)
    (_hd0 : b 0=1 → b 2+b 6=if 0=4 ∨ 0=7 then 3 else 4)
    (_hd1 : b 1=1 → b 4+b 5=if 1=4 ∨ 1=7 then 3 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 4=if 2=4 ∨ 2=7 then 3 else 4)
    (_hd3 : b 3=1 → 2*b 2+b 5+b 7=if 3=4 ∨ 3=7 then 3 else 4)
    (_hd4 : b 4=1 → b 1+b 2+2*b 5=if 4=4 ∨ 4=7 then 3 else 4)
    (_hd5 : b 5=1 → b 1+b 3+2*b 4=if 5=4 ∨ 5=7 then 3 else 4)
    (_hd6 : b 6=1 → b 0+2*b 7+b 8=if 6=4 ∨ 6=7 then 3 else 4)
    (_hd7 : b 7=1 → b 3+2*b 6+b 9=if 7=4 ∨ 7=7 then 3 else 4)
    (_hd8 : b 8=1 → b 6+b 9+2*b 10=if 8=4 ∨ 8=7 then 3 else 4)
    (_hd9 : b 9=1 → b 7+b 8+2*b 10=if 9=4 ∨ 9=7 then 3 else 4)
    (_hd10 : b 10=1 → 2*b 8+2*b 9=if 10=4 ∨ 10=7 then 3 else 4)
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

/-- The finite core with joints 4, 8. -/
theorem coreVIII_hyper_4_8 (b : ℕ → ℕ)
    (_ha : b 4=1) (hj : b 8=1) (_hb : ∀ i<11,b i≤1)
    (_hd0 : b 0=1 → b 2+b 6=if 0=4 ∨ 0=8 then 3 else 4)
    (_hd1 : b 1=1 → b 4+b 5=if 1=4 ∨ 1=8 then 3 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 4=if 2=4 ∨ 2=8 then 3 else 4)
    (_hd3 : b 3=1 → 2*b 2+b 5+b 7=if 3=4 ∨ 3=8 then 3 else 4)
    (_hd4 : b 4=1 → b 1+b 2+2*b 5=if 4=4 ∨ 4=8 then 3 else 4)
    (_hd5 : b 5=1 → b 1+b 3+2*b 4=if 5=4 ∨ 5=8 then 3 else 4)
    (_hd6 : b 6=1 → b 0+2*b 7+b 8=if 6=4 ∨ 6=8 then 3 else 4)
    (_hd7 : b 7=1 → b 3+2*b 6+b 9=if 7=4 ∨ 7=8 then 3 else 4)
    (_hd8 : b 8=1 → b 6+b 9+2*b 10=if 8=4 ∨ 8=8 then 3 else 4)
    (_hd9 : b 9=1 → b 7+b 8+2*b 10=if 9=4 ∨ 9=8 then 3 else 4)
    (_hd10 : b 10=1 → 2*b 8+2*b 9=if 10=4 ∨ 10=8 then 3 else 4)
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

/-- The finite core with joints 4, 9. -/
theorem coreVIII_hyper_4_9 (b : ℕ → ℕ)
    (_ha : b 4=1) (hj : b 9=1) (_hb : ∀ i<11,b i≤1)
    (_hd0 : b 0=1 → b 2+b 6=if 0=4 ∨ 0=9 then 3 else 4)
    (_hd1 : b 1=1 → b 4+b 5=if 1=4 ∨ 1=9 then 3 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 4=if 2=4 ∨ 2=9 then 3 else 4)
    (_hd3 : b 3=1 → 2*b 2+b 5+b 7=if 3=4 ∨ 3=9 then 3 else 4)
    (_hd4 : b 4=1 → b 1+b 2+2*b 5=if 4=4 ∨ 4=9 then 3 else 4)
    (_hd5 : b 5=1 → b 1+b 3+2*b 4=if 5=4 ∨ 5=9 then 3 else 4)
    (_hd6 : b 6=1 → b 0+2*b 7+b 8=if 6=4 ∨ 6=9 then 3 else 4)
    (_hd7 : b 7=1 → b 3+2*b 6+b 9=if 7=4 ∨ 7=9 then 3 else 4)
    (_hd8 : b 8=1 → b 6+b 9+2*b 10=if 8=4 ∨ 8=9 then 3 else 4)
    (_hd9 : b 9=1 → b 7+b 8+2*b 10=if 9=4 ∨ 9=9 then 3 else 4)
    (_hd10 : b 10=1 → 2*b 8+2*b 9=if 10=4 ∨ 10=9 then 3 else 4)
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

/-- The finite core with joints 4, 10. -/
theorem coreVIII_hyper_4_10 (b : ℕ → ℕ)
    (_ha : b 4=1) (hj : b 10=1) (_hb : ∀ i<11,b i≤1)
    (_hd0 : b 0=1 → b 2+b 6=if 0=4 ∨ 0=10 then 3 else 4)
    (_hd1 : b 1=1 → b 4+b 5=if 1=4 ∨ 1=10 then 3 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 4=if 2=4 ∨ 2=10 then 3 else 4)
    (_hd3 : b 3=1 → 2*b 2+b 5+b 7=if 3=4 ∨ 3=10 then 3 else 4)
    (_hd4 : b 4=1 → b 1+b 2+2*b 5=if 4=4 ∨ 4=10 then 3 else 4)
    (_hd5 : b 5=1 → b 1+b 3+2*b 4=if 5=4 ∨ 5=10 then 3 else 4)
    (_hd6 : b 6=1 → b 0+2*b 7+b 8=if 6=4 ∨ 6=10 then 3 else 4)
    (_hd7 : b 7=1 → b 3+2*b 6+b 9=if 7=4 ∨ 7=10 then 3 else 4)
    (_hd8 : b 8=1 → b 6+b 9+2*b 10=if 8=4 ∨ 8=10 then 3 else 4)
    (_hd9 : b 9=1 → b 7+b 8+2*b 10=if 9=4 ∨ 9=10 then 3 else 4)
    (_hd10 : b 10=1 → 2*b 8+2*b 9=if 10=4 ∨ 10=10 then 3 else 4)
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
