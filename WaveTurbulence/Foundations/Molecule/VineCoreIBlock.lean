/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-! # Exhaustive degree masks for the pinned type I core (TARGET subsetvc)

Each theorem fixes the smaller joint. The equations are the actual adjacency
matrix of the pinned template; the proof is kernel-checked integer arithmetic.
These are degree masks, not yet the vine-like containment classification. -/

public section
namespace WaveTurbulence.Vine

/-- Exhaustive finite-core masks with smaller joint 0. -/
theorem coreI_block_0 (b : ℕ → ℕ) (j : ℕ)
    (hj0 : 0<j) (hj1 : j<2) (_ha : b 0=1) (hj : b j=1)
    (_hb : ∀ i<2,b i≤1)
    (_hd0 : b 0=1 → 2*b 1=if 0=0 ∨ 0=j then 2 else 4)
    (_hd1 : b 1=1 → 2*b 0=if 1=0 ∨ 1=j then 2 else 4)
    : [b 0,b 1] ∈ ([[1,1]] : List (List ℕ)) := by
  have hb0 := _hb 0 (by decide)
  have hb1 := _hb 1 (by decide)
  interval_cases j
  all_goals norm_num at hj _hd0 _hd1 ⊢
  all_goals omega

end WaveTurbulence.Vine
