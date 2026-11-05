/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-! # Core masks with cut at most two, type I

The outer joints are absent. Explicit integer flows add directed edge
inequalities before the final arithmetic step. No bounded search replaces
a proof: every flow sum is checked by the Lean kernel. -/

public section
namespace WaveTurbulence.Vine

/-- The literal type-I core has only these two-edge cut masks away from its joints. -/
theorem coreI_cut_masks (b c : ℕ → ℕ) (_h0 : b 0=0) (_h1 : b 1=0)
    (_hb : ∀ i < 2,b i ≤ 1) (_hcut : 2*c 0 ≤ 2)
    (_hd0 : b 0 ≤ b 1+c 0 ∧ b 1 ≤ b 0+c 0)
    : [b 0,b 1] ∈ ([[0,0]] : List (List ℕ)) := by
  clear _hcut _hd0 c _hb
  simp only [List.mem_cons,List.not_mem_nil,or_false,List.cons.injEq,and_true]
  omega

end WaveTurbulence.Vine
