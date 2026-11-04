/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.CollisionOp
public import WaveTurbulence.Frozen.Defs.Mom

/-!
# wkeTaylorTerm

Wave B tier B1 (WaveB1-System.lean), source: T (wketaylor2), L753–L755. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

/-- **`𝒰^{(p)}_n(t, k)`** (T (wketaylor2), L753–L755): `𝒰₀ = φ(pδ)` and
`𝒰_{n+1}(t) = δ ∑_{n₁+n₂+n₃ = n} ∫_p^t 𝒦(𝒰_{n₁}(t'), 𝒰_{n₂}(t'), 𝒰_{n₃}(t')) dt'`. -/
noncomputable def wkeTaylorTerm {d : ℕ} (φp : Mom d → ℝ) (δ : ℝ) (p : ℝ) :
    ℕ → ℝ → Mom d → ℝ
  | 0 => fun _ => φp
  | n + 1 => fun t k => δ * ∑ x ∈ (Finset.Nat.antidiagonalTuple 3 n).attach,
      ∫ t' in p..t, collisionOp
        (wkeTaylorTerm φp δ p (x.1 0) t')
        (wkeTaylorTerm φp δ p (x.1 1) t')
        (wkeTaylorTerm φp δ p (x.1 2) t') k
  decreasing_by
    all_goals
      have h := (Finset.Nat.mem_antidiagonalTuple.1 x.2)
      have h2 : ∀ i, x.1 i ≤ n := fun i => by
        have := Finset.single_le_sum (f := x.1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        rw [h] at this
        exact this
      exact Nat.lt_succ_of_le (h2 _)

end WaveTurbulence
