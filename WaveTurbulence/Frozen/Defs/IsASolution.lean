/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.ANonlin
public import WaveTurbulence.Frozen.Defs.LatticePoint
public import WaveTurbulence.Frozen.Defs.Mom

/-!
# IsASolution

Wave B tier B1 (WaveB1-System.lean), source: T (akeqn); L545–L564; WAVE-B §2.3.2. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

/-- **Classed solutions of the `a`-system** (T (akeqn)–(akeqn2), L545–L564; WAVE-B §2.3.2 with Q16
and review C1): `a(0) = c`, the class `sup_{t ∈ [0,T]} sup_n ⟨n/L⟩^{d+1} |a_n(t)| < ∞` (in which the
sums of `𝒞₊` converge absolutely and uniqueness holds), and `∂ₜ a_n = 𝒞₊(a, ā, a)_n(t)` within
`[0, T]` at every `t ∈ [0, T]`. Same body as the landed `NLS.IsAkSolution` (bridge
`isASolution_iff_nls`). -/
def IsASolution {d : ℕ} (L γ δ T : ℝ) (c : (Fin d → ℤ) → ℂ) (a : ℝ → (Fin d → ℤ) → ℂ) : Prop :=
  a 0 = c ∧
    (∃ C, ∀ t ∈ Icc 0 T, ∀ n, (1 + ‖latticePoint L n‖ ^ 2) ^ (((d : ℝ) + 1) / 2) * ‖a t n‖ ≤ C) ∧
    ∀ t ∈ Icc 0 T, ∀ n, HasDerivWithinAt (fun s => a s n)
      (aNonlin L γ δ 1 t (a t) (fun m => (starRingEnd ℂ) (a t m)) (a t) n) (Icc 0 T) t

end WaveTurbulence
