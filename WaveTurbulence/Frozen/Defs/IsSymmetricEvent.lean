/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.InitialCoeff
public import WaveTurbulence.Frozen.Defs.LatticePoint
public import WaveTurbulence.Frozen.Defs.Mom

/-!
# IsSymmetricEvent

Wave B tier B1 (WaveB1-System.lean), source: T L567–L569; WAVE-B §2.3.4. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

/-- **Gauge and space-translation symmetric events** (T L567–L569): `F` is the set of `ω` whose
initial data `(û_in(k))_k = (√φin(k) g_k(ω))_k` lie in a measurable set `A` of coefficient arrays that
is invariant under `c ↦ e^{iθ} c` (gauge) and `c ↦ (e^{-2πi⟨k,x₀⟩} c_k)_k` (translation
`u ↦ u(· - x₀)`). (WAVE-B §2.3.4 uses the preimage under `g` instead of the initial data; TARGET
says "any event can be interpreted as a subset of initial data". See DESIGN Q5.) -/
def IsSymmetricEvent {d : ℕ} {Ω : Type*} (L : ℝ) (φin : Mom d → ℝ)
    (g : (Fin d → ℤ) → Ω → ℂ) (F : Set Ω) : Prop :=
  ∃ A : Set ((Fin d → ℤ) → ℂ), MeasurableSet A ∧ F = initialCoeff L φin g ⁻¹' A ∧
    (∀ θ : ℝ, ∀ c ∈ A, (fun n => Complex.exp ((θ : ℂ) * Complex.I) * c n) ∈ A) ∧
    ∀ x₀ : Mom d, ∀ c ∈ A, (fun n => Complex.exp
      (-(2 * Real.pi * inner ℝ (latticePoint L n) x₀ : ℝ) * Complex.I) * c n) ∈ A

end WaveTurbulence
