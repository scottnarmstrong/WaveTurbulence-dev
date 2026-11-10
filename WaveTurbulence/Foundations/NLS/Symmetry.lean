/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NLS.UniformDecay

/-!
# Gauge and space-translation symmetry of (NLS) and of the solvability event

TARGET (gaugeinv), L567–L570, uses gauge invariance `u ↦ e^{iθ}u` and space translation invariance
`u ↦ u(· - x₀)` of (NLS) and of the event that (NLS) has a smooth solution. With
`smoothDataSet L α T = {c : ∃ u, IsSmoothNLSSolution L α T c u}`:

* `IsSmoothNLSSolution.gauge`, `IsSmoothNLSSolution.translate`: the solution map commutes with the
  symmetries; on the data, `c ↦ e^{iθ} c` and `cₙ ↦ e^{-2πi⟨n/L, x₀⟩} cₙ`
  (`= torusChar L n (-x₀) * cₙ`);
* `mem_smoothDataSet_gauge_iff`, `mem_smoothDataSet_translate_iff`: `smoothDataSet` is invariant;
* `solvableEvent_eq_preimage`, `solvableEvent_gauge`, `solvableEvent_translate`: `solvableEvent` is
  the preimage of `smoothDataSet` under the data map, and is unchanged when the random coefficients
  `g` are rotated or modulated (the "gauge or space translation symmetry" of L569, in the form
  `IsSymmetricEvent` of the Wave B proposal §2.3.4);
* `reducedCoeff_gauge`, `reducedCoeff_translate`: the transformation laws of the reduced
  coefficients `a_k(t)` of (reducedcoef).
-/

public section

noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped ContDiff

namespace WaveTurbulence.NLS

variable {d : ℕ}

/-- The data `c` for which (NLS) has a smooth solution on `[0, T]`. -/
@[expose] def smoothDataSet (L α T : ℝ) : Set ((Fin d → ℤ) → ℂ) :=
  {c | ∃ u, IsSmoothNLSSolution L α T c u}

/-! ### Calculus lemmas -/

/-! ### The symmetries of (NLS) -/

section Solutions

variable {L α T : ℝ} {c : (Fin d → ℤ) → ℂ} {u : ℝ → (Fin d → ℝ) → ℂ}

end Solutions

/-! ### The solvability event -/

section Event

variable {Ω : Type*} {L α T : ℝ} {φin : Mom d → ℝ} {g : (Fin d → ℤ) → Ω → ℂ}

end Event

/-! ### The reduced coefficients -/

end WaveTurbulence.NLS
