/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.IsASolution
public import WaveTurbulence.Frozen.Defs.IsSmoothNLSSolution
public import WaveTurbulence.Frozen.Defs.Jbr
public import WaveTurbulence.Frozen.Defs.KineticTime
public import WaveTurbulence.Frozen.Defs.LatticePoint
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.TorusFourierCoeff
public import WaveTurbulence.Frozen.Defs.ZNormOn
public import WaveTurbulence.Foundations.NLS.AkBridge

/-!
# Provider for `WaveTurbulence.nlsAkBridge`

The proof of the frozen anchor `WaveTurbulence.nlsAkBridge` (ruling D7), exported as
`WaveTurbulence.Provider.nlsAkBridge`, with the anchor's data binders implicit and its hypotheses
`autoParam`s, so the anchor seals with the bare `by exact` the checker requires (as for `wkelwp`). This module
must not import the frozen anchor.
-/

public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
universe u

namespace WaveTurbulence.Provider

/-- **B1.4 `nlsAkBridge`** (T L540–L566, L817–L819; F8). For `L > 0`, `α = L^{-γ}`, `δ > 0`,
`T = 𝔇 δ T_kin(α)`: (1) a smooth NLS solution with data `c` gives, through (reducedcoef), a classed
solution of the `a`-system on `[0, 𝔇]` with `|a_n(t)| = |û(δT_kin t, n)|`, in every `Z^Λ([0,𝔇])`;
(2) conversely, a classed `a`-system solution with rapidly decreasing data gives a smooth NLS
solution with `|û(t, n)| = |a_n(t/(δT_kin))|`; (3) smooth solutions are unique; (4) the solvable
event is measurable and so are the truncated observables at times `t ∈ [0, T]` (a smooth solution is
constrained only on `[0, T]`; for all `t ∈ ℝ` the item was false, stage-3 R3). Deviations (WAVE-B v2
§4.4): (D1) item 4 is the precise form of F8's measurability; (D2) rapidly decreasing data in item 2.
(D3, delta-stage-3 N1) `1 ≤ 𝔇`: at `𝔇 = 0` the `a`-system on `[0,0]` is void (a derivative within a
singleton is arbitrary) while a smooth solution on `[0,0]` must be stationary, so item (2) is false
there; every consumer has `1 ≤ 𝔇` from the prefix. The classed `a`-system solution is
`IsASolution`. The phase
conventions (`e^{-πiδL^{2γ}|k|²t}`, `e^{-2iαMδT_kin t}`) follow (reducedcoef) with the normalized
Laplacian of Wave A; to be checked by the NLS packet. -/
theorem nlsAkBridge {d : ℕ} (hd : 1 ≤ d := by assumption) {L γ δ : ℝ} (hL : 0 < L := by assumption)
    (hδ : 0 < δ := by assumption) {D : ℕ} (hD : 1 ≤ D := by assumption) {α T : ℝ}
    (hα : α = L ^ (-γ) := by assumption) (hT : T = D * δ * kineticTime α := by assumption) :
    -- (1) forward
    (∀ (c : (Fin d → ℤ) → ℂ) (u : ℝ → (Fin d → ℝ) → ℂ), IsSmoothNLSSolution L α T c u →
      let M : ℝ := (L ^ d)⁻¹ * ∑' n, ‖c n‖ ^ 2
      let a : ℝ → (Fin d → ℤ) → ℂ := fun t n =>
        Complex.exp (-(Real.pi * δ * L ^ (2 * γ) * ‖latticePoint L n‖ ^ 2 * t : ℝ) *
          Complex.I) *
        Complex.exp (-(2 * α * M * δ * kineticTime α * t : ℝ) * Complex.I) *
        torusFourierCoeff L (u (δ * kineticTime α * t)) n
      IsASolution L γ δ D c a ∧ (∀ Λ : ℝ, ZNormOn L Λ (Icc 0 D) a < ⊤) ∧
        ∀ t ∈ Icc (0 : ℝ) D, ∀ n,
          ‖a t n‖ = ‖torusFourierCoeff L (u (δ * kineticTime α * t)) n‖) ∧
    -- (2) backward
    (∀ (c : (Fin d → ℤ) → ℂ) (a : ℝ → (Fin d → ℤ) → ℂ),
      (∀ s : ℝ, ∃ C, ∀ n, jbr (latticePoint L n) ^ s * ‖c n‖ ≤ C) →
      IsASolution L γ δ D c a →
      ∃ u : ℝ → (Fin d → ℝ) → ℂ, IsSmoothNLSSolution L α T c u ∧
        ∀ t ∈ Icc 0 T, ∀ n, ‖torusFourierCoeff L (u t) n‖ = ‖a (t / (δ * kineticTime α)) n‖) ∧
    -- (3) uniqueness
    (∀ (c : (Fin d → ℤ) → ℂ) (u u' : ℝ → (Fin d → ℝ) → ℂ),
      IsSmoothNLSSolution L α T c u → IsSmoothNLSSolution L α T c u' → ∀ t ∈ Icc 0 T, u t = u' t) ∧
    -- (4) measurability
    (∀ (Ω : Type u) [MeasurableSpace Ω] (c : Ω → (Fin d → ℤ) → ℂ), Measurable c →
      MeasurableSet {ω | ∃ v, IsSmoothNLSSolution L α T (c ω) v} ∧
      ∀ U : Ω → ℝ → (Fin d → ℝ) → ℂ,
        (∀ ω, (∃ v, IsSmoothNLSSolution L α T (c ω) v) → IsSmoothNLSSolution L α T (c ω) (U ω)) →
        ∀ t ∈ Icc 0 T, ∀ n, Measurable fun ω =>
          {ω | ∃ v, IsSmoothNLSSolution L α T (c ω) v}.indicator
            (fun ω => ‖torusFourierCoeff L (U ω t) n‖ ^ 2) ω) :=
  NLSBridge.nlsAkBridge hd L γ δ hL hδ D hD α T hα hT

end WaveTurbulence.Provider
