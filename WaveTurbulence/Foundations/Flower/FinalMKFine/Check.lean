/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKFine.Bridge
import Mathlib.Tactic

/-! # C4b FINE-PIN: exact-type checks of the export

The body below is the statement text of `FineSplicedAtMK` in `FinalMKDefs/Fine.lean` (copied by source from the
probe `FinalMKProbe.lean`, sha256 `49bf9d1e…6025`), under `WTPrefix fun P => 1 / 2 < P.γ → …` (the definition of
`FineSplicedGateHalfMK`), with ruling R187's hypothesis `(∀ b, (D.lb b).isSome → b ∈ E)`. -/

@[expose] public section
set_option autoImplicit false

open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs

/-- The C4b deliverable by name. -/
example : FineSplicedGateHalfMK := fineSplicedGateHalfMK

/-- The C4b deliverable, statement text of the probe. -/
example : WTPrefix fun (P : WTParams) => 1 / 2 < P.γ →
    ∀ p : ℕ, p < P.D → ∀ R : ℕ, 1 ≤ R → R ≤ 10 * P.R (p + 1) →
    ∀ G : Garden (2 * R), G.IsPlain → G.Irreducible → IsBalancedSig G.sig →
      1 ≤ G.order → G.order ≤ P.N (p + 1) ^ 4 →
    ∀ (D : SplicedKernelDataMK G P.d) (Cs : SubproChoices G) (S : SurvivorData G) (E : Finset (GBranch G.tree)),
      SplicedAmplitudeBounds G D.toSplicedKernelData → (∀ v, D.layer v ≤ p) →
      (∀ a q, D.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) → (∀ k, 0 ≤ D.ind k ∧ D.ind k ≤ 1) →
      (∀ b, (D.fix b).isSome → b ∈ E) → (∀ b t, D.fix b = some t → (D.layer b : ℝ) ≤ t ∧ t ≤ D.layer b + 1) →
      (∀ b, (D.lb b).isSome → b ∈ E) →
    ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
      SplicedGeomPremises G → SubproConclusionsMK G D.toSplicedKernelData Cs S P.L P.γ P.η base roots →
      ‖splicedKernelMK G D P.L P.γ P.η P.δ base roots‖ ≤
        P.C₁ * (P.C₁ * P.δ ^ (-10 * P.ν)) ^ G.order * P.L ^ (2 * (S.m : ℝ)) *
          (((G.order : ℝ) + 1) * P.L) ^ ((5 * P.d + 4) * E.card) *
          P.L ^ (-P.η ^ 6 * (G.molecule.rho + D.hinges.card)) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 50)) :=
  fineSplicedGateHalfMK

end WaveTurbulence.Flower.FinalMKFine
