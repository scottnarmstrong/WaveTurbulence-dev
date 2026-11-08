/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.LadderL1Gate

/-! # C3 LAD-FILT: definitions

`filterB` (the `𝔟`-norm of a filter profile, o83 §2.1) and the target `LadderL1AtFilt` (S-MARKED §2.6), copied by
source from the S-MARKED probe (see `COPIED-SHA256SUMS`). -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.LadFilt

open scoped FourierTransform in
/-- The `𝔟`-norm of a filter profile (o83 §2.1): `∫ (1+|ξ|)² |ψ̂(ξ)| dξ`. -/
noncomputable def filterB (ψ : ℝ → ℂ) : ℝ :=
  ∫ ξ : ℝ, (1 + |ξ|) ^ 2 * ‖𝓕 ψ ξ‖

/-- **LadderL1AtFilt**: main's `LadderDecay.LadderL1At` with Schwartz resonance filters `ψ a (Ω_a / Rv a)` at the ladder atoms;
extra factor `∏ max 1 (𝔟 ψ_a)`. Frontier cutoffs on ladder bonds need no new gate: they are edge amplitudes
(normalized by `c_χ²`). -/
def LadderL1AtFilt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ, 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ G : Garden (2 * R), G.IsPlain → G.Irreducible → IsBalancedSig G.sig →
    1 ≤ G.order → G.order ≤ P.N (p + 1) ^ 4 →
  ∀ D : SplicedKernelData G P.d, SplicedAmplitudeBounds G D → (∀ v, D.layer v ≤ p) →
  ∀ (m : ℕ) (u v : Fin (m + 1) → GBranch G.tree), 1 ≤ m → G.molecule.IsLadder u v →
    Disjoint (Molecule.ladderAtoms u v) D.hinges →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
  ∀ (boundary : GardenDart G → (Fin P.d → ℤ))
    (T0 : Finset ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary))
    (ψ : GBranch G.tree → SchwartzMap ℝ ℂ) (Rv : GBranch G.tree → ℝ), (∀ a, 1 ≤ Rv a) →
    (∀ z, z ∉ T0 → LadderDecay.ladderWeight D (Molecule.ladderAtoms u v) P.L P.γ P.η base z.1.1 = 0) →
    ‖(coupling P.d P.L P.γ P.δ : ℂ)‖ ^ ((Molecule.ladderAtoms u v).card - 1) *
      ∫ t in LadderDecay.timeBox G D.layer (Molecule.ladderAtoms u v),
        ‖∑ z ∈ T0, (∏ a ∈ Molecule.ladderAtoms u v,
            ψ a (omegaNode G (cosetDecoration G P.L base z.1.1) a / Rv a)) *
          LadderDecay.ladderWeight D (Molecule.ladderAtoms u v) P.L P.γ P.η base z.1.1 *
          LadderDecay.ladderPhase D (Molecule.ladderAtoms u v) P.L P.γ P.δ base z.1.1 t‖ ≤
      (∏ a ∈ Molecule.ladderAtoms u v, max 1 (filterB ⇑(ψ a))) * P.C₁ * (P.C₁ * P.δ) ^ m *
        P.L ^ (-(P.gamma1 - Real.sqrt P.η) * sourceLadderIncoherency G D.layer u v + 20 * P.d)

end WaveTurbulence.Flower.LadFilt
