/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceLocalLadder
public import WaveTurbulence.Foundations.Spine.MolecularSpineAt
/-! Literal local ladder decay input from TARGET ladderl1new, L1978–L1992. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Set Finset

/-- TARGET (redladder2), L1986–L1990, with the explicit local kernel of the proposition.
All boundary bonds/times are fixed, and no hinge belongs to the ladder. Provider: S3 LADDER.
The normalization C1 * (C1 delta)^m spells out the source lesssim_1 constant. -/
abbrev LadderDecayAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ, 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ G : Garden (2 * R), G.IsPlain → G.Irreducible → IsBalancedSig G.sig →
    1 ≤ G.order → G.order ≤ P.N (p + 1) ^ 4 →
  ∀ D : SplicedKernelData G P.d, SplicedAmplitudeBounds G D → (∀ v, D.layer v ≤ p) →
  ∀ (m : ℕ) (u v : Fin (m + 1) → GBranch G.tree), 1 ≤ m → G.molecule.IsLadder u v →
    Disjoint (Molecule.ladderAtoms u v) D.hinges →
  ∀ (outside : GBranch G.tree → ℝ), (∀ a, a ∉ Molecule.ladderAtoms u v → outside a ∈ Icc (D.layer a : ℝ) (D.layer a + 1)) →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (boundary : GardenDart G → (Fin P.d → ℤ)),
    ‖sourceLocalLadderKernel G D (Molecule.ladderAtoms u v) outside P.L P.γ P.η P.δ base roots boundary‖ ≤
      P.C₁ * (P.C₁ * P.δ) ^ m *
        P.L ^ (-(P.gamma1 - Real.sqrt P.η) * sourceLadderIncoherency G D.layer u v + 20 * P.d)

abbrev LadderDecayGate : Prop := WTPrefix LadderDecayAt

end WaveTurbulence.LGSpine
