/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceSplicedFourier
public import WaveTurbulence.Foundations.Spine.SourceCountingData
public import WaveTurbulence.Foundations.Spine.AnchorTypes
/-! Literal downstream ladder Fourier input, TARGET ladderl1old L1994–L2001.
The spectral carrier is defined by actual compactly supported garden decorations. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Set Finset
open scoped ENNReal

/-- The dyadic ladder-gap restriction in the proposition's first paragraph. -/
def sourceLadderGapScales {w d : ℕ} (G : Garden w) (P : Finset (GBranch G.tree) → ℝ)
    (L : ℝ) (base : Mom d) (κ : GardenDart G → (Fin d → ℤ)) : Prop :=
  ∀ S ∈ G.molecule.maximalLadders,
    (P S = 0 ∨ (SourceVine.IsDyadicScale (P S) ∧ L⁻¹ ≤ P S ∧ P S ≤ 1)) ∧
    ∃ m : ℕ, ∃ u v : Fin (m + 1) → GBranch G.tree, ∃ hm : 1 ≤ m,
      G.molecule.IsLadder u v ∧ Molecule.ladderAtoms u v = S ∧
      ∃ r, G.molecule.IsLadderGap L base κ u v hm r ∧
        (P S = 0 → r = 0) ∧
        (0 < P S → P S < 1 → P S / 2 ≤ ‖r‖ ∧ ‖r‖ ≤ 2 * P S) ∧
        (P S = 1 → 1 ≤ ‖r‖)

/-- Exactly the alpha values that may occur for a decoration under the source restrictions. -/
def splicedFrequencySpectrum {w d : ℕ} (G : Garden w) (D : SplicedKernelData G d)
    (P : Finset (GBranch G.tree) → ℝ) (L γ η δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) : Set (GBranch G.tree → ℝ) :=
  {α | ∃ z : GenDecoration G d roots 0,
    splicedEpsilon G D.hinges z.1 ≠ 0 ∧ splicedGapIndicator G D L γ η base z.1 ≠ 0 ∧
    (∀ x ∈ G.molecule.bonds, ‖base + latticePoint L (bondIndex G z.1 x) - D.center x‖ ≤ 1) ∧
    sourceLadderGapScales G P L base (bondIndex G z.1) ∧
    α = splicedFrequency G D L γ δ base z.1}

/-- Integer frequency boxes are included only when an actual allowed alpha realizes them. -/
def sourceFrequencyBoxes {w : ℕ} (G : Garden w) (A : Set (GBranch G.tree → ℝ)) :
    Set (GBranch G.tree → ℤ) := {σ | ∃ α ∈ A, ∀ v, ⌊α v⌋ = σ v}

noncomputable def splicedFourierBoxSum {w : ℕ} (G : Garden w)
    (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ) (A : Set (GBranch G.tree → ℝ)) : ℝ≥0∞ :=
  ∑' σ : sourceFrequencyBoxes G A,
    ⨆ (α : GBranch G.tree → ℝ) (_ : α ∈ A) (_ : ∀ v, |α v - σ.1 v| ≤ 1),
      ‖splicedFourierB G layer rootTime α‖ₑ

/-- TARGET ladderl1old / (ladderl1), L1994–L2001. B is the literal time integral,
not arbitrary data. Its alpha and sigma ranges retain the explicit may-occur restriction.
Provider: S3 LADDER; B1.6 sumint, DH21 Lemma 10.2 and DH19 Prop 2.3 are upstream. -/
abbrev LadderFourierGate : Prop := WTPrefix fun P =>
  ∀ p : ℕ, p < P.D → ∀ R : ℕ, 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ G : Garden (2 * R), G.IsPlain → G.Irreducible → IsBalancedSig G.sig →
    1 ≤ G.order → G.order ≤ P.N (p + 1) ^ 4 →
  ∀ (D : SplicedKernelData G P.d) (scales : Finset (GBranch G.tree) → ℝ),
    (∀ v, D.layer v ≤ p) → SplicedAmplitudeBounds G D →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
    splicedFourierBoxSum G D.layer D.rootTime
      (splicedFrequencySpectrum G D scales P.L P.γ P.η P.δ base roots) ≤
    ENNReal.ofReal (P.C₁ * (P.C₁ * P.δ ^ (-1 / 2 - 5 * P.ν)) ^ G.order *
      P.L ^ (P.δ ^ (5 * P.ν) * G.molecule.rho) *
      ∏ S ∈ G.molecule.maximalLadders,
        Molecule.ladderWeight P.L P.γ P.δ (scales S) ^ Molecule.ladderLength S)

end WaveTurbulence.LGSpine
