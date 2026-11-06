/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceLadderDecayInput
public import WaveTurbulence.Foundations.Spine.SourceCountingData
/-! Literal downstream finalsbest1/finalsbest2 propositions, with separate gamma-explicit contracts.
Owner ruling: finalsbest1 is the S3 spine input; redladder2 is upstream. finalsbest2 remains
a counting consumer, affected by F69b/F73 for gamma <= 1/2. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Set Finset
open scoped Classical

/-- A selected presentation of each actual maximal ladder; no ladder is replaced by a surrogate. -/
structure SourceMaximalLadderData {w : ℕ} (G : Garden w) where
  length : {S // S ∈ G.molecule.maximalLadders} → ℕ
  upper : (S : {S // S ∈ G.molecule.maximalLadders}) → Fin (length S + 1) → GBranch G.tree
  lower : (S : {S // S ∈ G.molecule.maximalLadders}) → Fin (length S + 1) → GBranch G.tree
  ladder : ∀ S, G.molecule.IsLadder (upper S) (lower S)
  atoms : ∀ S, Molecule.ladderAtoms (upper S) (lower S) = S.1

noncomputable def SourceMaximalLadderData.totalIncoherency {w : ℕ} {G : Garden w}
    (A : SourceMaximalLadderData G) (layer : GBranch G.tree → ℕ) : ℕ :=
  ∑ S, sourceLadderIncoherency G layer (A.upper S) (A.lower S)

/-- Literal source geometry and inherited epsilon/gap support, subpro(1)–(6).
The charge exception set is exactly the fixed root momenta. -/
structure SplicedSourcePremises {R : ℕ} (P : WTParams) (G : Garden (2 * R))
    (D : SplicedKernelData G P.d) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) : Prop where
  molecule : G.molecule.IsMolecule
  connected : G.molecule.IsConnected
  atom_count : G.molecule.atoms.card = G.order
  bond_count : G.molecule.bonds.card + R = 2 * G.order
  subpro : ∃ C : SourceVine.SubproChoices G,
    C.Structural ∧ D.hinges = C.hinges ∧
    ∀ z : GenDecoration G P.d roots 0,
      splicedEpsilon G D.hinges z.1 ≠ 0 → splicedGapIndicator G D P.L P.γ P.η base z.1 ≠ 0 →
      SourceVine.SubproSupport G C P.L P.γ P.η base
        (univ.image (fun i => base + latticePoint P.L (roots i))) (bondIndex G z.1)

/-- TARGET finalsbest1, L2075–L2077, the exact normalized kernel redvine3 (L1976).
Provider: S3 LADDER. redladder2 and simultaneous ladder/time extraction are upstream.
No F69b/F73 counterexample to this coarse estimate is recorded. Gamma remains P.gamma
in the explicit kernel and the original WTPrefix range 0 < gamma < 1. -/
abbrev CoarseSplicedAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ, 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ G : Garden (2 * R), G.IsPlain → G.Irreducible → IsBalancedSig G.sig →
    1 ≤ G.order → G.order ≤ P.N (p + 1) ^ 4 →
  ∀ D : SplicedKernelData G P.d, SplicedAmplitudeBounds G D → (∀ v, D.layer v ≤ p) →
  ∀ (A : SourceMaximalLadderData G) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
    SplicedSourcePremises P G D base roots →
    ‖splicedKernel G D P.L P.γ P.η P.δ base roots‖ ≤
      P.C₂ * (P.C₁ * Real.sqrt P.δ) ^ G.order *
        P.L ^ (-P.η * A.totalIncoherency D.layer +
          80 * P.d * (G.molecule.rho + D.hinges.card))

abbrev CoarseSplicedGate : Prop := WTPrefix CoarseSplicedAt

/-- TARGET finalsbest2, L2078: a distinct downstream counting consumer proposition.
F69b/F73: false on T-bead necklaces for gamma <= 1/2 under the literal source reading.
It is not conjoined as a redundant extra spine input: derive it conditionally from
separate finalcount1 and ladder Fourier inputs plus the proved choice assembly. -/
abbrev FineSplicedAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ, 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ G : Garden (2 * R), G.IsPlain → G.Irreducible → IsBalancedSig G.sig →
    1 ≤ G.order → G.order ≤ P.N (p + 1) ^ 4 →
  ∀ D : SplicedKernelData G P.d, SplicedAmplitudeBounds G D → (∀ v, D.layer v ≤ p) →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
    SplicedSourcePremises P G D base roots →
    ‖splicedKernel G D P.L P.γ P.η P.δ base roots‖ ≤
      P.C₁ * (P.C₁ * P.δ ^ (-10 * P.ν)) ^ G.order *
        P.L ^ (-P.η ^ 6 * (G.molecule.rho + D.hinges.card)) *
          P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 50))

/-- Optional explicit gamma domains for future author-approved range changes; the exact
snapshot-7 target and existing gate definitions are unchanged. -/
abbrev CoarseSplicedOn (Γ : Set ℝ) : Prop := WTPrefix (fun P => P.γ ∈ Γ → CoarseSplicedAt P)
abbrev FineSplicedOn (Γ : Set ℝ) : Prop := WTPrefix (fun P => P.γ ∈ Γ → FineSplicedAt P)
abbrev FinalCountOn (Γ : Set ℝ) : Prop := WTPrefix (fun P => P.γ ∈ Γ → FinalCountAt P)

end WaveTurbulence.LGSpine
