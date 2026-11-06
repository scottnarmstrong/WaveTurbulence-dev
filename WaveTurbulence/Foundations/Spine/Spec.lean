/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LadderL1Gate
public import WaveTurbulence.Foundations.Spine.SourceLadderGeometry
public import WaveTurbulence.Foundations.Spine.SourceSubproObjects
/-! # Verbatim copies of the pinned coarse spliced statement (S3c)

`SourceSplicedBounds.lean` (pinned, sha256 38b56114...) cannot be imported into the same environment
as the S3b ladder scratch (its import chain contains lg-spine's `WaveBDraft.Sumint`, which clashes with
the sumint scratch `WaveBDraft.SumintData` used by `LadderDecay`).  The definitions are therefore copied
here with the suffix `C` and bodies identical to the pinned text. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.CoarseSpliced
open WaveTurbulence WaveTurbulence.LGSpine Set Finset
open scoped Classical

/-- A selected presentation of each actual maximal ladder; no ladder is replaced by a surrogate. -/
structure SourceMaximalLadderDataC {w : ℕ} (G : Garden w) where
  length : {S // S ∈ G.molecule.maximalLadders} → ℕ
  upper : (S : {S // S ∈ G.molecule.maximalLadders}) → Fin (length S + 1) → GBranch G.tree
  lower : (S : {S // S ∈ G.molecule.maximalLadders}) → Fin (length S + 1) → GBranch G.tree
  ladder : ∀ S, G.molecule.IsLadder (upper S) (lower S)
  atoms : ∀ S, Molecule.ladderAtoms (upper S) (lower S) = S.1

noncomputable def SourceMaximalLadderDataC.totalIncoherency {w : ℕ} {G : Garden w}
    (A : SourceMaximalLadderDataC G) (layer : GBranch G.tree → ℕ) : ℕ :=
  ∑ S, sourceLadderIncoherency G layer (A.upper S) (A.lower S)

structure SplicedSourcePremisesC {R : ℕ} (P : WTParams) (G : Garden (2 * R))
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

abbrev CoarseSplicedAtC (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ, 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ G : Garden (2 * R), G.IsPlain → G.Irreducible → IsBalancedSig G.sig →
    1 ≤ G.order → G.order ≤ P.N (p + 1) ^ 4 →
  ∀ D : SplicedKernelData G P.d, SplicedAmplitudeBounds G D → (∀ v, D.layer v ≤ p) →
  ∀ (A : SourceMaximalLadderDataC G) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
    SplicedSourcePremisesC P G D base roots →
    ‖splicedKernel G D P.L P.γ P.η P.δ base roots‖ ≤
      P.C₂ * (P.C₁ * Real.sqrt P.δ) ^ G.order *
        P.L ^ (-P.η * A.totalIncoherency D.layer +
          80 * P.d * (G.molecule.rho + D.hinges.card))

/-- A family of pairwise disjoint hinge-free ladders. -/
structure SelData {w : ℕ} (G : Garden w) (hinges : Finset (GBranch G.tree)) where
  ι : Type
  [fin : Fintype ι]
  [deq : DecidableEq ι]
  m : ι → ℕ
  u : (i : ι) → Fin (m i + 1) → GBranch G.tree
  v : (i : ι) → Fin (m i + 1) → GBranch G.tree
  ladder : ∀ i, G.molecule.IsLadder (u i) (v i)
  disj : ∀ i j, i ≠ j →
    Disjoint (Molecule.ladderAtoms (u i) (v i)) (Molecule.ladderAtoms (u j) (v j))
  hing : ∀ i, Disjoint (Molecule.ladderAtoms (u i) (v i)) hinges

attribute [instance] SelData.fin SelData.deq

/-- **The ladder selection claim** (pure molecule combinatorics): from the maximal ladders one can
select pairwise disjoint hinge-free ladders carrying a fixed fraction of the incoherency and
covering all but boundedly many atoms. -/
def SelectionClaim : Prop :=
  ∀ {R : ℕ} (G : Garden (2 * R)) (layer : GBranch G.tree → ℕ) (hinges : Finset (GBranch G.tree)),
    G.molecule.IsMolecule → G.molecule.IsConnected → G.molecule.atoms.card = G.order →
    ∀ (A : SourceMaximalLadderDataC G),
    ∃ F : SelData G hinges,
      A.totalIncoherency layer ≤
          4 * ∑ i, sourceLadderIncoherency G layer (F.u i) (F.v i) +
            20 * (G.molecule.rho + hinges.card) ∧
      Fintype.card F.ι ≤ 2 * (G.molecule.rho + hinges.card) ∧
      G.order - ∑ i, (2 * F.m i + 2) + Fintype.card F.ι ≤ 8 * (G.molecule.rho + hinges.card)

end WaveTurbulence.CoarseSpliced
