/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceSplicedBounds
public import WaveTurbulence.Foundations.Spine.LadderL1Gate
public import WaveTurbulence.Foundations.Spine.SourceLadderGeometry
public import WaveTurbulence.Foundations.Spine.SourceSubproObjects
/-! Canonical coarse-spliced carriers and the ladder selection claim. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.CoarseSpliced
open WaveTurbulence WaveTurbulence.LGSpine Set Finset
open scoped Classical

abbrev SourceMaximalLadderDataC {w : ℕ} (G : Garden w) :=
  LGSpine.SourceMaximalLadderData G

noncomputable abbrev SourceMaximalLadderDataC.totalIncoherency {w : ℕ} {G : Garden w}
    (A : SourceMaximalLadderDataC G) (layer : GBranch G.tree → ℕ) : ℕ :=
  LGSpine.SourceMaximalLadderData.totalIncoherency A layer

abbrev SplicedSourcePremisesC {R : ℕ} (P : WTParams) (G : Garden (2 * R))
    (D : SplicedKernelData G P.d) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) : Prop :=
  LGSpine.SplicedSourcePremises P G D base roots

abbrev CoarseSplicedAtC (P : WTParams) : Prop := LGSpine.CoarseSplicedAt P

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
