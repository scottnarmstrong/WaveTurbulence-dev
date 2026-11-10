/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceCountingObjects
/-! R6(a): one canonical designation per atom set of the second collection.

READING (source ambiguity, not an erratum): in TARGET an HV/HVC vine-like object is an atomic
group, so it has one designation. The Lean `Object` keeps the deleted bond, so two different
deleted bonds of one atom set are two objects. The selection of the collection is assembly
(RULINGS R3/R6(a)); we select, among the members of the collection with one hyper atom set, the one
whose deleted bond (up to mates) is least for a fixed injective rank `rk` on darts. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open SourceVine Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Rank of the deleted bond of a hyper object (the least rank of the two darts of the bond);
`0` for an ordinary object (unused). -/
def SourceVine.Object.hyperRank {M : Molecule V D} (rk : D → ℕ) (P : Object M) : ℕ :=
  match P.shape with
  | .vc _ => 0
  | .hyper R => min (rk R.added) (rk (M.mate R.added))

/-- The canonical part of a collection: among members with the same hyper atom set, only those
of least deleted-bond rank. -/
def canonicalSub {M : Molecule V D} (rk : D → ℕ) (K : Set (Object M)) : Set (Object M) :=
  {P | P ∈ K ∧ ∀ Q ∈ K, Q.atoms = P.atoms → (∃ R, P.shape = .hyper R) →
    (∃ R, Q.shape = .hyper R) → P.hyperRank rk ≤ Q.hyperRank rk}

end WaveTurbulence.LGSpine
