/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineTemplates

/-! # Finite masks of the pinned vine cores (TARGET subsetvc) -/

public section
namespace WaveTurbulence.Vine

/-- Degree at v within a selected subset, represented by its 0/1 mask. -/
@[expose] def coreDegree (X : VineType) (mask : ℕ → ℕ) (v : ℕ) : ℕ :=
  (X.template.bonds.map (fun e => if e.1=v then mask e.2 else 0)).sum +
    (X.template.bonds.map (fun e => if e.2=v then mask e.1 else 0)).sum

/-- The finite mask vector on the template atom range. -/
@[expose] def coreMaskVector (X : VineType) (mask : ℕ → ℕ) : List ℕ :=
  (List.range X.template.n).map mask

/-- The exact degree conditions of a block (t=2) or hyper-block (t=3),
with the joints put in increasing order. -/
@[expose] def CoreMaskShape (X : VineType) (t : ℕ) (mask : ℕ → ℕ) (a b : ℕ) : Prop :=
  a<b ∧ b<X.template.n ∧ mask a=1 ∧ mask b=1 ∧
    (∀ i<X.template.n,mask i≤1) ∧
    ∀ i<X.template.n,mask i=1 → coreDegree X mask i=if i=a ∨ i=b then t else 4

/-- All degree masks in each of the eight finite cores. This table includes
degree-shaped groups that are not vine-like; no such identification is assumed. -/
inductive CoreKind | block | hyper deriving DecidableEq

/-- Joint degree of the selected block kind. -/
@[expose] def CoreKind.jointDegree : CoreKind → ℕ
  | .block => 2
  | .hyper => 3

/-- Exhaustive finite-core mask table for the two block kinds. -/
@[expose] def coreMaskCandidates : VineType → CoreKind → List (List ℕ)
  | .I, .block => [[1,1]]
  | .I, .hyper => []
  | .II, .block => [[0,0,1,1],[1,1,1,1]]
  | .II, .hyper => []
  | .III, .block => [[0,0,1,1,0,0,0,0,0],[0,0,0,0,0,1,1,0,0],[0,0,0,0,0,0,0,1,1],[1,1,1,1,1,1,1,1,1]]
  | .III, .hyper => []
  | .IV, .block => [[0,0,1,1,0,0,0,0,0],[0,0,0,0,1,1,0,0,0],[0,0,0,0,0,1,1,0,0],[0,0,0,0,1,1,1,0,0],[0,0,0,0,0,0,0,1,1],[1,1,1,1,1,1,1,1,1]]
  | .IV, .hyper => []
  | .V, .block => [[0,0,1,1,0,0,0,0,0],[0,0,0,0,1,1,0,0,0],[0,0,0,0,0,0,1,0,1],[0,0,0,0,0,0,0,1,1],[1,1,1,1,1,1,1,1,1]]
  | .V, .hyper => [[0,0,0,0,0,0,1,1,1],[0,0,0,0,1,1,1,1,1],[0,0,1,1,1,1,1,1,1]]
  | .VI, .block => [[0,0,1,1,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,1,1,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,1,1,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,1,1,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,1,0,1,0,0],[0,0,0,0,0,0,0,0,0,0,0,1,1,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,1,1],[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]]
  | .VI, .hyper => [[0,0,0,0,0,0,0,0,0,0,1,1,1,0,0],[0,0,0,0,0,0,0,0,1,1,1,1,1,0,0]]
  | .VII, .block => [[0,0,1,1,0,0,0,0,0,0,0],[0,0,0,0,1,1,0,0,0,0,0],[0,0,0,0,1,0,1,0,0,0,0],[0,0,0,0,1,1,1,1,1,0,0],[0,0,0,0,0,0,0,0,0,1,1],[1,1,1,1,1,1,1,1,1,1,1]]
  | .VII, .hyper => [[0,0,0,0,1,1,1,0,0,0,0]]
  | .VIII, .block => [[0,0,1,1,0,0,0,0,0,0,0],[0,0,0,0,1,1,0,0,0,0,0],[0,0,0,0,0,0,1,1,0,0,0],[0,0,0,0,0,0,0,0,1,0,1],[0,0,0,0,0,0,0,0,0,1,1],[1,1,1,1,1,1,1,1,1,1,1]]
  | .VIII, .hyper => [[0,0,0,0,0,0,0,0,1,1,1],[0,0,0,0,0,0,1,1,1,1,1]]

end WaveTurbulence.Vine
