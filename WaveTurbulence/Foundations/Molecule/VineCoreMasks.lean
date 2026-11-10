/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineTemplates

/-! # Finite masks of the pinned vine cores (TARGET subsetvc) -/

public section
namespace WaveTurbulence.Vine

/-- The finite mask vector on the template atom range. -/
@[expose] def coreMaskVector (X : VineType) (mask : ℕ → ℕ) : List ℕ :=
  (List.range X.template.n).map mask

/-- All degree masks in each of the eight finite cores. This table includes
degree-shaped groups that are not vine-like; no such identification is assumed. -/
inductive CoreKind | block | hyper deriving DecidableEq

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
