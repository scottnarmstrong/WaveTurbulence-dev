/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.GardenMoleculeDefs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

/-! # Trees with one or three children in TARGET `cnblock`
Unary vertices are retained CN joints. Leaves are actual path addresses,
and their cardinality remains odd under both allowed branching operations.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset

/-- The generalized rooted trees used after removing CN blocks. -/
inductive GeneralizedTree where
  | leaf
  | unary (child : GeneralizedTree)
  | ternary (left middle right : GeneralizedTree)
  deriving DecidableEq

namespace GeneralizedTree

end GeneralizedTree
end WaveTurbulence.Mole
