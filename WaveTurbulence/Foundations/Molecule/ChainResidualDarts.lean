/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MarkedGardenChains
public import WaveTurbulence.Foundations.Molecule.MoleculeSingleDeficit
public import WaveTurbulence.Foundations.Molecule.MoleculeJointSymmetry
import Mathlib.Tactic

/-! # All and only the distinguished ingredient's bonds survive chain splicing -/

public section
namespace WaveTurbulence.Mole
open TTree Finset
namespace MarkedGardenChain
variable {w : ℕ} {G : Garden w} {focus : GardenBlockSegment G}
variable {X : Finset (GBranch G.tree)} {left right : GBranch G.tree}

/-- Literal residual-dart condition for simultaneous molecular splicing. -/
@[expose] def ResidualDartCondition (C : MarkedGardenChain G focus X left right) (x : GardenDart G) : Prop :=
  G.molecule.InGroup X x ∧ ∀ S ∈ C.erasedGroups, ¬ G.molecule.InGroup S x

end MarkedGardenChain
end WaveTurbulence.Mole
