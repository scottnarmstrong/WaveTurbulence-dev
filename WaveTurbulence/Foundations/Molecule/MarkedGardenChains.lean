/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.BlockChains
import Mathlib.Tactic

/-! # Legal block concatenations around a distinguished ingredient
TARGET `defblock` and `blockchainprop`: start at the distinguished block
and adjoin CL ingredients at either endpoint, sharing exactly one joint.
Each constructor records the source operation's block typing. A hyper-block
cannot be extended further, as stipulated in `defblock`; the splicing
assertion concerns a whole block and therefore uses the block constructors.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ}

inductive MarkedGardenChain (G : Garden w) (focus : GardenBlockSegment G) :
    Finset (GBranch G.tree) → GBranch G.tree → GBranch G.tree → Type where
  | base : MarkedGardenChain G focus focus.atoms focus.leftJoint focus.rightJoint
  | append {X : Finset (GBranch G.tree)} {left right : GBranch G.tree}
      (prev : MarkedGardenChain G focus X left right) (A : GardenBlockSegment G)
      (join : A.leftJoint = right) (intersection : X ∩ A.atoms = {right})
      (whole : G.molecule.IsBlock (X ∪ A.atoms) left A.rightJoint)
      (cl : CLParentPattern G A.atoms A.leftJoint A.rightJoint ∨
        CLParentPattern G A.atoms A.rightJoint A.leftJoint) :
      MarkedGardenChain G focus (X ∪ A.atoms) left A.rightJoint
  | prepend {X : Finset (GBranch G.tree)} {left right : GBranch G.tree}
      (prev : MarkedGardenChain G focus X left right) (A : GardenBlockSegment G)
      (join : A.rightJoint = left) (intersection : X ∩ A.atoms = {left})
      (whole : G.molecule.IsBlock (X ∪ A.atoms) A.leftJoint right)
      (cl : CLParentPattern G A.atoms A.leftJoint A.rightJoint ∨
        CLParentPattern G A.atoms A.rightJoint A.leftJoint) :
      MarkedGardenChain G focus (X ∪ A.atoms) A.leftJoint right

namespace MarkedGardenChain
variable {G : Garden w} {focus : GardenBlockSegment G}
variable {X : Finset (GBranch G.tree)} {left right : GBranch G.tree}

/-- The actual groups whose atoms are to be merged by CL splicing. -/
@[expose] def erasedGroups : {X : Finset (GBranch G.tree)} → {left right : GBranch G.tree} →
    MarkedGardenChain G focus X left right → List (Finset (GBranch G.tree))
  | _,_,_,.base => []
  | _,_,_,.append prev A _ _ _ _ => A.atoms :: prev.erasedGroups
  | _,_,_,.prepend prev A _ _ _ _ => A.atoms :: prev.erasedGroups

end MarkedGardenChain
end WaveTurbulence.Mole
