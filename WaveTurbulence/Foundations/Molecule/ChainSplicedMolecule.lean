/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MergeQuotients
public import WaveTurbulence.Foundations.Molecule.ChainResidualDarts
public import WaveTurbulence.Foundations.Molecule.DirectedMoleculeIso
public import WaveTurbulence.Foundations.Molecule.MoleculeGroups
public import Mathlib.Data.Fintype.Quotient
import Mathlib.Tactic

/-! # Actual molecular splicing of all CL ingredients around a CN block
TARGET `blockchainprop`: vertices are the quotient by the CL atom
identifications; darts are precisely old whole-block darts not internal
to a CL ingredient. The resulting directed molecule is proved isomorphic
to the distinguished ingredient, with its internal bonds unchanged.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
namespace MarkedGardenChain
variable {w : ℕ} {G : Garden w} {focus : GardenBlockSegment G}
variable {X : Finset (GBranch G.tree)} {left right : GBranch G.tree}

abbrev SplicedAtom (C : MarkedGardenChain G focus X left right) := MergeQuotient X C.erasedGroups
abbrev SplicedDart (C : MarkedGardenChain G focus X left right) :=
  {x : GardenDart G // C.ResidualDartCondition x}

noncomputable instance splicedAtomFintype (C : MarkedGardenChain G focus X left right) :
    Fintype C.SplicedAtom := Fintype.ofFinite _

noncomputable instance splicedDartFintype (C : MarkedGardenChain G focus X left right) :
    Fintype C.SplicedDart := Fintype.ofFinite _

end MarkedGardenChain
end WaveTurbulence.Mole
