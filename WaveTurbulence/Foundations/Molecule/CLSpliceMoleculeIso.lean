/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.CLIncidenceParents
public import WaveTurbulence.Foundations.Molecule.CLDartStructure
public import WaveTurbulence.Foundations.Molecule.GardenRootEncoding
import Mathlib.Tactic

/-! # TARGET block_clcn: the actual spliced molecule is the contraction
The equivalence retains literal outside atom names, removes exactly the
internal old bonds, and commutes with atoms, mates and orientations.
-/

public section
namespace WaveTurbulence.Mole
open TTree
variable {w : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable (hB : G.molecule.IsBlock S a b) (hCL : CLParentPattern G S a b) (D : CLSpliceSlots G S a b)

theorem clSplicedDartEquiv_atom (x : GardenDart (clSplicedGardenOfSlots hB hCL D)) :
    (contractGroup G.molecule S).atom (clSplicedDartEquiv hB hCL D x) =
      (clSplicedBranchAtomEquiv hB hCL D ((clSplicedGardenOfSlots hB hCL D).molecule.atom x)).1 := by
  rcases x with ⟨c,side⟩ | l
  · cases side
    · exact clSplicedBranchName_contract hB hCL D c.1
    · exact cl_branch_name_parent_contract hB hCL D c.1 c.2 (clPCChildEquiv hB hCL D c).1.2
  · exact cl_leaf_name_parent_contract hB hCL D l.1 l.2.2.1 (clLPLeafEquiv hB hCL D l).1.2.2.1

/-- TARGET `block_clcn` (2): the constructed garden's actual molecule is
isomorphic to the old molecule with every block atom merged and every
internal block bond removed. Both atom and half-edge maps are bijections. -/
@[expose] noncomputable def clSpliceMoleculeIsoOfSlots :
    GardenMoleculeIso (clSplicedGardenOfSlots hB hCL D) (contractGroup G.molecule S) where
  branches := clSplicedBranchAtomEquiv hB hCL D
  darts := clSplicedDartEquiv hB hCL D
  atom_comm := clSplicedDartEquiv_atom hB hCL D
  mate_comm := clSplicedDartEquiv_mate hB hCL D
  out_comm := clSplicedDartEquiv_out hB hCL D

/-- No slot or pairing hypothesis is added to the source result: the
canonical slot choices and every commutation law are derived from the CL block. -/
@[expose] noncomputable def clSpliceMoleculeIso :
    GardenMoleculeIso (clSplicedGarden hB hCL) (contractGroup G.molecule S) :=
  clSpliceMoleculeIsoOfSlots hB hCL (clSpliceSlotsOfBlock hB hCL)

end WaveTurbulence.Mole
