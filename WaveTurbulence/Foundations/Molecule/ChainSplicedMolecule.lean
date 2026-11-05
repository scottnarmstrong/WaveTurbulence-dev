/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.ChainAtomQuotient
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

theorem splicedDart_mate (C : MarkedGardenChain G focus X left right) (x : C.SplicedDart) :
    C.ResidualDartCondition (G.molecule.mate x.1) := by
  refine ⟨⟨x.2.1.2,?_⟩,?_⟩
  · simpa only [G.molecule.mate_mate] using x.2.1.1
  · intro S hS hi
    exact x.2.2 S hS ⟨by simpa only [G.molecule.mate_mate] using hi.2,hi.1⟩

/-- The actual quotient-and-deletion directed molecule, independently
defined before identifying it with the distinguished ingredient. -/
@[expose] noncomputable def splicedMolecule (C : MarkedGardenChain G focus X left right) :
    Molecule C.SplicedAtom C.SplicedDart where
  atoms := univ
  atom x := mergeClass X C.erasedGroups ⟨G.molecule.atom x.1,x.2.1.1⟩
  mate x := ⟨G.molecule.mate x.1,C.splicedDart_mate x⟩
  out x := G.molecule.out x.1
  atom_mem _ := mem_univ _
  mate_mate x := Subtype.ext (G.molecule.mate_mate x.1)
  mate_ne x h := G.molecule.mate_ne x.1 (congrArg Subtype.val h)
  out_mate x := G.molecule.out_mate x.1

@[expose] def splicedDartEquiv (C : MarkedGardenChain G focus X left right) :
    C.SplicedDart ≃ {x : GardenDart G // G.molecule.InGroup focus.atoms x} :=
  Equiv.subtypeEquivRight C.residualDartCondition_iff_focus

@[expose] noncomputable def splicedAtomEquiv (C : MarkedGardenChain G focus X left right) :
    C.splicedMolecule.atoms ≃ focus.atoms :=
  ({ toFun := Subtype.val
     invFun := fun q => ⟨q,mem_univ _⟩
     left_inv := fun q => Subtype.ext rfl
     right_inv := fun _ => rfl } : C.splicedMolecule.atoms ≃ C.SplicedAtom).trans
    C.atomEquivalenceData.equiv

theorem splicedAtomEquiv_comm (C : MarkedGardenChain G focus X left right) (x : C.SplicedDart) :
    (induced G.molecule focus.atoms).atom (C.splicedDartEquiv x) =
      (C.splicedAtomEquiv ⟨C.splicedMolecule.atom x,C.splicedMolecule.atom_mem x⟩).1 := by
  have hf : G.molecule.atom x.1 ∈ focus.atoms :=
    ((C.residualDartCondition_iff_focus x.1).mp x.2).1
  have he := C.atomEquivalenceData.fixesFocus ⟨G.molecule.atom x.1,hf⟩
  exact (congrArg (fun v : focus.atoms => v.1) he).symm

/-- TARGET `blockchainprop`, splicing conclusion in its exact molecular
form: after merging all CL ingredient atoms and removing their internal
bonds, the whole block is precisely the distinguished ingredient up to
atom names. No isomorphism or residual-bond assertion is a hypothesis. -/
@[expose] noncomputable def splicedFocusIso (C : MarkedGardenChain G focus X left right) :
    DirectedMoleculeIso C.splicedMolecule (induced G.molecule focus.atoms) where
  atoms := C.splicedAtomEquiv
  darts := C.splicedDartEquiv
  atom_comm := C.splicedAtomEquiv_comm
  mate_comm _ := rfl
  out_comm _ := rfl

/-- When the distinguished ingredient is CN, the molecular splicing
leaves exactly that single CN block, as asserted in TARGET `blockchainprop`. -/
theorem splicing_leaves_cn (C : MarkedGardenChain G focus X left right)
    (hCN : CNParentPattern G focus.atoms focus.leftJoint focus.rightJoint) :
    CNParentPattern G focus.atoms focus.leftJoint focus.rightJoint ∧
      Nonempty (DirectedMoleculeIso C.splicedMolecule (induced G.molecule focus.atoms)) :=
  ⟨hCN,⟨C.splicedFocusIso⟩⟩

end MarkedGardenChain
end WaveTurbulence.Mole
