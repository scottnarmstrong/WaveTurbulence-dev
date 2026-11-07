/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBIsoComponents
public import WaveTurbulence.Foundations.FinalCount.AppBRealizations
import Mathlib.Tactic

/-! # Actual atom-and-dart isomorphism for two successive atom deletions -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def appbEraseAtomsUnionIso (M : Molecule V D) (Y Z : Finset V) :
    DirectedMoleculeIso (Degen.eraseAtoms (Degen.eraseAtoms M Y) Z) (Degen.eraseAtoms M (Y ∪ Z)) := by
  have hatoms : (Degen.eraseAtoms (Degen.eraseAtoms M Y) Z).atoms =
      (Degen.eraseAtoms M (Y ∪ Z)).atoms := by
    ext v
    simp only [Degen.eraseAtoms,mem_sdiff,mem_union]
    tauto
  let ae : (Degen.eraseAtoms (Degen.eraseAtoms M Y) Z).atoms ≃ (Degen.eraseAtoms M (Y ∪ Z)).atoms := {
    toFun := fun v => ⟨v.val,hatoms ▸ v.property⟩
    invFun := fun v => ⟨v.val,hatoms.symm ▸ v.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let de : Degen.RetainedDart (Degen.eraseAtoms M Y) Z ≃ Degen.RetainedDart M (Y ∪ Z) := {
    toFun := fun x => ⟨x.val.val,
      notMem_union.mpr ⟨x.val.property.1,x.property.1⟩,
      notMem_union.mpr ⟨x.val.property.2,x.property.2⟩⟩
    invFun := fun x => ⟨⟨x.val,(notMem_union.mp x.property.1).1,(notMem_union.mp x.property.2).1⟩,
      (notMem_union.mp x.property.1).2,(notMem_union.mp x.property.2).2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact {
    atoms := ae
    darts := de
    atom_comm := fun _ => rfl
    mate_comm := fun _ => rfl
    out_comm := fun _ => rfl }

end WaveTurbulence.Mole
