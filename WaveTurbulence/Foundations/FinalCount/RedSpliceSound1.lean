/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceSpec
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a): the structural half of `Stage1Piece.Sound` for any disjoint family

For the simultaneous splice `spliceGarden G0 l` of a family of (CL) blocks of a plain irreducible
garden `G0` (width `2R`, positive order): plain, irreducible, same signature, order in `[1, order G0]`,
molecule axioms, connected, `n` atoms and `2n - R` bonds (TARGET `subpro` (1)).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open TTree Finset WaveTurbulence WaveTurbulence.Mole SpMap

variable {R : ℕ}

theorem spliceGarden_plain (G0 : Garden (2 * R)) (l : List (CLBlock G0)) (hP : G0.IsPlain) :
    (spliceGarden G0 l).IsPlain := (spliceFold G0 l).plain hP

theorem spliceGarden_irreducible (G0 : Garden (2 * R)) (l : List (CLBlock G0)) (hP : G0.IsPlain)
    (hI : G0.Irreducible) : (spliceGarden G0 l).Irreducible := (spliceFold G0 l).irred hP hI

theorem spliceGarden_sig (G0 : Garden (2 * R)) (l : List (CLBlock G0)) :
    (spliceGarden G0 l).sig = G0.sig := (spliceFold G0 l).sig_eq

theorem spliceGarden_order_le (G0 : Garden (2 * R)) (l : List (CLBlock G0)) :
    (spliceGarden G0 l).order ≤ G0.order := (spliceFold G0 l).M.order_le

theorem spliceGarden_order_pos (G0 : Garden (2 * R)) (l : List (CLBlock G0)) (h : 1 ≤ G0.order) :
    1 ≤ (spliceGarden G0 l).order := (spliceFold G0 l).M.order_pos (spliceFold G0 l).hcls h

theorem spliceGarden_connected (G0 : Garden (2 * R)) (l : List (CLBlock G0)) (hP : G0.IsPlain)
    (hI : G0.Irreducible) : (spliceGarden G0 l).molecule.IsConnected := by
  apply (spliceFold G0 l).M.connected (spliceFold G0 l).hcls
  intro u _ v _
  exact irreducible_garden_molecule_connected G0 hP hI u v

theorem spliceGarden_molecule (G0 : Garden (2 * R)) (l : List (CLBlock G0)) :
    (spliceGarden G0 l).molecule.IsMolecule := garden_isMolecule _

theorem spliceGarden_atom_count (G0 : Garden (2 * R)) (l : List (CLBlock G0)) :
    (spliceGarden G0 l).molecule.atoms.card = (spliceGarden G0 l).order := garden_card_atoms _

theorem spliceGarden_bond_count (G0 : Garden (2 * R)) (l : List (CLBlock G0)) (hP : G0.IsPlain)
    (hI : G0.Irreducible) (h : 1 ≤ G0.order) :
    (spliceGarden G0 l).molecule.bonds.card + R = 2 * (spliceGarden G0 l).order := by
  have := irreducible_garden_bonds_identity (spliceGarden G0 l) (spliceGarden_plain G0 l hP)
    (spliceGarden_irreducible G0 l hP hI) (spliceGarden_order_pos G0 l h)
  omega

end WaveTurbulence.RedSplice
