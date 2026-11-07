/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceSound1
public import WaveTurbulence.Foundations.FinalCount.RedSpliceHinge
public import WaveTurbulence.Foundations.Spine.Stage1Interface
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a): the generic part of `Stage1Piece.Sound` for the spliced garden

`SoundBasics` collects exactly the S2a-owned `Stage1Piece.Sound` fields that do not involve the collection
`C_1`: plain, irreducible, balanced, order bounds, layer bound, molecule, connected, atom/bond counts,
and the triple-bond clause of `SubproChoices.Structural` (with the hinge set of the splice).
They hold for the simultaneous splice of ANY family `l` of (CL) blocks of the skeleton garden.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open TTree Finset WaveTurbulence WaveTurbulence.Mole SpMap WaveTurbulence.LGSpine

variable {R : ℕ}

/-- The S2a-owned `Sound` fields independent of the collection `C_1`. -/
structure SoundBasics (G0 : Garden (2 * R)) (st : SpState G0) (layer0 : GBranch G0.tree → ℕ) (p N : ℕ) : Prop where
  plain : st.G.IsPlain
  irreducible : st.G.Irreducible
  balanced : IsBalancedSig st.G.sig
  order_pos : 1 ≤ st.G.order
  order_le : st.G.order ≤ N
  layer_le : ∀ c, st.layer layer0 c ≤ p
  molecule : st.G.molecule.IsMolecule
  connected : st.G.molecule.IsConnected
  atom_count : st.G.molecule.atoms.card = st.G.order
  bond_count : st.G.molecule.bonds.card + R = 2 * st.G.order
  triple_hinge : ∀ a b, st.G.molecule.bondsBetween a b = 3 → a ∈ st.hinges ∨ b ∈ st.hinges

/-- The S2a-owned basics for the splice of an arbitrary family of blocks. -/
theorem soundBasics (G0 : Garden (2 * R)) (l : List (CLBlock G0)) (layer0 : GBranch G0.tree → ℕ) (p N : ℕ)
    (hP : G0.IsPlain) (hI : G0.Irreducible) (hbal : IsBalancedSig G0.sig) (hn : 1 ≤ G0.order)
    (hN : G0.order ≤ N) (hlayer : ∀ v, layer0 v ≤ p)
    (hno : ∀ a b, G0.molecule.bondsBetween a b ≠ 3) :
    SoundBasics G0 (spliceFold G0 l) layer0 p N where
  plain := spliceGarden_plain G0 l hP
  irreducible := spliceGarden_irreducible G0 l hP hI
  balanced := by
    have := spliceGarden_sig G0 l
    unfold spliceGarden at this
    rw [this]; exact hbal
  order_pos := spliceGarden_order_pos G0 l hn
  order_le := (spliceGarden_order_le G0 l).trans hN
  layer_le := (spliceFold G0 l).layer_le layer0 hlayer
  molecule := spliceGarden_molecule G0 l
  connected := spliceGarden_connected G0 l hP hI
  atom_count := spliceGarden_atom_count G0 l
  bond_count := spliceGarden_bond_count G0 l hP hI hn
  triple_hinge := (spliceFold G0 l).triple_hinge hno

end WaveTurbulence.RedSplice
