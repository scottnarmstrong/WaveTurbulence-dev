/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.GardenPairReconstruction
import Mathlib.Tactic

/-! # Uniqueness of plain garden reconstruction from positions and root records -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open TTree
variable {w : ℕ} {V D : Type*} {G H : Garden w} {M : Molecule V D}

/-- All actual leaf-pair coordinates are fixed by position codes and root
records, including pairs incident to one or two trivial roots. -/
theorem root_codes_recover_pairs (f : GardenMoleculeIso G M) (g : GardenMoleculeIso H M)
    (hP : G.IsPlain) (hc : encodePositions G M f = encodePositions H M g)
    (hr : encodeRoot G M f = encodeRoot H M g) (l : GLeaf G.tree) :
    ∃ m : GLeaf H.tree, m.1 = l.1 ∧ (H.pair m).1 = (G.pair l).1 := by
  by_cases hl : l.1.2 = []
  · exact root_record_recovers_pair f g hc hr l hl
  · by_cases hp : (G.pair l).1.2 = []
    · obtain ⟨m,hm,hmp⟩ := root_record_recovers_pair f g hc hr (G.pair l) hp
      rw [G.pair_pair] at hmp
      exact ⟨H.pair m,hmp,by rw [H.pair_pair]; exact hm⟩
    · exact (isoOfCodes G M f g hc).nonroot_leaf_pair
        (roots_determine_order G M f g hc hr) hP l hl hp

/-- Structure extensionality for actual gardens with identical tree carrier.
The marks and pairing, not their proof fields, determine the remaining data. -/
theorem garden_eq_same_trees (G H : Garden w) (ht : G.tree = H.tree) (hs : G.sig = H.sig)
    (hm : ∀ l : GLeaf G.tree, G.mark l = H.mark ⟨l.1,ht ▸ l.2⟩)
    (hp : ∀ l : GLeaf G.tree, (G.pair l).1 = (H.pair ⟨l.1,ht ▸ l.2⟩).1) : G = H := by
  cases G
  cases H
  cases ht
  cases hs
  congr 1
  · funext l
    exact Subtype.ext (hp l)
  · funext l
    exact hm l

/-- DH21-2 Proposition 6.4, reconstruction uniqueness: the entire plain
garden is recovered from incidence positions, root records and signatures. -/
theorem garden_reconstruction_unique (f : GardenMoleculeIso G M) (g : GardenMoleculeIso H M)
    (hP : G.IsPlain) (hQ : H.IsPlain) (hc : encodePositions G M f = encodePositions H M g)
    (hr : encodeRoot G M f = encodeRoot H M g) (hs : G.sig = H.sig) : G = H := by
  have ht := (isoOfCodes G M f g hc).trees_eq (roots_determine_order G M f g hc hr)
  apply garden_eq_same_trees G H ht hs
  · intro l
    exact (hP l).trans (hQ ⟨l.1,ht ▸ l.2⟩).symm
  · intro l
    obtain ⟨m,hm,hmp⟩ := root_codes_recover_pairs f g hP hc hr l
    have he : m = ⟨l.1,ht ▸ l.2⟩ := Subtype.ext hm
    rw [← he]
    exact hmp.symm

end WaveTurbulence.Mole
