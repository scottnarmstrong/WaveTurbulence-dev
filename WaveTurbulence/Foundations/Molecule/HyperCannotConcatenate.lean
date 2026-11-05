/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeBlockConcatenation
public import WaveTurbulence.Foundations.Molecule.MoleculeHyperBlocks
import Mathlib.Tactic

/-! # A hyper-block cannot be extended by a further block
TARGET `defblock` L1330. This justifies recording legal block typing at
intermediate steps in a marked concatenation whose final object is a block.
-/

public section
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

theorem hyper_cannot_concatenate (hM : M.IsMolecule) {S T : Finset V} {a b c : V}
    (hH : IsHyperBlock M S a c) (hB : M.IsBlock T b c) (hcB : GroupConnected M T)
    (hi : S ∩ T = {c}) : False := by
  have hdH := (hyperBlock_degrees M hH).2.1
  have hdB := (block_joint_degrees M hB).2
  have hcS : c ∈ S := by
    obtain ⟨e,he,hbase⟩ := hH
    exact hbase.2.2.1
  have hno : ∀ x, M.atom x = c → M.atom (M.mate x) ≠ c := by
    intro x hx
    have hh := connected_block_no_joint_loop M hB hcB (Or.inr hx)
    simpa only [hx] using hh
  have hz : M.degIn (S ∩ T) c = 0 := by
    rw [hi]
    exact degIn_singleton_eq_zero M hno
  have hs := degIn_union_add_inter M S T hcS hB.2.2.1
  have hle := (degIn_le_deg M (S ∪ T) c).trans (deg_le_four M hM (hB.1 hB.2.2.1))
  omega

end WaveTurbulence.Mole
