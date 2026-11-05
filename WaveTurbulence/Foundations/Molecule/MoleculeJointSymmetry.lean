/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeBlockRealizations
import Mathlib.Tactic

/-! # Exchanging the two joints in actual block and deletion data -/

public section
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] (M : Molecule V D)

/-- Block joints are unordered; orientation counts stay attached to their atoms. -/
theorem block_swap_joints {S : Finset V} {a b : V} (hB : M.IsBlock S a b) : M.IsBlock S b a := by
  obtain ⟨hS,ha,hb,hne,hoa,hia,hob,hib,hi⟩ := hB
  exact ⟨hS,hb,ha,Ne.symm hne,hob,hib,hoa,hia,fun v hv h1 h2 => hi.1 v hv h2 h1,hi.2⟩

omit [Fintype D] in
/-- The labels of the two actual connected components can be exchanged. -/
theorem twoComponents_swap {S : Finset V} {a b : V} (h : TwoComponents M S a b) : TwoComponents M S b a := by
  obtain ⟨U,W,hcover,hdis,hU,hW,ha,hb,hno⟩ := h
  refine ⟨W,U,?_,hdis.symm,hW,hU,hb,ha,?_⟩
  · rw [Finset.union_comm,hcover]
  · intro w hw u hu hadj
    exact hno u hu w hw (adj_symmetric M hadj)

omit [Fintype D] in
/-- The source interior-deletion property is symmetric in its joints. -/
theorem interiorDeletionProperty_swap {S : Finset V} {a b : V}
    (h : InteriorDeletionProperty M S a b) : InteriorDeletionProperty M S b a := by
  intro v hv h1 h2
  rcases h v hv h2 h1 with hc | ht
  · exact Or.inl hc
  · exact Or.inr (twoComponents_swap M ht)

variable [DecidableEq D] {M}

/-- A realization can exchange its joint ordering without changing a bond. -/
@[expose] def BlockRealization.swap {S : Finset V} {a b : V} (R : BlockRealization M S a b) :
    BlockRealization M S b a := by
  cases R with
  | block hB hc => exact .block (block_swap_joints M hB) hc
  | hyper e he hB hc => exact .hyper e (he.trans Sym2.eq_swap) (block_swap_joints (eraseBond M e) hB) hc

end WaveTurbulence.Mole
