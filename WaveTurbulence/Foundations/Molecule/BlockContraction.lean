/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeBlockBarriers
import Mathlib.Tactic

/-! # Concrete atom contraction with internal bonds removed
TARGET `block_clcn` (2): the merged atom is `none`, all other atoms retain
their names, and the surviving darts are exactly the noninternal bonds.
-/

public section
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] (M : Molecule V D)

/-- Vertex names after merging an atomic group. -/
abbrev ContractVertex (S : Finset V) := Option {v : V // v ∉ S}

/-- All atoms of S map to the single merged vertex. -/
@[expose] def contractVertex (S : Finset V) (v : V) : ContractVertex S :=
  if h : v ∈ S then none else some ⟨v,h⟩

/-- Exactly the old bonds not internal to the merged group survive. -/
abbrev ContractDart (S : Finset V) := {x : D // ¬ M.InGroup S x}

theorem contractDart_mate {S : Finset V} (x : ContractDart M S) : ¬ M.InGroup S (M.mate x.1) := by
  intro h
  exact x.2 ⟨by simpa only [M.mate_mate] using h.2,h.1⟩

/-- The actual directed multigraph obtained by merging S and deleting
its internal bonds, retaining all external multiplicities and orientations. -/
@[expose] noncomputable def contractGroup (S : Finset V) :
    Molecule (ContractVertex S) (ContractDart M S) where
  atoms := M.atoms.image (contractVertex S)
  atom x := contractVertex S (M.atom x.1)
  mate x := ⟨M.mate x.1,contractDart_mate M x⟩
  out x := M.out x.1
  atom_mem x := mem_image.mpr ⟨M.atom x.1,M.atom_mem x.1,rfl⟩
  mate_mate x := Subtype.ext (M.mate_mate x.1)
  mate_ne x h := M.mate_ne x.1 (congrArg Subtype.val h)
  out_mate x := M.out_mate x.1

theorem contractVertex_eq_none (S : Finset V) (v : V) : contractVertex S v = none ↔ v ∈ S := by
  unfold contractVertex
  split <;> simp_all

theorem contractVertex_outside_injective {S : Finset V} {u v : V}
    (hu : u ∉ S) (hv : v ∉ S) (he : contractVertex S u = contractVertex S v) : u = v := by
  simpa only [contractVertex,dite_eq_right hu,dite_eq_right hv,Option.some.injEq,Subtype.mk.injEq] using he

end WaveTurbulence.Mole
