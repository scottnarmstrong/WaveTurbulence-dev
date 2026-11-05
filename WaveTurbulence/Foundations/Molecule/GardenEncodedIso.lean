/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.GardenPositionReconstruction
import Mathlib.Tactic

/-!
# Uniqueness of tree reconstruction from encoded molecules

DH21-2 Proposition 6.4: a position-preserving graph isomorphism preserves
parent-child incidence. Once the root ordering is fixed, it preserves
all branching-node addresses, and therefore all of the ternary trees.
-/

public section
namespace WaveTurbulence.Mole
open TTree
variable {w : ℕ} {G H : Garden w}

/-- An actual isomorphism of the half-edge molecules with their local
position codes. No tree or pairing preservation is assumed. -/
structure GardenEncodedIso (G H : Garden w) where
  branches : GBranch G.tree ≃ GBranch H.tree
  darts : GardenDart G ≃ GardenDart H
  atom_comm : ∀ x, H.molecule.atom (darts x) = branches (G.molecule.atom x)
  mate_comm : ∀ x, H.molecule.mate (darts x) = darts (G.molecule.mate x)
  position_comm : ∀ x, dartPosition H (darts x) = dartPosition G x

namespace GardenEncodedIso

/-- The encoded graph detects the actual branching roots. -/
theorem root_iff (f : GardenEncodedIso G H) (v : GBranch G.tree) :
    (f.branches v).1.2 = [] ↔ v.1.2 = [] := by
  rw [branch_root_iff_no_zero H,branch_root_iff_no_zero G]
  constructor
  · intro hn ⟨x,hx,hp⟩
    apply hn
    exact ⟨f.darts x,(f.atom_comm x).trans (congrArg f.branches hx),
      (f.position_comm x).trans hp⟩
  · intro hn ⟨y,hy,hp⟩
    let x := f.darts.symm y
    have hxy : f.darts x = y := f.darts.apply_symm_apply y
    have hx : G.molecule.atom x = v := by
      apply f.branches.injective
      rw [← f.atom_comm x,hxy,hy]
    have hpos : dartPosition G x = 0 := by rw [← f.position_comm x,hxy,hp]
    exact hn ⟨x,hx,hpos⟩

/-- The PC relation is forced by zero/nonzero incidence codes. -/
theorem parent_child (f : GardenEncodedIso G H) (v : GBranch G.tree) (hv : v.1.2 ≠ []) :
    (f.branches (GNode.parent v.toNode hv)).child (v.1.2.getLast hv) =
      (f.branches v).toNode := by
  let x : GardenDart G := .inl (⟨v,hv⟩,true)
  have hx : dartPosition H (f.darts x) = (v.1.2.getLast hv).succ := f.position_comm x
  have hm : dartPosition H (H.molecule.mate (f.darts x)) = 0 := by
    rw [f.mate_comm,f.position_comm]
    rfl
  have he := position_recovers_child H (f.darts x) (v.1.2.getLast hv) hx hm
  rw [f.atom_comm,f.mate_comm,f.atom_comm] at he
  exact he

/-- Fixing the root ordering fixes every actual branching-node address. -/
theorem branch_addresses (f : GardenEncodedIso G H)
    (hroot : ∀ v : GBranch G.tree, v.1.2 = [] → (f.branches v).1.1 = v.1.1)
    (v : GBranch G.tree) : (f.branches v).1 = v.1 := by
  by_cases hv : v.1.2 = []
  · exact Prod.ext (hroot v hv) (((f.root_iff v).mpr hv).trans hv.symm)
  · let p : GBranch G.tree := GNode.parent v.toNode hv
    have ih := branch_addresses f hroot p
    have he := congrArg (fun a : GNode H.tree => a.1) (f.parent_child v hv)
    change ((f.branches p).1.1,(f.branches p).1.2++[v.1.2.getLast hv]) = (f.branches v).1 at he
    rw [ih] at he
    exact he.symm.trans (Prod.ext rfl (List.dropLast_append_getLast hv))
termination_by v.1.2.length
decreasing_by
  change v.1.2.dropLast.length < v.1.2.length
  rw [List.length_dropLast]
  have hpos := List.length_pos_iff.mpr hv
  omega

end GardenEncodedIso
end WaveTurbulence.Mole
