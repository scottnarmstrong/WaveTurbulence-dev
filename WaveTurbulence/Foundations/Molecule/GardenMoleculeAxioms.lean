/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.GardenOrientation
public import WaveTurbulence.Foundations.Molecule.MoleculeComponents
import Mathlib.Tactic

/-!
# The actual garden constructor satisfies the molecule axioms

TARGET `propcplmol` L1304–L1306: every branching atom is linked by parent
bonds to its tree root; the root has no parent dart and is unsaturated.
The argument works even for marked or reducible gardens.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ} {tree : Fin w → TTree}

/-- The branching root of the tree containing an existing branching node. -/
@[expose] def branchRoot (c : GBranch tree) : GBranch tree :=
  ⟨(c.1.1,[]),by
    have hroot (t : TTree) (ht : t.branching.Nonempty) : ([] : Path) ∈ t.branching := by
      cases t <;> simp_all [TTree.branching]
    exact hroot _ ⟨c.1.2,c.2⟩⟩

theorem branch_adj_parent (G : Garden w) (c : GBranch G.tree) (hc : c.1.2 ≠ []) :
    G.molecule.Adj c (GNode.parent c.toNode hc) := by
  refine ⟨Sum.inl (⟨c,hc⟩,false),rfl,?_⟩
  rfl

/-- Following actual parent bonds reaches the branching tree root. -/
theorem branch_connected_root (G : Garden w) (c : GBranch G.tree) :
    G.molecule.SameComponent c (branchRoot c) := by
  by_cases hc : c.1.2 = []
  · have he : c = branchRoot c := Subtype.ext (Prod.ext rfl hc)
    exact he ▸ sameComponent_refl G.molecule c
  · let p := GNode.parent c.toNode hc
    have hp := branch_connected_root G p
    have he : branchRoot p = branchRoot c := Subtype.ext rfl
    rw [he] at hp
    exact sameComponent_trans G.molecule (sameComponent_of_adj G.molecule (branch_adj_parent G c hc)) hp
termination_by c.1.2.length
decreasing_by
  dsimp only [p,GNode.parent,GBranch.toNode]
  rw [List.length_dropLast]
  have hpos := List.length_pos_of_ne_nil hc
  omega

theorem dart_position_ne_zero_at_root (G : Garden w) (v : GBranch G.tree) (hv : v.1.2 = [])
    (x : GardenDart G) (hx : G.molecule.atom x = v) : dartPosition G x ≠ 0 := by
  rcases x with ⟨c,_|_⟩ | l
  · change c.1 = v at hx
    have he := congrArg (fun z : GBranch G.tree => z.1.2) hx
    exact False.elim (c.2 (he.trans hv))
  · exact Fin.succ_ne_zero _
  · exact Fin.succ_ne_zero _

/-- An actual root atom has at most three darts, so it is unsaturated. -/
theorem root_degree_le_three (G : Garden w) (v : GBranch G.tree) (hv : v.1.2 = []) :
    G.molecule.deg v ≤ 3 := by
  let S := G.molecule.dartsAt v
  have hinj : Set.InjOn (dartPosition G) S := by
    intro x hx y hy hxy
    apply atom_position_injective G
    apply Prod.ext
    · exact ((mem_dartsAt G.molecule v x).mp hx).trans ((mem_dartsAt G.molecule v y).mp hy).symm
    · exact hxy
  have hsub : S.image (dartPosition G) ⊆ (Finset.univ : Finset (Fin 4)).erase 0 := by
    intro i hi
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_erase.mpr ⟨dart_position_ne_zero_at_root G v hv x
      ((mem_dartsAt G.molecule v x).mp hx),Finset.mem_univ _⟩
  have hh := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj] at hh
  have hc : ((Finset.univ : Finset (Fin 4)).erase 0).card = 3 := by decide
  rw [hc] at hh
  exact hh

/-- The actual garden molecule satisfies both molecule axioms. This
proves the B2 characterization obligation without using its draft proof. -/
theorem garden_isMolecule (G : Garden w) : G.molecule.IsMolecule := by
  constructor
  · intro v _hv
    exact ⟨garden_molecule_outdeg_le_two G v,garden_molecule_indeg_le_two G v⟩
  · intro v _hv
    refine ⟨branchRoot v,Finset.mem_univ _,branch_connected_root G v,?_⟩
    have hh := root_degree_le_three G (branchRoot v) rfl
    omega

end WaveTurbulence.Mole
