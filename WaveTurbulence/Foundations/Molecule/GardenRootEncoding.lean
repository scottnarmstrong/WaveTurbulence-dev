/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.TreeReconstruction
public import WaveTurbulence.Foundations.Molecule.GardenNodeCounts
import Mathlib.Tactic

/-!
# Root records for molecular reconstruction

DH21-2 Proposition 6.4: nontrivial roots record their atom; trivial roots
record either their partner root or the atom/child position of their
partner. This records the trivial-tree data omitted by incidence codes.
-/

public section
namespace WaveTurbulence.Mole
open TTree
variable {w : ℕ} {V D : Type*} (G : Garden w) (M : Molecule V D)

/-- An isomorphism to a fixed directed molecule, retaining actual half-edge
multiplicities and the atom set. -/
structure GardenMoleculeIso where
  branches : GBranch G.tree ≃ M.atoms
  darts : GardenDart G ≃ D
  atom_comm : ∀ x, M.atom (darts x) = (branches (G.molecule.atom x)).1
  mate_comm : ∀ x, M.mate (darts x) = darts (G.molecule.mate x)
  out_comm : ∀ x, M.out (darts x) = G.molecule.out x

/-- Root information has four atom-slot choices per atom, or a partner root. -/
abbrev RootRecord (A : Type*) (w : ℕ) := A ⊕ ((A × Fin 3) ⊕ Fin w)

/-- The actual code function on a fixed molecule. -/
@[expose] def encodePositions (f : GardenMoleculeIso G M) : D → Fin 4 :=
  fun x => dartPosition G (f.darts.symm x)

/-- The actual root record, including roots of trivial trees. -/
@[expose] def encodeRoot (f : GardenMoleculeIso G M) (i : Fin w) : RootRecord M.atoms w :=
  if hb : [] ∈ (G.tree i).branching then .inl (f.branches ⟨(i,[]),hb⟩)
  else
    let l : GLeaf G.tree := ⟨(i,[]),((TTree.mem_nodes_iff _ _).mp (TTree.nil_mem_nodes _)).resolve_right hb⟩
    if hp : (G.pair l).1.2 = [] then .inr (.inr (G.pair l).1.1)
    else .inr (.inl (f.branches (GNode.parent (G.pair l).toNode hp),(G.pair l).1.2.getLast hp))

/-- A branching-root record identifies exactly its root index and atom. -/
theorem encodeRoot_inl_iff (f : GardenMoleculeIso G M) (i : Fin w) (a : M.atoms) :
    encodeRoot G M f i = .inl a ↔
      ∃ v : GBranch G.tree, v.1 = (i,[]) ∧ f.branches v = a := by
  unfold encodeRoot
  split
  · rename_i hb
    constructor
    · intro he
      exact ⟨⟨(i,[]),hb⟩,rfl,Sum.inl.inj he⟩
    · rintro ⟨v,hv,ha⟩
      have he : v = ⟨(i,[]),hb⟩ := Subtype.ext hv
      rw [← he,ha]
  · rename_i hb
    dsimp only
    split
    · constructor
      · intro he
        cases he
      · rintro ⟨v,hv,_ha⟩
        have hh := v.2
        change v.1.2 ∈ (G.tree v.1.1).branching at hh
        rw [hv] at hh
        exact (hb hh).elim
    · constructor
      · intro he
        cases he
      · rintro ⟨v,hv,_ha⟩
        have hh := v.2
        change v.1.2 ∈ (G.tree v.1.1).branching at hh
        rw [hv] at hh
        exact (hb hh).elim

/-- Equal position functions produce an actual encoded graph isomorphism. -/
@[expose] def isoOfCodes {H : Garden w} (f : GardenMoleculeIso G M) (g : GardenMoleculeIso H M)
    (hc : encodePositions G M f = encodePositions H M g) : GardenEncodedIso G H where
  branches := f.branches.trans g.branches.symm
  darts := f.darts.trans g.darts.symm
  atom_comm := by
    intro x
    apply g.branches.injective
    apply Subtype.ext
    rw [← g.atom_comm]
    simp only [Equiv.trans_apply,Equiv.apply_symm_apply]
    exact f.atom_comm x
  mate_comm := by
    intro x
    apply g.darts.injective
    rw [← g.mate_comm]
    simp only [Equiv.trans_apply,Equiv.apply_symm_apply]
    exact f.mate_comm x
  position_comm := by
    intro x
    have he := congrFun hc (f.darts x)
    simp only [encodePositions,Equiv.symm_apply_apply] at he
    exact he.symm

/-- Root records determine the root ordering required by tree reconstruction. -/
theorem roots_determine_order {H : Garden w} (f : GardenMoleculeIso G M)
    (g : GardenMoleculeIso H M) (hc : encodePositions G M f = encodePositions H M g)
    (hr : encodeRoot G M f = encodeRoot H M g) (v : GBranch G.tree) (hv : v.1.2 = []) :
    ((isoOfCodes G M f g hc).branches v).1.1 = v.1.1 := by
  have hrec : encodeRoot G M f v.1.1 = .inl (f.branches v) :=
    (encodeRoot_inl_iff G M f v.1.1 (f.branches v)).mpr ⟨v,Prod.ext rfl hv,rfl⟩
  rw [hr] at hrec
  obtain ⟨u,hu,huf⟩ := (encodeRoot_inl_iff H M g v.1.1 (f.branches v)).mp hrec
  have he : (isoOfCodes G M f g hc).branches v = u := by
    change g.branches.symm (f.branches v) = u
    rw [← huf,g.branches.symm_apply_apply]
  rw [he,hu]

end WaveTurbulence.Mole
