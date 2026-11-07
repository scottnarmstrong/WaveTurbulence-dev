/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBPatterns
public import WaveTurbulence.Foundations.FinalCount.Degen.BondDeletion
import Mathlib.Tactic

/-! # Actual realizations and erasures of Appendix B atomic groups

The input is an enumeration of the old incident bonds, including their
endpoints. The post-molecule is constructed by literal atom deletion.
No output component, count, or deviation bound is a realization field.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def AppbPattern.vertices (P : AppbPattern) : Finset ℕ :=
  P.removed ∪ (P.edges.flatMap fun e => [e.1,e.2]).toFinset

/-- All old bonds touching the removed atoms, represented by outgoing darts. -/
def appbRemovedBonds (M : Molecule V D) (Y : Finset V) : Finset D :=
  M.bonds.filter fun x => M.atom x ∈ Y ∨ M.atom (M.mate x) ∈ Y

/-- A figure realized in an actual molecule. Surviving vertices may have
additional ambient bonds, which the operation retains. -/
structure AppbRealization (M : Molecule V D) (P : AppbPattern) where
  vertex : ℕ → V
  vertex_injective : Set.InjOn vertex (P.vertices : Set ℕ)
  vertex_mem : ∀ v ∈ P.vertices, vertex v ∈ M.atoms
  edge : Fin P.edges.length ≃ {x // x ∈ appbRemovedBonds M (P.removed.image vertex)}
  endpoints : ∀ i, M.ends (edge i).val = s(vertex (P.edges[i].1), vertex (P.edges[i].2))

namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

def removedAtoms : Finset V := P.removed.image r.vertex

def post : Molecule V (Degen.RetainedDart M r.removedAtoms) :=
  Degen.eraseAtoms M r.removedAtoms

theorem removedAtoms_subset : r.removedAtoms ⊆ M.atoms := by
  intro v hv
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hv
  exact r.vertex_mem a (mem_union_left _ ha)

/-- Exact atom decrement, including deletion of a whole component. -/
theorem post_card_atoms : r.post.atoms.card + P.removed.card = M.atoms.card := by
  have hinj : Set.InjOn r.vertex (P.removed : Set ℕ) :=
    r.vertex_injective.mono (by intro a ha; exact mem_union_left _ ha)
  have hc : r.removedAtoms.card = P.removed.card := card_image_of_injOn hinj
  rw [← hc]
  exact appb_eraseAtoms_card M r.removedAtoms r.removedAtoms_subset

/-- Exact bond decrement, from the actual incident-bond enumeration. -/
theorem post_card_bonds : r.post.bonds.card + P.edges.length = M.bonds.card := by
  have he : (appbRemovedBonds M r.removedAtoms).card = P.edges.length := by
    have hh := Fintype.card_congr r.edge
    simpa only [Fintype.card_fin, Fintype.card_coe, removedAtoms] using hh.symm
  change (Degen.eraseAtoms M r.removedAtoms).bonds.card + _ = _
  rw [Degen.card_bonds_eraseAtoms, ← he]
  have hn : (M.bonds.filter fun x => M.atom x ∉ r.removedAtoms ∧
      M.atom (M.mate x) ∉ r.removedAtoms) =
      M.bonds.filter (fun x => ¬(M.atom x ∈ r.removedAtoms ∨ M.atom (M.mate x) ∈ r.removedAtoms)) := by
    ext x
    simp only [mem_filter, not_or]
  rw [hn,appbRemovedBonds,add_comm,card_filter_add_card_filter_not]

/-- The exact circuit-rank effect; the remaining term is the actual
component difference, to be evaluated by the operation's cut topology. -/
theorem post_circuitRank : r.post.circuitRank - M.circuitRank =
    -(P.edges.length : ℤ) + P.removed.card +
      ((r.post.numComponents : ℤ) - M.numComponents) := by
  have hv := r.post_card_atoms
  have he := r.post_card_bonds
  have hvz : (r.post.atoms.card : ℤ) + P.removed.card = M.atoms.card := by exact_mod_cast hv
  have hez : (r.post.bonds.card : ℤ) + P.edges.length = M.bonds.card := by exact_mod_cast he
  unfold Molecule.circuitRank
  omega

/-- The exact nu effect, with actual post component count. -/
theorem post_nu : appbNu r.post - appbNu M =
    -4 * (P.removed.card : ℤ) + 2 * P.edges.length -
      4 * ((r.post.numComponents : ℤ) - M.numComponents) := by
  have hv := r.post_card_atoms
  have he := r.post_card_bonds
  have hvz : (r.post.atoms.card : ℤ) + P.removed.card = M.atoms.card := by exact_mod_cast hv
  have hez : (r.post.bonds.card : ℤ) + P.edges.length = M.bonds.card := by exact_mod_cast he
  unfold appbNu
  omega

end AppbRealization
end WaveTurbulence.Mole
