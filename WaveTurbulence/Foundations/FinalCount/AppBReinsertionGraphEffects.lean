/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBReinsertion
public import WaveTurbulence.Foundations.FinalCount.AppBAddConnectedBond
import Mathlib.Tactic

/-! # Exact circuit and nu effects of the actual reinserted bond -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

/-- Reinsertion inside one residual component adds exactly one circuit
and lowers nu by two. Its atom set is unchanged. -/
theorem postWithBond_graph_effects (a b : ℕ) (ha : a ∈ P.vertices) (hb : b ∈ P.vertices)
    (hka : a ∉ P.removed) (hkb : b ∉ P.removed)
    (hpath : r.post.SameComponent (r.vertex a) (r.vertex b)) :
    (r.postWithBond a b).numComponents = r.post.numComponents ∧
    (r.postWithBond a b).circuitRank = r.post.circuitRank + 1 ∧
    appbNu (r.postWithBond a b) = appbNu r.post - 2 := by
  have hf := appb_addBond_components_of_connected r.post (r.vertex a) (r.vertex b)
    (r.vertex_mem_post a ha hka) (r.vertex_mem_post b hb hkb) hpath
  change (r.postWithBond a b).numComponents = r.post.numComponents at hf
  have he := r.postWithBond_bonds a b
  have hv : (r.postWithBond a b).atoms.card = r.post.atoms.card := congrArg card (r.postWithBond_atoms a b ha hb hka hkb)
  refine ⟨hf,?_,?_⟩
  · unfold Molecule.circuitRank
    rw [hf,he,hv]
    push_cast
    ring
  · unfold appbNu
    rw [hf,he,hv]
    push_cast
    ring

/-- Choosing the output direction from the old boundary bond has exactly
the same graph effects, for either possible old orientation. -/
theorem directedPostWithBond_graph_effects (a b : ℕ) (i : Fin P.edges.length)
    (ha : a ∈ P.vertices) (hb : b ∈ P.vertices) (hka : a ∉ P.removed) (hkb : b ∉ P.removed)
    (hpath : r.post.SameComponent (r.vertex a) (r.vertex b)) :
    (r.directedPostWithBond a b i).numComponents = r.post.numComponents ∧
    (r.directedPostWithBond a b i).circuitRank = r.post.circuitRank + 1 ∧
    appbNu (r.directedPostWithBond a b i) = appbNu r.post - 2 := by
  unfold directedPostWithBond
  split_ifs
  · exact r.postWithBond_graph_effects a b ha hb hka hkb hpath
  · exact r.postWithBond_graph_effects b a hb ha hkb hka hpath.symm

end AppbRealization
end WaveTurbulence.Mole
