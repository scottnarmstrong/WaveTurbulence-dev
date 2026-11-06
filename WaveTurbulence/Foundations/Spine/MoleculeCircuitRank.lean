/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.GraphForestBound
public import WaveTurbulence.Foundations.WaveB.Molecules
/-! The circuit rank `chi = E - V + F` of every finite half-edge molecule is nonnegative. The proof is
ported (with the simple-graph reduction and the edge bound `atomGraph_edges_le_bonds`) from
`/home/scott/wt-scratch/mole/src/MoleculeGraphBounds.lean` (sha256
2f5cd70949e0281807c8c2af4965a728844ff5af29814b197e38bffa340884d3), generalized from the connected case
to arbitrary molecules by `card_le_edgeSet_add_components`. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence Finset
open scoped Classical

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

theorem molecule_adj_symm {u v : V} (h : M.Adj u v) : M.Adj v u := by
  obtain ⟨x, rfl, rfl⟩ := h
  exact ⟨M.mate x, rfl, by rw [M.mate_mate]⟩

/-- The underlying simple atom graph (no loops, parallel bonds identified). -/
@[expose] def atomGraph : SimpleGraph M.atoms where
  Adj a b := a ≠ b ∧ M.Adj a.1 b.1
  symm := ⟨by rintro a b ⟨hab, h⟩; exact ⟨hab.symm, molecule_adj_symm M h⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

/-- Every actual bond has a canonical pair of endpoints in the atom subtype. -/
@[expose] def bondEnds (x : D) : Sym2 M.atoms :=
  s(⟨M.atom x, M.atom_mem x⟩, ⟨M.atom (M.mate x), M.atom_mem (M.mate x)⟩)

theorem atomGraph_edges_le_bonds : Nat.card (atomGraph M).edgeSet ≤ M.bonds.card := by
  have hsub : (atomGraph M).edgeFinset ⊆ M.bonds.image (bondEnds M) := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ a b =>
      have hab : (atomGraph M).Adj a b := by
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
      obtain ⟨_hne, x, hxa, hxb⟩ := hab
      have ha : (⟨M.atom x, M.atom_mem x⟩ : M.atoms) = a := Subtype.ext hxa
      have hb : (⟨M.atom (M.mate x), M.atom_mem (M.mate x)⟩ : M.atoms) = b := Subtype.ext hxb
      cases hout : M.out x
      · refine Finset.mem_image.mpr ⟨M.mate x, ?_, ?_⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [M.out_mate, hout]; rfl⟩
        · dsimp only [bondEnds]
          simp only [M.mate_mate, hb, ha]
          exact Sym2.eq_swap
      · refine Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hout⟩, ?_⟩
        simp only [bondEnds, ha, hb]
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_image_le)
  simpa only [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet] using hcard

theorem components_le_numComponents : Nat.card (atomGraph M).ConnectedComponent ≤ M.numComponents := by
  unfold Molecule.numComponents
  haveI : Finite (atomGraph M).ConnectedComponent := inferInstance
  refine Nat.card_le_card_of_surjective
    (Quot.lift (fun a : M.atoms => (atomGraph M).connectedComponentMk a) ?_) ?_
  · intro a b h
    by_cases hab : a = b
    · rw [hab]
    · exact SimpleGraph.ConnectedComponent.eq.mpr (SimpleGraph.Adj.reachable ⟨hab, h⟩)
  · intro c
    obtain ⟨a, rfl⟩ := c.exists_rep
    exact ⟨Quot.mk _ a, rfl⟩

theorem circuitRank_nonneg : 0 ≤ M.circuitRank := by
  have h1 := card_le_edgeSet_add_components (atomGraph M)
  have h2 := atomGraph_edges_le_bonds M
  have h3 := components_le_numComponents M
  rw [Fintype.card_coe] at h1
  unfold Molecule.circuitRank
  omega

end WaveTurbulence.LGSpine
