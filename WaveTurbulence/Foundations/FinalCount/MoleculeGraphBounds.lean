/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeComponents
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic

/-!
# Connected half-edge molecules have nonnegative circuit rank

TARGET `propcplmol` L1304–L1306. The proof uses Mathlib's connected simple
graph bound after forgetting self-loops and identifying parallel bonds;
the actual half-edge bond count is retained as an upper bound.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
variable {V D : Type*} (M : Molecule V D)

/-- The underlying simple atom graph, used only for the cardinal lower bound. -/
@[expose] def atomGraph : SimpleGraph M.atoms where
  Adj a b := a ≠ b ∧ M.Adj a.1 b.1
  symm := ⟨by rintro a b ⟨hab,h⟩; exact ⟨hab.symm,adj_symmetric M h⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

/-- Actual component paths remain reachable after loops and multiplicities
are forgotten. -/
theorem atomGraph_reachable {u v : V} (h : M.SameComponent u v)
    (hu : u ∈ M.atoms) (hv : v ∈ M.atoms) :
    (atomGraph M).Reachable ⟨u,hu⟩ ⟨v,hv⟩ := by
  induction h with
  | rel u v huv =>
    by_cases he : u = v
    · subst v
      exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable ⟨fun h => he (congrArg Subtype.val h),huv⟩
  | refl u => exact SimpleGraph.Reachable.refl _
  | symm u v huv ih => exact (ih hv hu).symm
  | trans u v z huv hvz ih ih' =>
    have hvm : v ∈ M.atoms := (sameComponent_mem_iff M huv).mp hu
    exact (ih hu hvm).trans (ih' hvm hv)

/-- Every actual bond has a canonical pair of endpoints in the atom subtype. -/
@[expose] def bondEnds (x : D) : Sym2 M.atoms :=
  s(⟨M.atom x,M.atom_mem x⟩,⟨M.atom (M.mate x),M.atom_mem (M.mate x)⟩)

variable [Fintype D]

/-- Simple edges form an image of a subset of the actual directed bonds. -/
theorem atomGraph_edges_le_bonds : Nat.card (atomGraph M).edgeSet ≤ M.bonds.card := by
  classical
  have hsub : (atomGraph M).edgeFinset ⊆ M.bonds.image (bondEnds M) := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ a b =>
      have hab : (atomGraph M).Adj a b := by simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using he
      obtain ⟨_hne,x,hxa,hxb⟩ := hab
      have ha : (⟨M.atom x,M.atom_mem x⟩ : M.atoms) = a := Subtype.ext hxa
      have hb : (⟨M.atom (M.mate x),M.atom_mem (M.mate x)⟩ : M.atoms) = b := Subtype.ext hxb
      cases hout : M.out x
      · refine Finset.mem_image.mpr ⟨M.mate x,?_,?_⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [M.out_mate,hout]; rfl⟩
        · dsimp only [bondEnds]
          simp only [M.mate_mate,hb,ha]
          exact Sym2.eq_swap
      · refine Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hout⟩,?_⟩
        simp only [bondEnds,ha,hb]
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_image_le)
  simpa only [Nat.card_eq_fintype_card,SimpleGraph.card_edgeSet] using hcard

/-- A nonempty connected molecule has at least V-1 actual bonds. -/
theorem card_atoms_le_bonds_add_one (hne : M.atoms.Nonempty)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v) :
    M.atoms.card ≤ M.bonds.card+1 := by
  have : Nonempty M.atoms := by obtain ⟨u,hu⟩ := hne; exact ⟨⟨u,hu⟩⟩
  have hg : (atomGraph M).Connected :=
    ⟨fun u v => atomGraph_reachable M (hconn u.1 u.2 v.1 v.2) u.2 v.2⟩
  have hh := hg.card_vert_le_card_edgeSet_add_one
  have he := atomGraph_edges_le_bonds M
  rw [Nat.card_eq_finsetCard] at hh
  omega

/-- The actual circuit rank of a nonempty connected molecule is nonnegative. -/
theorem circuitRank_nonneg_of_connected (hne : M.atoms.Nonempty)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v) : 0 ≤ M.circuitRank := by
  have hh := card_atoms_le_bonds_add_one M hne hconn
  have hc := numComponents_eq_one M hne hconn
  rw [Molecule.circuitRank,hc]
  norm_num only [Nat.cast_one]
  omega

end WaveTurbulence.Mole
