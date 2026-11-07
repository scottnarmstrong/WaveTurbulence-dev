/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ScanMode
public import WaveTurbulence.Foundations.FinalCount.Algorithm.NormalFineForestTrace
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ClosedSideCircuitRank
public import WaveTurbulence.Foundations.FinalCount.Algorithm.CountingForest
import Mathlib.Tactic

/-! # Defect and bond bookkeeping for forests

`forestDefect` is the forest defect potential and `forestHasBonds` says that a
component of the forest still has a bond.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
universe u v
variable {V : Type v} [DecidableEq V] {d : ℕ} {L γ η c : ℝ} {w : Mom d} {B : ℕ}

/-- Some component has a bond. -/
def ListBonds (l : List (State.{u,v} V)) : Prop := ∃ s ∈ l,s.graph.bonds.Nonempty

noncomputable def forestDefect (F : CountingForest.{u,v} V d L γ η w c B) : ℤ :=
  forestDefectPotential F.graphs

def forestHasBonds (F : CountingForest.{u,v} V d L γ η w c B) : Prop := ListBonds F.graphs

theorem listBonds_edit {pre tail : List (State.{u,v} V)} {s t : State.{u,v} V}
    (h : s.graph.bonds.Nonempty → t.graph.bonds.Nonempty) :
    ListBonds (pre++s::tail) → ListBonds (pre++t::tail) := by
  rintro ⟨x,hx,hb⟩
  rcases List.mem_append.mp hx with h1 | h1
  · exact ⟨x,List.mem_append_left _ h1,hb⟩
  · rcases List.mem_cons.mp h1 with rfl | h2
    · exact ⟨t,by simp,h hb⟩
    · exact ⟨x,List.mem_append_right _ (List.mem_cons_of_mem _ h2),hb⟩

theorem listBonds_discard {pre tail : List (State.{u,v} V)} {s : State.{u,v} V}
    (hs : Terminal s) : ListBonds (pre++s::tail) → ListBonds (pre++tail) := by
  rintro ⟨x,hx,hb⟩
  rcases List.mem_append.mp hx with h1 | h1
  · exact ⟨x,List.mem_append_left _ h1,hb⟩
  · rcases List.mem_cons.mp h1 with rfl | h2
    · exact absurd hs (by unfold Terminal; exact Finset.nonempty_iff_ne_empty.mp hb)
    · exact ⟨x,List.mem_append_right _ h2,hb⟩

theorem listBonds_split {pre tail : List (State.{u,v} V)} (s : State.{u,v} V)
    (S : Finset V) (hS : AppbClosedSide s.graph S) :
    ListBonds (pre++s::tail) → ListBonds (pre++ofMolecule (appbSideMolecule s.graph S hS)::
      ofMolecule (appbSideMolecule s.graph (s.graph.atoms \ S) hS.complement)::tail) := by
  rintro ⟨x,hx,hb⟩
  rcases List.mem_append.mp hx with h1 | h1
  · exact ⟨x,List.mem_append_left _ h1,hb⟩
  · rcases List.mem_cons.mp h1 with rfl | h2
    · have hc := bonds_card_closed_side_add x.graph S hS
      have hp : 0 < x.graph.bonds.card := Finset.card_pos.mpr hb
      by_cases h0 : (appbSideMolecule x.graph S hS).bonds.Nonempty
      · exact ⟨_,List.mem_append_right _ (List.mem_cons_self),h0⟩
      · refine ⟨_,List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self)),?_⟩
        have : (appbSideMolecule x.graph S hS).bonds.card = 0 := by
          by_contra hne; exact h0 (Finset.card_pos.mp (Nat.pos_of_ne_zero hne))
        have h2 : 0 < (appbSideMolecule x.graph (x.graph.atoms \ S) hS.complement).bonds.card := by
          omega
        exact Finset.card_pos.mp h2
    · exact ⟨x,List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h2)),hb⟩

theorem realization_bonds_nonempty {D : Type u} [Fintype D] [DecidableEq D] {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33.pattern) : M.bonds.Nonempty := by
  have h : 0 < AppbPatternKind.d33.pattern.edges.length := by decide
  have := (r.edge ⟨0,h⟩).property
  exact ⟨_,(Finset.mem_filter.mp this).1⟩

theorem forestDefect_edit (pre tail : List (State.{u,v} V)) (s t : State.{u,v} V) :
    forestDefectPotential (pre++t::tail)-forestDefectPotential (pre++s::tail) =
      defectPotential t.graph-defectPotential s.graph := by
  simp only [forestDefectPotential,List.map_append,List.sum_append,List.map_cons,List.sum_cons]
  ring

end WaveTurbulence.Mole.AppbAlgorithm
