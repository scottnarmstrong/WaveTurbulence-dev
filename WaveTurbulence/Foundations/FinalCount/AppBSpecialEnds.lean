/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBFiveStarFrames
public import WaveTurbulence.Foundations.FinalCount.AppBR32SplitSide
import Mathlib.Tactic

/-! # Both interchangeable ends of a residual special bond -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace AppbRealization
variable {M : Molecule V D} (s : AppbRealization M AppbPatternKind.s33new3.pattern)

def specialAtom (b : Bool) : V := s.vertex (if b then 2 else 1)
def specialCompanion (b : Bool) : V := s.vertex (if b then 4 else 3)
def specialFirst (_s : AppbRealization M AppbPatternKind.s33new3.pattern) (b : Bool) : Fin AppbPatternKind.s33new3.pattern.edges.length := if b then ⟨3,by decide⟩ else ⟨1,by decide⟩
def specialSecond (_s : AppbRealization M AppbPatternKind.s33new3.pattern) (b : Bool) : Fin AppbPatternKind.s33new3.pattern.edges.length := if b then ⟨4,by decide⟩ else ⟨2,by decide⟩

def specialFrame (b : Bool) : AppbTripleFrame s (s.specialAtom b) := by
  cases b
  · exact appbFiveFirst s rfl (s.vertex 1) (appb_s33_first_incidence .s33new3 (by decide) s)
  · exact appbFiveSecond s rfl (s.vertex 2) (appb_s33_second_incidence .s33new3 (by decide) s)

theorem specialFrame_indices (b : Bool) :
    (s.specialFrame b).index 0 = ⟨0,by decide⟩ ∧
    (s.specialFrame b).index 1 = s.specialFirst b ∧ (s.specialFrame b).index 2 = s.specialSecond b := by
  cases b <;> exact ⟨rfl,rfl,rfl⟩

theorem special_bridge_ends (b : Bool) :
    M.ends (s.edge ⟨0,by decide⟩).val = s(s.specialAtom b,s.specialAtom (!b)) := by
  cases b
  · exact s.endpoints ⟨0,by decide⟩
  · exact (s.endpoints ⟨0,by decide⟩).trans (Sym2.eq_swap)

theorem special_first_ends (b : Bool) :
    M.ends (s.edge (s.specialFirst b)).val = s(s.specialAtom b,s.specialCompanion b) := by
  cases b
  · exact s.endpoints ⟨1,by decide⟩
  · exact s.endpoints ⟨3,by decide⟩

theorem special_second_ends (b : Bool) :
    M.ends (s.edge (s.specialSecond b)).val = s(s.specialAtom b,s.specialCompanion b) := by
  cases b
  · exact s.endpoints ⟨2,by decide⟩
  · exact s.endpoints ⟨4,by decide⟩

theorem special_atoms_mem (b : Bool) : s.specialAtom b ∈ M.atoms ∧ s.specialCompanion b ∈ M.atoms := by
  cases b
  all_goals constructor <;> exact s.vertex_mem _ (by decide)

theorem special_atom_removed (b : Bool) : s.specialAtom b ∈ s.removedAtoms := by
  cases b
  all_goals exact mem_image_of_mem _ (by decide)

theorem special_atom_ne_companion (b : Bool) : s.specialAtom b ≠ s.specialCompanion b := by
  cases b
  · exact (s.vertex_eq_iff 1 3 (by decide) (by decide)).not.mpr (by decide)
  · exact (s.vertex_eq_iff 2 4 (by decide) (by decide)).not.mpr (by decide)

end AppbRealization

theorem appb_r32_choose_special_end {M : Molecule V D}
    (s : AppbRealization M AppbPatternKind.s33new3.pattern) (S : Finset V) (h : AppbR32SideLabels s S) :
    ∃ b : Bool,s.specialAtom b ∈ S ∧ s.specialAtom (!b) ∉ S ∧
      s.specialCompanion b ∈ S ∧ s.specialCompanion (!b) ∉ S := by
  rcases h with h | h
  · exact ⟨false,h⟩
  · exact ⟨true,h⟩

end WaveTurbulence.Mole
