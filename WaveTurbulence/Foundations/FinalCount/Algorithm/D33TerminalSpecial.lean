/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33SpecialLift
public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33SpecialNeighbors
public import WaveTurbulence.Foundations.FinalCount.Algorithm.SpecialComponentTransport
import Mathlib.Tactic

/-! # The no-new-figure test at the end of a normal double-pair chain -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- In source rule three(c), all other atoms of the current component
have degree four. The negative 3D3-6G test therefore excludes every
special bond of that component after the normal deletion. -/
theorem d33_terminal_component_no_special (M : Molecule V D) (hno : AppbNoLoops M)
    (r : AppbRealization M AppbPatternKind.d33.pattern)
    (hregular : ∀ b ∈ M.atoms, M.SameComponent (r.vertex 1) b →
      b ∉ r.removedAtoms → M.deg b = 4)
    (hn : ¬∃ q : AppbRealization M AppbPatternKind.d33new.pattern,
      q.vertex 1 = r.vertex 1 ∧ q.vertex 2 = r.vertex 2 ∧
      q.vertex 3 = r.vertex 3 ∧ q.vertex 4 = r.vertex 4)
    (x : Degen.RetainedDart M r.removedAtoms)
    (hc : M.SameComponent (r.vertex 1) (M.atom x.val)) : ¬AppbSpecial r.post x := by
  intro hs
  have ht : M.SameComponent (r.vertex 1) (M.atom (M.mate x.val)) :=
    Relation.EqvGen.trans _ _ _ hc (Relation.EqvGen.rel _ _ ⟨x.val,rfl,rfl⟩)
  have hdisplay (b : V) (hb : b ∈ r.post.atoms)
      (hc : M.SameComponent (r.vertex 1) b) (hd : r.post.deg b = 3) :
      b = r.vertex 3 ∨ b = r.vertex 4 := by
    by_cases hi : b ∈ AppbPatternKind.d33.pattern.vertices.image r.vertex
    · exact D33Special.displayed_survivor r hb hi
    · have h4 := hregular b (mem_sdiff.mp hb).1 hc (mem_sdiff.mp hb).2
      have he := r.post_degree_outside b hi
      omega
  have hsrc : M.atom x.val = r.vertex 3 ∨ M.atom x.val = r.vertex 4 :=
    hdisplay _ (r.post.atom_mem x) hc hs.2.1
  have htgt : M.atom (M.mate x.val) = r.vertex 3 ∨ M.atom (M.mate x.val) = r.vertex 4 :=
    hdisplay _ (r.post.atom_mem (r.post.mate x)) ht hs.2.2.1
  have hne := hno x.val
  have he : r.post.ends x = s(r.vertex 3,r.vertex 4) := by
    change s(M.atom x.val,M.atom (M.mate x.val)) = _
    rcases hsrc with hsrc | hsrc <;> rcases htgt with htgt | htgt
    · exact (hne (hsrc.trans htgt.symm)).elim
    · rw [hsrc,htgt]
    · rw [hsrc,htgt,Sym2.eq_swap]
    · exact (hne (hsrc.trans htgt.symm)).elim
  exact no_residual_special_between_boundary_of_no_d33new M hno r hn x he hs

theorem d33_terminal_special_count_le (M : Molecule V D) (hno : AppbNoLoops M)
    (r : AppbRealization M AppbPatternKind.d33.pattern)
    (hregular : ∀ b ∈ M.atoms, M.SameComponent (r.vertex 1) b →
      b ∉ r.removedAtoms → M.deg b = 4)
    (hn : ¬∃ q : AppbRealization M AppbPatternKind.d33new.pattern,
      q.vertex 1 = r.vertex 1 ∧ q.vertex 2 = r.vertex 2 ∧
      q.vertex 3 = r.vertex 3 ∧ q.vertex 4 = r.vertex 4) :
    (appbSpecialBonds r.post).card ≤ (appbSpecialBonds M).card :=
  pattern_special_count_le_of_component_test M .d33 r
    (d33_terminal_component_no_special M hno r hregular hn)

end WaveTurbulence.Mole.AppbAlgorithm
