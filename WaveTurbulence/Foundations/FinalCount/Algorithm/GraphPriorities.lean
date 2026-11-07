/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.SinglePairPriority
public import WaveTurbulence.Foundations.FinalCount.Algorithm.DoublePairExistence
public import WaveTurbulence.Foundations.FinalCount.Algorithm.D34Classification
public import WaveTurbulence.Foundations.FinalCount.Algorithm.S32Classification
public import WaveTurbulence.Foundations.FinalCount.Algorithm.PriorityTests
public import WaveTurbulence.Foundations.FinalCount.Algorithm.DegreeTwoSelection
import Mathlib.Tactic

/-! # Exhaustive actual graph priorities for DH23 Appendix B

This is the geometric dispatch before the source's direction and decoration
tests and its ladder-continuation subloop. It is not a replacement for that
subloop or for the good-operation count.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

inductive GraphPriority (M : Molecule V D) : Prop
  | bridge (e : D) (h : Degen.IsBridge M e) : GraphPriority M
  | single (hb : ∀ e : D,¬Degen.IsBridge M e) (h : RuleTwoFigure M) : GraphPriority M
  | double (hb : ∀ e : D,¬Degen.IsBridge M e) (h1 : ¬HasDegreeThreePair M 1)
      (h : Nonempty (AppbRealization M AppbPatternKind.d33.pattern) ∨
        Nonempty (AppbRealization M AppbPatternKind.d33same.pattern)) : GraphPriority M
  | mixedDouble (hb : ∀ e : D,¬Degen.IsBridge M e)
      (h1 : ¬HasDegreeThreePair M 1) (h2 : ¬HasDegreeThreePair M 2)
      (h : D34Figure M) : GraphPriority M
  | mixedSingle (hb : ∀ e : D,¬Degen.IsBridge M e)
      (h1 : ¬HasDegreeThreePair M 1) (h2 : ¬HasDegreeThreePair M 2)
      (h4 : ¬HasThreeFourDouble M) (h : S32Figure M) : GraphPriority M
  | regular (hb : ∀ e : D,¬Degen.IsBridge M e)
      (h1 : ¬HasDegreeThreePair M 1) (h2 : ¬HasDegreeThreePair M 2)
      (h4 : ¬HasThreeFourDouble M) (h32 : ¬HasThreeTwo M)
      (r : AppbRealization M AppbPatternKind.r3.pattern)
      (hd2 : M.deg (r.vertex 2) = 4) (hd3 : M.deg (r.vertex 3) = 4)
      (hd4 : M.deg (r.vertex 4) = 4) : GraphPriority M
  | fine (hb : ∀ e : D,¬Degen.IsBridge M e)
      (h3 : ∀ a ∈ M.atoms,M.deg a ≠ 3) (h : DegreeTwoSelection M) : GraphPriority M

/-- DH23 Appendix B rules one through seven: every nonterminal molecule
has the next geometric group, with all earlier negative tests retained. -/
theorem exists_graph_priority (M : Molecule V D) (hM : M.IsMolecule)
    (hno : AppbNoLoops M) (hnt : AppbNoTripleBonds M) (hne : M.bonds.Nonempty) :
    GraphPriority M := by
  classical
  by_cases hb : ∃ e : D,Degen.IsBridge M e
  · obtain ⟨e,he⟩ := hb
    exact .bridge e he
  have hb' : ∀ e : D,¬Degen.IsBridge M e := fun e he => hb ⟨e,he⟩
  by_cases h331 : HasDegreeThreePair M 1
  · obtain ⟨a,ha,b,hb,hdA,hdB,hab,hm⟩ := h331
    exact .single hb' (rule_two_figure M (exists_single_pair_figure M hno ha hb hab hdA hdB hm))
  by_cases h332 : HasDegreeThreePair M 2
  · obtain ⟨a,ha,b,hb,hdA,hdB,hab,hm⟩ := h332
    rcases exists_double_pair_realization M hno ha hb hab hdA hdB hm with h | h
    · obtain ⟨r,_⟩ := h
      exact .double hb' h331 (Or.inl ⟨r⟩)
    · obtain ⟨r,_⟩ := h
      exact .double hb' h331 (Or.inr ⟨r⟩)
  by_cases h34 : HasThreeFourDouble M
  · obtain ⟨a,ha,b,hb,hdA,hdB,hab,hm⟩ := h34
    exact .mixedDouble hb' h331 h332 (exists_d34_figure M hno ha hb hab hdA hdB hm)
  by_cases h32 : HasThreeTwo M
  · obtain ⟨a,ha,b,hb,hdA,hdB,hab,hm⟩ := h32
    exact .mixedSingle hb' h331 h332 h34 (exists_s32_figure M hno hnt hb' ha hb hab hdA hdB hm)
  by_cases h3 : ∃ a ∈ M.atoms,M.deg a = 3
  · obtain ⟨a,ha,hdA⟩ := h3
    obtain ⟨r,_,h2,h3,h4⟩ := rule_six_star M hM hno hnt hb' h331 h332 h34 h32 ha hdA
    exact .regular hb' h331 h332 h34 h32 r h2 h3 h4
  have h3' : ∀ a ∈ M.atoms,M.deg a ≠ 3 := fun a ha hd => h3 ⟨a,ha,hd⟩
  exact .fine hb' h3' (exists_degree_two_selection M hM hno hb' h3' hne)

end WaveTurbulence.Mole.AppbAlgorithm
