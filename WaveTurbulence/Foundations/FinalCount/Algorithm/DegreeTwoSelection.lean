/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.TwoChainExistence
public import WaveTurbulence.Foundations.FinalCount.Algorithm.TwoStarExistence
public import WaveTurbulence.Foundations.FinalCount.Algorithm.StarReindex
import Mathlib.Tactic

/-! # Exhaustive selection of the actual fine-operation groups in rule seven -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The geometric alternatives of DH23 Appendix B rule seven. All stored
statistic premises are old degrees at actual figure vertices. -/
inductive DegreeTwoSelection (M : Molecule V D) : Prop
  | doubleFour (r : AppbRealization M AppbPatternKind.r21.pattern)
      (h : M.deg (r.vertex 2) = 4) : DegreeTwoSelection M
  | singleFour (r : AppbRealization M AppbPatternKind.r22.pattern)
      (h : M.deg (r.vertex 2) = 4)
      (h3 : M.deg (r.vertex 3) = 2 ∨ M.deg (r.vertex 3) = 4) : DegreeTwoSelection M
  | triangle (r : AppbRealization M AppbPatternKind.r23triangle.pattern) : DegreeTwoSelection M
  | common (r : AppbRealization M appbR23Common) : DegreeTwoSelection M
  | chain (r : AppbRealization M AppbPatternKind.r23.pattern) : DegreeTwoSelection M
  | doubleTwo (r : AppbRealization M AppbPatternKind.r24.pattern) : DegreeTwoSelection M

/-- Rule seven is exhaustive on a nonterminal molecule once bridges and
all degree-three atoms have been excluded. -/
theorem exists_degree_two_selection (M : Molecule V D) (hM : M.IsMolecule)
    (hno : AppbNoLoops M) (hb : ∀ e : D,¬Degen.IsBridge M e)
    (h3 : ∀ a ∈ M.atoms,M.deg a ≠ 3) (hne : M.bonds.Nonempty) :
    DegreeTwoSelection M := by
  classical
  obtain ⟨a,ha,hda⟩ := exists_degree_two_or_three_of_no_bridges M hM hno hb hne
  have hda : M.deg a = 2 := hda.resolve_right (h3 a ha)
  let st := starOfDegree M hno a 2 hda
  have hd0 := st.neighbor_degree_two_or_four hM hno hb h3 0
  have hd1 := st.neighbor_degree_two_or_four hM hno hb h3 1
  by_cases heq : st.neighbor 0 = st.neighbor 1
  · rcases hd0 with hd0 | hd0
    · exact .doubleTwo (st.closedDoubleRealization ha heq hd0)
    · exact .doubleFour (st.doubleRealization ha heq) hd0
  · by_cases h4 : M.deg (st.neighbor 0) = 4
    · exact .singleFour (st.singleRealization ha heq) h4 hd1
    · by_cases h4' : M.deg (st.neighbor 1) = 4
      · let st' := st.reindex (Equiv.swap 0 1)
        have hs0 : st'.neighbor 0 = st.neighbor 1 := by simp [st',Star.reindex]
        have hs1 : st'.neighbor 1 = st.neighbor 0 := by simp [st',Star.reindex]
        have hn : st'.neighbor 0 ≠ st'.neighbor 1 := by rw [hs0,hs1]; exact Ne.symm heq
        apply DegreeTwoSelection.singleFour (st'.singleRealization ha hn)
        · change M.deg (st'.neighbor 0) = 4
          rw [hs0]; exact h4'
        · change M.deg (st'.neighbor 1) = 2 ∨ M.deg (st'.neighbor 1) = 4
          rw [hs1]; exact hd0
      · have h2 : M.deg (st.neighbor 0) = 2 := hd0.resolve_right h4
        have h2' : M.deg (st.neighbor 1) = 2 := hd1.resolve_right h4'
        rcases exists_two_chain_realization M hno ha hda st heq h2 h2' with ht | hc | ho
        · obtain ⟨r,_⟩ := ht; exact .triangle r
        · obtain ⟨r,_⟩ := hc; exact .common r
        · obtain ⟨r,_⟩ := ho; exact .chain r

end WaveTurbulence.Mole.AppbAlgorithm
