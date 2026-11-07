/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.TwoStarPatterns
public import WaveTurbulence.Foundations.FinalCount.Algorithm.DoubleDegreeTwo
public import WaveTurbulence.Foundations.FinalCount.Algorithm.DegreeOneBridge
import Mathlib.Tactic

/-! # Existence of the actual two-bond configurations used by rule seven -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem exists_two_star_realization (M : Molecule V D) (hno : AppbNoLoops M)
    {v : V} (hv : v ∈ M.atoms) (hd : M.deg v = 2) :
    (∃ r : AppbRealization M AppbPatternKind.r21.pattern,r.vertex 1 = v) ∨
      (∃ r : AppbRealization M AppbPatternKind.r22.pattern,r.vertex 1 = v) := by
  classical
  let st := starOfDegree M hno v 2 hd
  by_cases heq : st.neighbor 0 = st.neighbor 1
  · exact Or.inl ⟨st.doubleRealization hv heq,rfl⟩
  · exact Or.inr ⟨st.singleRealization hv heq,rfl⟩

theorem Star.neighbor_degree_pos {M : Molecule V D} {v : V} {k : ℕ}
    (st : Star M v k) (i : Fin k) : 0 < M.deg (st.neighbor i) := by
  rcases Sym2.eq_iff.mp (st.endpoints i) with h | h
  · apply card_pos.mpr
    exact ⟨M.mate (st.edge i).val,mem_filter.mpr ⟨mem_univ _,h.2⟩⟩
  · apply card_pos.mpr
    exact ⟨(st.edge i).val,mem_filter.mpr ⟨mem_univ _,h.1⟩⟩

theorem Star.neighbor_degree_two_or_four {M : Molecule V D} (hM : M.IsMolecule)
    (hno : AppbNoLoops M) (hb : ∀ e : D,¬Degen.IsBridge M e)
    (h3 : ∀ a ∈ M.atoms,M.deg a ≠ 3) {v : V} {k : ℕ} (st : Star M v k) (i : Fin k) :
    M.deg (st.neighbor i) = 2 ∨ M.deg (st.neighbor i) = 4 := by
  have hpos := st.neighbor_degree_pos i
  have hcap := deg_le_four M hM (st.neighbor_mem i)
  have hn3 := h3 _ (st.neighbor_mem i)
  have hn1 : M.deg (st.neighbor i) ≠ 1 := by
    intro he
    obtain ⟨e,he⟩ := exists_bridge_of_degree_one M hno he
    exact hb e he
  omega

end WaveTurbulence.Mole.AppbAlgorithm
