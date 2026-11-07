/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ThreeStarPattern
public import WaveTurbulence.Foundations.FinalCount.Algorithm.StarSingleBonds
public import WaveTurbulence.Foundations.FinalCount.Algorithm.TwoStarExistence
import Mathlib.Tactic

/-! # Actual graph predicates for the source loop's degree-three priorities -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Rule two or three: the multiplicity is exactly one or two. -/
def HasDegreeThreePair (M : Molecule V D) (n : ℕ) : Prop :=
  ∃ a ∈ M.atoms, ∃ b ∈ M.atoms,
    M.deg a = 3 ∧ M.deg b = 3 ∧ a ≠ b ∧ M.bondsBetween a b = n

/-- Rule four, after degree-three pairs have been excluded. -/
def HasThreeFourDouble (M : Molecule V D) : Prop :=
  ∃ a ∈ M.atoms, ∃ b ∈ M.atoms,
    M.deg a = 3 ∧ M.deg b = 4 ∧ a ≠ b ∧ M.bondsBetween a b = 2

/-- Rule five: any positive bond multiplicity to a degree-two atom. -/
def HasThreeTwo (M : Molecule V D) : Prop :=
  ∃ a ∈ M.atoms, ∃ b ∈ M.atoms,
    M.deg a = 3 ∧ M.deg b = 2 ∧ a ≠ b ∧ 0 < M.bondsBetween a b

theorem Star.bondsBetween_neighbor_pos {M : Molecule V D} {a : V} {k : ℕ}
    (st : Star M a k) (i : Fin k) : 0 < M.bondsBetween a (st.neighbor i) := by
  classical
  rw [st.bondsBetween_eq_neighbor_count]
  exact Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩

/-- The fallback in rule six follows from the earlier negative graph tests.
Its distinct degree-four neighbors are conclusions of those tests. -/
theorem rule_six_star (M : Molecule V D) (hM : M.IsMolecule)
    (hno : AppbNoLoops M) (hnt : AppbNoTripleBonds M)
    (hb : ∀ e : D,¬Degen.IsBridge M e)
    (h331 : ¬HasDegreeThreePair M 1) (h332 : ¬HasDegreeThreePair M 2)
    (h34 : ¬HasThreeFourDouble M) (h32 : ¬HasThreeTwo M)
    {a : V} (ha : a ∈ M.atoms) (hd : M.deg a = 3) :
    ∃ r : AppbRealization M AppbPatternKind.r3.pattern,
      r.vertex 1 = a ∧ M.deg (r.vertex 2) = 4 ∧
        M.deg (r.vertex 3) = 4 ∧ M.deg (r.vertex 4) = 4 := by
  classical
  let st := starOfDegree M hno a 3 hd
  have hdeg (i : Fin 3) : M.deg (st.neighbor i) = 4 := by
    have hp := st.neighbor_degree_pos i
    have hcap := deg_le_four M hM (st.neighbor_mem i)
    have hbp := st.bondsBetween_neighbor_pos i
    have hbc := hnt a ha _ (st.neighbor_mem i) (st.neighbor_ne i).symm
    have hn1 : M.deg (st.neighbor i) ≠ 1 := by
      intro hh
      obtain ⟨e,he⟩ := exists_bridge_of_degree_one M hno hh
      exact hb e he
    have hn2 : M.deg (st.neighbor i) ≠ 2 := by
      intro hh
      exact h32 ⟨a,ha,_,st.neighbor_mem i,hd,hh,(st.neighbor_ne i).symm,hbp⟩
    have hn3 : M.deg (st.neighbor i) ≠ 3 := by
      intro hh
      have hm : M.bondsBetween a (st.neighbor i) = 1 ∨
          M.bondsBetween a (st.neighbor i) = 2 := by omega
      rcases hm with hm | hm
      · exact h331 ⟨a,ha,_,st.neighbor_mem i,hd,hh,(st.neighbor_ne i).symm,hm⟩
      · exact h332 ⟨a,ha,_,st.neighbor_mem i,hd,hh,(st.neighbor_ne i).symm,hm⟩
    omega
  have hs (i : Fin 3) : M.bondsBetween a (st.neighbor i) ≤ 1 := by
    have hbc := hnt a ha _ (st.neighbor_mem i) (st.neighbor_ne i).symm
    have hn : M.bondsBetween a (st.neighbor i) ≠ 2 := by
      intro hh
      exact h34 ⟨a,ha,_,st.neighbor_mem i,hd,hdeg i,(st.neighbor_ne i).symm,hh⟩
    omega
  exact ⟨st.threeRealization ha (st.neighbor_injective_of_single hs),rfl,hdeg 0,hdeg 1,hdeg 2⟩

end WaveTurbulence.Mole.AppbAlgorithm
