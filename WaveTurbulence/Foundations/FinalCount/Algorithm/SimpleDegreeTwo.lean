/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.TwoStarExistence
public import WaveTurbulence.Foundations.FinalCount.AppBPatternMultiplicities
import Mathlib.Tactic

/-! # The actual V2-star statistic in the good-operation count -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A degree-two atom incident to two single bonds, DH23 §10.3.2. -/
def SimpleDegreeTwo (M : Molecule V D) (a : V) : Prop :=
  M.deg a = 2 ∧ ∃ b ∈ M.atoms,∃ c ∈ M.atoms,
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ M.bondsBetween a b = 1 ∧ M.bondsBetween a c = 1

noncomputable def simpleDegreeTwoAtoms (M : Molecule V D) : Finset V := by
  classical
  exact M.atoms.filter (SimpleDegreeTwo M)

theorem Star.simpleDegreeTwo_iff {M : Molecule V D} {v : V} (hv : v ∈ M.atoms)
    (hd : M.deg v = 2) (st : Star M v 2) :
    SimpleDegreeTwo M v ↔ st.neighbor 0 ≠ st.neighbor 1 := by
  classical
  constructor
  · rintro ⟨hdeg,b,hb,c,hc,hab,hac,hbc,hvb,hvc⟩ heq
    let r := st.doubleRealization hv heq
    have hp : M.bondsBetween v (st.neighbor 0) = 2 := by
      have hh := r.bondsBetween_vertices_eq 1 2 (by decide) (by decide)
      exact hh.trans (by decide)
    obtain ⟨a,ha,he⟩ := r.neighbor_mem_vertices 1 (by decide) (by change 0 < M.bondsBetween v b; omega)
    have ha' : a = 1 ∨ a = 2 := by
      have hV : AppbPatternKind.r21.pattern.vertices = {1,2} := by decide
      simpa only [hV,mem_insert,mem_singleton] using ha
    rcases ha' with rfl | rfl
    · exact hab he.symm
    · change b = st.neighbor 0 at he
      rw [he,hp] at hvb
      omega
  · intro hne
    let r := st.singleRealization hv hne
    have h1 : M.bondsBetween v (st.neighbor 0) = 1 :=
      (r.bondsBetween_vertices_eq 1 2 (by decide) (by decide)).trans (by decide)
    have h2 : M.bondsBetween v (st.neighbor 1) = 1 :=
      (r.bondsBetween_vertices_eq 1 3 (by decide) (by decide)).trans (by decide)
    exact ⟨hd,st.neighbor 0,st.neighbor_mem 0,st.neighbor 1,st.neighbor_mem 1,
      (st.neighbor_ne 0).symm,(st.neighbor_ne 1).symm,hne,h1,h2⟩

theorem simpleDegreeTwoAtoms_le_degreeTwo (M : Molecule V D) :
    (simpleDegreeTwoAtoms M).card ≤ (appbDegreeAtoms M 2).card := by
  classical
  apply card_le_card
  intro v hv
  exact mem_filter.mpr ⟨(mem_filter.mp hv).1,(mem_filter.mp hv).2.1⟩

end WaveTurbulence.Mole.AppbAlgorithm
