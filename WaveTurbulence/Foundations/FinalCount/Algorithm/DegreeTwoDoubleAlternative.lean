/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.DoubleSimpleDegreeTwo
import Mathlib.Tactic

/-! # A nonsimple degree-two atom has an actual double-bond neighbor -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem degree_two_not_simple_iff_double (M : Molecule V D) (hno : AppbNoLoops M)
    {a : V} (ha : a ∈ M.atoms) (hd : M.deg a = 2) :
    ¬SimpleDegreeTwo M a ↔ ∃ b ∈ M.atoms,b ≠ a ∧ M.bondsBetween a b = 2 := by
  classical
  constructor
  · intro hn
    let st := starOfDegree M hno a 2 hd
    have he : st.neighbor 0 = st.neighbor 1 := by
      by_contra hne
      exact hn ((st.simpleDegreeTwo_iff ha hd).mpr hne)
    let r := st.doubleRealization ha he
    have hm : M.bondsBetween a (st.neighbor 0) = 2 :=
      (r.bondsBetween_vertices_eq 1 2 (by decide) (by decide)).trans (by decide)
    exact ⟨st.neighbor 0,st.neighbor_mem 0,st.neighbor_ne 0,hm⟩
  · rintro ⟨b,hb,hne,hm⟩
    exact not_simpleDegreeTwo_of_double M hne.symm hd hm

end WaveTurbulence.Mole.AppbAlgorithm
