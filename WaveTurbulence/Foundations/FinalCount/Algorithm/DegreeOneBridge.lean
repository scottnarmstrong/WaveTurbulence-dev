/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.DefectAtom
public import WaveTurbulence.Foundations.FinalCount.AppBBranchConditions
public import WaveTurbulence.Foundations.Molecule.Degen.Bridges
import Mathlib.Tactic

/-! # Degree-one defects are handled by the source's first-priority bridge rule -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem exists_bridge_of_degree_one (M : Molecule V D) (hno : AppbNoLoops M)
    {v : V} (hd : M.deg v = 1) : ∃ e : D,Degen.IsBridge M e := by
  classical
  have heq : Degen.boundaryDarts M {v} = M.dartsAt v := by
    ext x
    simp only [Degen.boundaryDarts,Molecule.dartsAt,mem_filter,mem_univ,true_and,mem_singleton]
    constructor
    · exact And.left
    · intro hx
      exact ⟨hx,fun hy => hno x (hx.trans hy.symm)⟩
  have hc : (Degen.boundaryDarts M {v}).card = 1 := by rw [heq]; exact hd
  obtain ⟨e,he⟩ := card_eq_one.mp hc
  exact ⟨e,Degen.isBridge_of_single_boundary M {v} he⟩

theorem exists_degree_two_or_three_of_no_bridges (M : Molecule V D) (hM : M.IsMolecule)
    (hno : AppbNoLoops M) (hb : ∀ e : D,¬Degen.IsBridge M e) (hne : M.bonds.Nonempty) :
    ∃ v ∈ M.atoms,M.deg v = 2 ∨ M.deg v = 3 := by
  obtain ⟨v,hv,hp,hle⟩ := exists_nonisolated_defect M hM hne
  have hn : M.deg v ≠ 1 := by
    intro he
    obtain ⟨e,he⟩ := exists_bridge_of_degree_one M hno he
    exact hb e he
  exact ⟨v,hv,by omega⟩

end WaveTurbulence.Mole.AppbAlgorithm
