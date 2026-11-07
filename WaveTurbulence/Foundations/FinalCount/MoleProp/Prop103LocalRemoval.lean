/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103OrdinaryStep
import Mathlib.Tactic

/-! # Actual low-degree rank loss with only local bridge exclusion -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Only bridges incident to the removed atom matter for its newly bounded
components. Unrelated bridges in the graph are allowed. -/
theorem two_mul_newComponents_le_of_no_incident_bridges (M : Molecule V D) (v : V)
    (hnb : ∀ e, M.atom e = v → ¬ IsBridge M e) :
    2 * (newComponents M {v}).card ≤ M.deg v := by
  classical
  have htwo (S : Finset V) (hS : S ∈ newComponents M {v}) :
      2 ≤ (boundaryDarts M S).card := by
    have hmem := mem_filter.mp hS
    have hn := hmem.2
    by_contra hlt
    have hc : (boundaryDarts M S).card = 1 := by
      have hp := card_pos.mpr hn
      omega
    obtain ⟨e,he⟩ := card_eq_one.mp hc
    have heb : IsBridge M e := isBridge_of_single_boundary M S he
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hmem.1
    have hem : e ∈ boundaryDarts M (residualComponent M {v} a) := by rw [he]; simp
    have hend := residual_boundary_ends_in_removed M {v} a hem
    have hv : M.atom (M.mate e) = v := by simpa only [mem_singleton] using hend
    exact hnb (M.mate e) hv ((isBridge_mate_iff M e).mpr heb)
  have hs : (∑ _S ∈ newComponents M {v}, (2 : ℕ)) ≤
      ∑ S ∈ newComponents M {v}, (boundaryDarts M S).card := sum_le_sum htwo
  have hu := sum_newComponents_boundary_card_le M ({v} : Finset V)
  have hb := boundary_singleton_card_le_degree M v
  have hc : (∑ _S ∈ newComponents M {v}, (2 : ℕ)) = 2 * (newComponents M {v}).card := by
    simp [sum_const,Nat.mul_comm]
  rw [hc] at hs
  omega

/-- A degree-two atom with no incident bridge loses exactly one circuit,
including in a disconnected graph with bridges elsewhere. -/
theorem circuitRank_erase_two_of_no_incident_bridges (M : Molecule V D)
    (hloop : ∀ e, M.atom e ≠ M.atom (M.mate e)) {v : V} (hv : v ∈ M.atoms)
    (hv2 : M.deg v = 2) (hnb : ∀ e, M.atom e = v → ¬ IsBridge M e) :
    (eraseAtoms M {v}).circuitRank = M.circuitRank - 1 := by
  have hp := newComponents_card_pos_of_degree_pos M hloop hv (by omega)
  have hu := two_mul_newComponents_le_of_no_incident_bridges M v hnb
  have hc : (newComponents M {v}).card = 1 := by omega
  have hi := incident_card_eq_deg_of_loopless M hloop v
  have hχ := circuitRank_erase_singleton_sub_general M hv
  rw [hc,hi,hv2] at hχ
  omega

end WaveTurbulence.MoleProp
