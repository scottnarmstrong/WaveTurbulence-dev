/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBIncidenceCounts
public import WaveTurbulence.Foundations.FinalCount.AppBBranchConditions
public import WaveTurbulence.Foundations.FinalCount.Degen.BondDeletion
import Mathlib.Tactic

/-! # Actual outgoing incident-bond enumeration at a loop-free atom -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem removed_singleton_eq_incident (M : Molecule V D) (v : V) :
    appbRemovedBonds M {v} = Degen.incidentBondsAt M v := by
  ext x
  simp only [appbRemovedBonds,Degen.incidentBondsAt,Degen.bondsOutAt,Degen.bondsInto,
    mem_filter,mem_union,mem_singleton]
  tauto

theorem incident_card_eq_degree (M : Molecule V D) (hno : AppbNoLoops M) (v : V) :
    (appbRemovedBonds M {v}).card = M.deg v := by
  have hs : Degen.selfBondsAt M v = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨ha,hb⟩ := mem_inter.mp hx
    exact hno x ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm)
  have hh := Degen.card_incident_add_self_eq_deg M v
  rw [hs,card_empty,add_zero] at hh
  rw [removed_singleton_eq_incident]
  exact hh

structure Star (M : Molecule V D) (v : V) (k : ℕ) where
  edge : Fin k ≃ {x // x ∈ appbRemovedBonds M {v}}
  neighbor : Fin k → V
  neighbor_mem : ∀ i,neighbor i ∈ M.atoms
  neighbor_ne : ∀ i,neighbor i ≠ v
  endpoints : ∀ i,M.ends (edge i).val = s(v,neighbor i)

noncomputable def starOfDegree (M : Molecule V D) (hno : AppbNoLoops M)
    (v : V) (k : ℕ) (hd : M.deg v = k) : Star M v k := by
  classical
  let e := (Finset.equivFinOfCardEq ((incident_card_eq_degree M hno v).trans hd)).symm
  let neighbor := fun i : Fin k =>
    if M.atom (e i).val = v then M.atom (M.mate (e i).val) else M.atom (e i).val
  have hend (i : Fin k) : M.ends (e i).val = s(v,neighbor i) := by
    have hi := (mem_filter.mp (e i).property).2
    simp only [mem_singleton] at hi
    by_cases ha : M.atom (e i).val = v
    · simp only [Molecule.ends,neighbor,ha,ite_true]
    · have hb : M.atom (M.mate (e i).val) = v := hi.resolve_left ha
      simp only [Molecule.ends,neighbor,ha,ite_false,hb]
      exact Sym2.eq_swap
  exact {
    edge := e
    neighbor := neighbor
    neighbor_mem := by
      intro i
      unfold neighbor
      split_ifs <;> exact M.atom_mem _
    neighbor_ne := by
      intro i
      unfold neighbor
      split_ifs with ha
      · intro hb
        exact hno (e i).val (ha.trans hb.symm)
      · exact ha
    endpoints := hend
  }

end WaveTurbulence.Mole.AppbAlgorithm
