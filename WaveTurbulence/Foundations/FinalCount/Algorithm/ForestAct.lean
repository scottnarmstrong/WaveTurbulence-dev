/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.GeometricPotentialBound
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ChargedTrace
public import WaveTurbulence.Foundations.FinalCount.Algorithm.PriorityTests
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ComponentStatistics
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ClosedSideMolecule
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ClosedSideBonds
public import WaveTurbulence.Foundations.FinalCount.Algorithm.DoublePairWitness
public import WaveTurbulence.Foundations.FinalCount.Algorithm.Terminal
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ClosedSideInvariants
import Mathlib.Tactic

/-! # The active-link accounting of a state: potential plus structural pending slack

`pendingSlack s` is `20` exactly when `s` has a bond and no degree-three double pair.
It is a function of the graph only. It pays the (at most two units of) active-link
potential lost by a terminal normal rung, whose output has exactly this shape
(`terminal_rung_next_priority`); it never needs a scan mode.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
universe u v
variable {V : Type v} [DecidableEq V]

noncomputable def pendingSlack (s : State.{u,v} V) : ℤ := by
  classical exact if s.graph.bonds.Nonempty ∧ ¬HasDegreeThreePair s.graph 2 then 20 else 0

noncomputable def stateAct (s : State.{u,v} V) : ℤ := activeLinkPotential s.graph+pendingSlack s

theorem pendingSlack_nonneg (s : State.{u,v} V) : 0 ≤ pendingSlack s := by
  unfold pendingSlack; split_ifs <;> norm_num

theorem pendingSlack_le (s : State.{u,v} V) : pendingSlack s ≤ 20 := by
  unfold pendingSlack; split_ifs <;> norm_num

theorem pendingSlack_of_pair (s : State.{u,v} V) (h : HasDegreeThreePair s.graph 2) :
    pendingSlack s = 0 := by
  unfold pendingSlack; rw [if_neg]; exact fun hh => hh.2 h

theorem pendingSlack_of_nopair (s : State.{u,v} V) (hb : s.graph.bonds.Nonempty)
    (h : ¬HasDegreeThreePair s.graph 2) : pendingSlack s = 20 := by
  unfold pendingSlack; rw [if_pos ⟨hb,h⟩]

theorem pendingSlack_of_terminal (s : State.{u,v} V) (h : Terminal s) : pendingSlack s = 0 := by
  unfold pendingSlack; rw [if_neg]
  rintro ⟨hb,-⟩
  exact Finset.nonempty_iff_ne_empty.mp hb h

/-- One geometric step loses at most `20` of active potential and `20` of slack. -/
theorem stateAct_le_step {s t : State.{u,v} V} (h : GeometricStep s t)
    (hM : s.graph.IsMolecule) (hN : t.graph.IsMolecule) : stateAct s ≤ stateAct t+40 := by
  have h1 := h.activePotential_drop_le hM hN
  have h2 := pendingSlack_le s
  have h3 := pendingSlack_nonneg t
  unfold stateAct; omega

theorem stateAct_counted {s t : State.{u,v} V} (h : GeometricStep s t)
    (hM : s.graph.IsMolecule) (hN : t.graph.IsMolecule) (c : ℤ) (hc : 1 ≤ c) :
    stateAct s ≤ stateAct t+60*c := by
  have := stateAct_le_step h hM hN
  linarith only [this,hc]

theorem stateAct_le_two {s t z : State.{u,v} V} (h₁ : GeometricStep s t) (h₂ : GeometricStep t z)
    (hM : s.graph.IsMolecule) (hN : t.graph.IsMolecule) (hZ : z.graph.IsMolecule) :
    stateAct s ≤ stateAct z+60 := by
  have h1 := h₁.activePotential_drop_le hM hN
  have h2 := h₂.activePotential_drop_le hN hZ
  have h3 := pendingSlack_le s
  have h4 := pendingSlack_nonneg z
  unfold stateAct; omega

/-- A graph edit with no active loss from a state carrying no slack. -/
theorem stateAct_le_of_noloss {s t : State.{u,v} V} (h : activeLinkPotential s.graph ≤ activeLinkPotential t.graph)
    (hs : pendingSlack s = 0) : stateAct s ≤ stateAct t := by
  have := pendingSlack_nonneg t
  unfold stateAct; omega

/-- A terminal rung: a loss of at most `20` into a nonterminal state with no double pair. -/
theorem stateAct_le_of_terminal_rung {s t : State.{u,v} V}
    (h : activeLinkPotential s.graph ≤ activeLinkPotential t.graph+20)
    (hs : pendingSlack s = 0)
    (hb : t.graph.bonds.Nonempty) (hn : ¬HasDegreeThreePair t.graph 2) : stateAct s ≤ stateAct t := by
  have := pendingSlack_of_nopair t hb hn
  unfold stateAct; omega

theorem stateAct_terminal {s : State.{u,v} V} (h : Terminal s) : stateAct s = 0 := by
  unfold stateAct
  rw [pendingSlack_of_terminal s h,activeLinkPotential_terminal s.graph h]; rfl

theorem pendingSlack_split_le (s : State.{u,v} V) (S : Finset V) (hS : AppbClosedSide s.graph S)
    (hb : s.graph.bonds.Nonempty) :
    pendingSlack s ≤ pendingSlack (ofMolecule (appbSideMolecule s.graph S hS))+
      pendingSlack (ofMolecule (appbSideMolecule s.graph (s.graph.atoms \ S) hS.complement)) := by
  have h0 := pendingSlack_nonneg (ofMolecule (appbSideMolecule s.graph S hS))
  have h1 := pendingSlack_nonneg (ofMolecule (appbSideMolecule s.graph (s.graph.atoms \ S) hS.complement))
  by_cases hp : HasDegreeThreePair s.graph 2
  · rw [pendingSlack_of_pair s hp]; omega
  · have e := pendingSlack_of_nopair s hb hp
    rw [e]
    have hcard := bonds_card_closed_side_add s.graph S hS
    have hpos : 0 < s.graph.bonds.card := Finset.card_pos.mpr hb
    have nopair : ∀ T (hT : AppbClosedSide s.graph T),
        ¬HasDegreeThreePair (appbSideMolecule s.graph T hT) 2 := by
      rintro T hT ⟨a,ha,b,hb',hda,hdb,hab,hm⟩
      apply hp
      refine ⟨a,hT.subset_atoms ha,b,hT.subset_atoms hb',?_,?_,hab,?_⟩
      · rw [← degree_closed_side s.graph T hT ha]; exact hda
      · rw [← degree_closed_side s.graph T hT hb']; exact hdb
      · rw [← bondsBetween_closed_side s.graph T hT ha hb']; exact hm
    by_cases hL : (appbSideMolecule s.graph S hS).bonds.Nonempty
    · rw [pendingSlack_of_nopair (ofMolecule (appbSideMolecule s.graph S hS)) hL (nopair S hS)]
      omega
    · have hR : (appbSideMolecule s.graph (s.graph.atoms \ S) hS.complement).bonds.Nonempty := by
        by_contra hR
        have a1 : (appbSideMolecule s.graph S hS).bonds.card = 0 := by
          simpa [Finset.not_nonempty_iff_eq_empty] using hL
        have a2 : (appbSideMolecule s.graph (s.graph.atoms \ S) hS.complement).bonds.card = 0 := by
          simpa [Finset.not_nonempty_iff_eq_empty] using hR
        omega
      rw [pendingSlack_of_nopair (ofMolecule (appbSideMolecule s.graph (s.graph.atoms \ S) hS.complement)) hR
        (nopair _ hS.complement)]
      omega

theorem stateAct_split_le (s : State.{u,v} V) (S : Finset V) (hS : AppbClosedSide s.graph S) :
    stateAct s ≤ stateAct (ofMolecule (appbSideMolecule s.graph S hS))+
      stateAct (ofMolecule (appbSideMolecule s.graph (s.graph.atoms \ S) hS.complement)) := by
  have hadd := activeLinkPotential_closed_side_add s.graph S hS
  by_cases hb : s.graph.bonds.Nonempty
  · have := pendingSlack_split_le s S hS hb
    unfold stateAct
    change activeLinkPotential s.graph+pendingSlack s ≤ (activeLinkPotential (appbSideMolecule s.graph S hS)+_)+
      (activeLinkPotential (appbSideMolecule s.graph (s.graph.atoms \ S) hS.complement)+_)
    omega
  · have hs : pendingSlack s = 0 := by
      unfold pendingSlack; rw [if_neg]; exact fun h => hb h.1
    have := pendingSlack_nonneg (ofMolecule (appbSideMolecule s.graph S hS))
    have := pendingSlack_nonneg (ofMolecule (appbSideMolecule s.graph (s.graph.atoms \ S) hS.complement))
    unfold stateAct
    change activeLinkPotential s.graph+pendingSlack s ≤ (activeLinkPotential (appbSideMolecule s.graph S hS)+_)+
      (activeLinkPotential (appbSideMolecule s.graph (s.graph.atoms \ S) hS.complement)+_)
    omega

end WaveTurbulence.Mole.AppbAlgorithm
