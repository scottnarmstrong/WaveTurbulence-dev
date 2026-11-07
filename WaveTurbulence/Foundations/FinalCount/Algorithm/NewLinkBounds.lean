/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBLinkLoss
public import WaveTurbulence.Foundations.FinalCount.AppBAddSafeLadder
public import WaveTurbulence.Foundations.FinalCount.AppBBridgeValidScales
import Mathlib.Tactic

/-! # A one-bond edit can create at most four selected links -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D E : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

theorem link_card_le_of_away_subset (M : Molecule V D) (N : Molecule V E) (hN : N.IsMolecule)
    (Y : Finset V) (haway : (appbLinks N).filter (fun S => Disjoint S Y) ⊆ appbLinks M) :
    (appbLinks N).card ≤ (appbLinks M).card+2*Y.card := by
  classical
  have hkeep := card_le_card haway
  have htouch := appbLinks_lost_card N hN Y
  have hpart := card_filter_add_card_filter_not (s := appbLinks N) (fun S => Disjoint S Y)
  omega

theorem addBond_links_card_le (M : Molecule V D) (a b : V) (hN : (addBond M a b).IsMolecule) :
    (appbLinks (addBond M a b)).card ≤ (appbLinks M).card+4 := by
  classical
  have hkeep : (appbLinks (addBond M a b)).filter (fun S => Disjoint S {a,b}) ⊆ appbLinks M := by
    intro S hS
    obtain ⟨hS,hdis⟩ := mem_filter.mp hS
    obtain ⟨u,v,hL,hset⟩ := (mem_appbLinks _ _).mp hS
    have hmem (j : Fin 2) : u j ∈ S ∧ v j ∈ S := by
      rw [← hset]
      constructor <;> simp [Molecule.ladderAtoms]
    have havoid : ∀ j,u j ≠ a ∧ u j ≠ b ∧ v j ≠ a ∧ v j ≠ b := by
      intro j
      have hu := disjoint_left.mp hdis (hmem j).1
      have hv := disjoint_left.mp hdis (hmem j).2
      exact ⟨fun he => hu (he.symm ▸ (by simp)),fun he => hu (he.symm ▸ (by simp)),
        fun he => hv (he.symm ▸ (by simp)),fun he => hv (he.symm ▸ (by simp))⟩
    exact (mem_appbLinks _ _).mpr ⟨u,v,(appb_sourceLadder_addBond_iff M a b u v havoid).mp hL,hset⟩
  have hh := link_card_le_of_away_subset M (addBond M a b) hN {a,b} hkeep
  have hc : ({a,b} : Finset V).card ≤ 2 := card_le_two
  omega

theorem eraseBond_links_card_le (M : Molecule V D) (e : D) (hN : (eraseBond M e).IsMolecule) :
    (appbLinks (eraseBond M e)).card ≤ (appbLinks M).card+4 := by
  classical
  have hkeep : (appbLinks (eraseBond M e)).filter
      (fun S => Disjoint S {M.atom e,M.atom (M.mate e)}) ⊆ appbLinks M := by
    intro S hS
    obtain ⟨hS,hdis⟩ := mem_filter.mp hS
    obtain ⟨u,v,hL,hset⟩ := (mem_appbLinks _ _).mp hS
    have hmem (j : Fin 2) : u j ∈ S ∧ v j ∈ S := by
      rw [← hset]
      constructor <;> simp [Molecule.ladderAtoms]
    have havoid : ∀ j,u j ≠ M.atom e ∧ u j ≠ M.atom (M.mate e) ∧
        v j ≠ M.atom e ∧ v j ≠ M.atom (M.mate e) := by
      intro j
      have hu := disjoint_left.mp hdis (hmem j).1
      have hv := disjoint_left.mp hdis (hmem j).2
      exact ⟨fun he => hu (he.symm ▸ (by simp)),fun he => hu (he.symm ▸ (by simp)),
        fun he => hv (he.symm ▸ (by simp)),fun he => hv (he.symm ▸ (by simp))⟩
    exact (mem_appbLinks _ _).mpr ⟨u,v,(appb_sourceLadder_eraseBond_iff M e u v havoid).mp hL,hset⟩
  have hh := link_card_le_of_away_subset M (eraseBond M e) hN {M.atom e,M.atom (M.mate e)} hkeep
  have hc : ({M.atom e,M.atom (M.mate e)} : Finset V).card ≤ 2 := card_le_two
  omega

end WaveTurbulence.Mole.AppbAlgorithm
