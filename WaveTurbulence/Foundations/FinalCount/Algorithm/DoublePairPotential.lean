/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.LinkPotential
public import WaveTurbulence.Foundations.FinalCount.AppBD33LinkLoss
import Mathlib.Tactic

/-! # Long normal double-pair chains have no local link-potential loss -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem d33_linkPotential_change (M : Molecule V D) (hM : M.IsMolecule)
    (r : AppbRealization M AppbPatternKind.d33.pattern) :
    linkPotential r.post = linkPotential M-
      (if appbD33LinkAtoms r ∈ appbLinks M then 0 else 2) := by
  classical
  have hv := r.post_card_atoms
  have htwo : AppbPatternKind.d33.pattern.removed.card = 2 := by decide
  rw [htwo] at hv
  have hlinks := appb_d33_links_post M hM r
  by_cases hS : appbD33LinkAtoms r ∈ appbLinks M
  · have hcard := card_erase_add_one hS
    unfold linkPotential
    rw [hlinks,if_pos hS]
    omega
  · unfold linkPotential
    rw [hlinks,erase_eq_of_notMem hS,if_neg hS]
    omega

end WaveTurbulence.Mole.AppbAlgorithm
