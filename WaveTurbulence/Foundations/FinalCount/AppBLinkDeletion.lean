/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBLinkDegrees
import Mathlib.Tactic

/-! # Exact selected-link survival under literal atom deletion -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Atom deletion leaves exactly the old links avoiding the deleted set. -/
theorem appb_link_eraseAtoms_iff (M : Molecule V D) (Y S : Finset V) :
    AppbLink (Degen.eraseAtoms M Y) S ↔ AppbLink M S ∧ Disjoint S Y := by
  rw [appb_link_iff_source_card,appb_link_iff_source_card,Degen.sourceLadderSet_erase_iff]
  tauto

theorem appbLinks_eraseAtoms (M : Molecule V D) (Y : Finset V) :
    appbLinks (Degen.eraseAtoms M Y) = (appbLinks M).filter (fun S => Disjoint S Y) := by
  classical
  ext S
  simp only [mem_appbLinks,mem_filter,appb_link_eraseAtoms_iff]

/-- If every deleted vertex has degree at most two, no link is changed. -/
theorem appbLinks_eraseAtoms_low_degree (M : Molecule V D) (Y : Finset V)
    (hY : ∀ a ∈ Y, M.deg a ≤ 2) : appbLinks (Degen.eraseAtoms M Y) = appbLinks M := by
  rw [appbLinks_eraseAtoms]
  apply filter_eq_self.mpr
  intro S hS
  exact ((mem_appbLinks M S).mp hS).disjoint_low_degree hY

/-- Exact ladder-factor preservation for every fine deletion operation. -/
theorem appbLinkProduct_eraseAtoms_low_degree (M : Molecule V D) (Y : Finset V)
    (hY : ∀ a ∈ Y, M.deg a ≤ 2) (L γ δ : ℝ) (P : Finset V → ℝ) :
    appbLinkProduct (Degen.eraseAtoms M Y) L γ δ P = appbLinkProduct M L γ δ P := by
  unfold appbLinkProduct
  rw [appbLinks_eraseAtoms_low_degree M Y hY]

/-- Exact preservation when the deleted atoms have no double partner,
covering the normal single-star and triple-bond roles. -/
theorem appbLinks_eraseAtoms_no_double_partner (M : Molecule V D) (Y : Finset V)
    (hY : ∀ a ∈ Y, ∀ b ∈ M.atoms, a ≠ b → M.bondsBetween a b ≠ 2) :
    appbLinks (Degen.eraseAtoms M Y) = appbLinks M := by
  rw [appbLinks_eraseAtoms]
  apply filter_eq_self.mpr
  intro S hS
  exact ((mem_appbLinks M S).mp hS).disjoint_no_double_partner hY

end WaveTurbulence.Mole
