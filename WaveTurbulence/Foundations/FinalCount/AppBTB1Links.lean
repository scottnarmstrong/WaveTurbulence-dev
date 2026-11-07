/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBLocalMultiplicity
public import WaveTurbulence.Foundations.FinalCount.AppBLinkDeletion
import Mathlib.Tactic

/-! # Triple-bond components contain no selected double-rung link -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Each deleted atom in TB-1N has three bonds to its sole neighbour,
so none of its bond multiplicities is two. -/
theorem appb_tb1_no_double_partner (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.tb1.pattern) :
    ∀ a ∈ r.removedAtoms,∀ b : V,M.bondsBetween a b ≠ 2 := by
  intro a ha b
  rw [r.bondsBetween_eq_local_sum ha b]
  have he : ∀ i : Fin AppbPatternKind.tb1.pattern.edges.length,
      M.ends (r.edge i).val = s(r.vertex 1,r.vertex 2) := by
    intro i
    rw [r.endpoints i]
    fin_cases i <;> rfl
  simp only [he]
  by_cases h : s(r.vertex 1,r.vertex 2) = s(a,b)
  · simp only [h,ite_true]
    decide
  · simp only [h,ite_false]
    decide

/-- The actual selected-link product is unchanged by TB-1N. -/
theorem appb_tb1_linkProduct (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.tb1.pattern) (L γ δ : ℝ) (P : Finset V → ℝ) :
    appbLinkProduct r.post L γ δ P = appbLinkProduct M L γ δ P := by
  change appbLinkProduct (Degen.eraseAtoms M r.removedAtoms) L γ δ P = _
  unfold appbLinkProduct
  rw [appbLinks_eraseAtoms_no_double_partner M r.removedAtoms]
  intro a ha b hb hne
  exact appb_tb1_no_double_partner M r a ha b

end WaveTurbulence.Mole
