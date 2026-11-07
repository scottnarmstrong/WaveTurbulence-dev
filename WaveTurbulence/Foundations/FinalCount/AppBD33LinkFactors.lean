/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBD33LinkLoss
import Mathlib.Tactic

/-! # Exact lost-weight factor in the normal double-pair operation -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def appbD33LostScale {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33.pattern) (P : Finset V → ℝ) : ℝ := by
  classical
  exact if appbD33LinkAtoms r ∈ appbLinks M then P (appbD33LinkAtoms r) else 0

/-- Exact multiplicative link-product identity. The baseline scale zero
produces weight one when the removed pair touches no selected link. -/
theorem appb_d33_linkProduct_factor (M : Molecule V D) (hM : M.IsMolecule)
    (r : AppbRealization M AppbPatternKind.d33.pattern) (L γ δ : ℝ)
    (P : Finset V → ℝ) (hlog : 1 ≤ Real.log L) :
    appbLinkProduct M L γ δ P =
      Molecule.ladderWeight L γ δ (appbD33LostScale r P)*appbLinkProduct r.post L γ δ P := by
  classical
  unfold appbLinkProduct
  rw [appb_d33_links_post M hM r]
  by_cases hT : appbD33LinkAtoms r ∈ appbLinks M
  · simp only [appbD33LostScale,hT,ite_true]
    exact (mul_prod_erase (appbLinks M) (fun S => Molecule.ladderWeight L γ δ (P S)) hT).symm
  · simp only [appbD33LostScale,hT,ite_false,appb_link_weight_zero hlog,
      erase_eq_of_notMem hT,one_mul]

end WaveTurbulence.Mole
