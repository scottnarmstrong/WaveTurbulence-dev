/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBLinkIncidence
public import WaveTurbulence.Foundations.FinalCount.AppBLinkDeletion
import Mathlib.Tactic

/-! # Bounded selected-link loss in atom deletion -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Each deleted atom meets at most two links, independently of graph size. -/
theorem appbLinks_lost_card (M : Molecule V D) (hM : M.IsMolecule) (Y : Finset V) :
    ((appbLinks M).filter (fun S => ¬Disjoint S Y)).card ≤ 2*Y.card := by
  classical
  have hsub : (appbLinks M).filter (fun S => ¬Disjoint S Y) ⊆
      Y.biUnion (fun x => (appbLinks M).filter (fun S => x ∈ S)) := by
    intro S hS
    obtain ⟨hlink,hnd⟩ := mem_filter.mp hS
    have hex : ∃ x ∈ S, x ∈ Y := by
      by_contra hn
      apply hnd
      exact disjoint_left.mpr (by intro x hx hy; exact hn ⟨x,hx,hy⟩)
    obtain ⟨x,hxS,hxY⟩ := hex
    exact mem_biUnion.mpr ⟨x,hxY,mem_filter.mpr ⟨hlink,hxS⟩⟩
  calc
    _ ≤ (Y.biUnion (fun x => (appbLinks M).filter (fun S => x ∈ S))).card := card_le_card hsub
    _ ≤ ∑ x ∈ Y, ((appbLinks M).filter (fun S => x ∈ S)).card := card_biUnion_le
    _ ≤ ∑ _x ∈ Y, 2 := sum_le_sum (fun x _ => appbLinks_through_card M hM x)
    _ = _ := by simp [Nat.mul_comm]

/-- Literal deletion loses at most one log-squared factor per vanished
link. The bound includes zero scale and zero decoration-count cases. -/
theorem appbLinkProduct_eraseAtoms_bound (M : Molecule V D) (hM : M.IsMolecule)
    (Y : Finset V) (L γ δ : ℝ) (P : Finset V → ℝ)
    (hL : 0 ≤ L) (hlog : 1 ≤ Real.log L) (hδ : 0 ≤ δ) (hP : ∀ S, 0 ≤ P S) :
    appbLinkProduct M L γ δ P ≤
      (Real.log L)^(4*Y.card)*appbLinkProduct (Degen.eraseAtoms M Y) L γ δ P := by
  classical
  let lost := (appbLinks M).filter (fun S => ¬Disjoint S Y)
  let kept := (appbLinks M).filter (fun S => Disjoint S Y)
  have hpart : appbLinkProduct M L γ δ P =
      (∏ S ∈ lost, Molecule.ladderWeight L γ δ (P S))*
        appbLinkProduct (Degen.eraseAtoms M Y) L γ δ P := by
    unfold appbLinkProduct
    rw [appbLinks_eraseAtoms]
    exact (prod_filter_mul_prod_filter_not (appbLinks M)
      (fun S => ¬Disjoint S Y) (fun S => Molecule.ladderWeight L γ δ (P S))).symm.trans
        (by simp only [not_not]; rfl)
  have hnon : 0 ≤ appbLinkProduct (Degen.eraseAtoms M Y) L γ δ P := by
    apply prod_nonneg
    intro S hS
    exact (appb_link_weight_bounds hL hlog hδ (hP S) γ).1.trans' (by norm_num)
  have hweights : (∏ S ∈ lost, Molecule.ladderWeight L γ δ (P S)) ≤
      (Real.log L^2)^lost.card := by
    rw [← prod_const]
    apply prod_le_prod₀
    · intro S _; exact (appb_link_weight_bounds hL hlog hδ (hP S) γ).1.trans' (by norm_num)
    · intro S _; exact (appb_link_weight_bounds hL hlog hδ (hP S) γ).2
  have hpow : (Real.log L^2)^lost.card ≤ Real.log L^(4*Y.card) := by
    rw [← pow_mul]
    apply pow_le_pow_right₀ hlog
    have hh := appbLinks_lost_card M hM Y
    dsimp only [lost]
    omega
  rw [hpart]
  exact mul_le_mul_of_nonneg_right (hweights.trans hpow) hnon

end WaveTurbulence.Mole
