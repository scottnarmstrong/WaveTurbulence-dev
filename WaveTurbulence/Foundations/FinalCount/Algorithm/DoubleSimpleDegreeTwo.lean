/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.SimpleDegreeTwoChange
public import WaveTurbulence.Foundations.Molecule.MoleculeBondsBetween
public import WaveTurbulence.Foundations.FinalCount.AppBResidualLabels
import Mathlib.Tactic

/-! # Double degree-two groups and their actual V2-star effects -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem not_simpleDegreeTwo_of_double (M : Molecule V D) {a b : V} (hab : a ≠ b)
    (hd : M.deg a = 2) (hm : M.bondsBetween a b = 2) : ¬SimpleDegreeTwo M a := by
  classical
  intro hs
  obtain ⟨_,c,hc,d,hd',hac,had,hcd,hmc,hmd⟩ := hs
  have hA : (M.dartsAt a).filter (fun x => M.atom (M.mate x) = b) = M.dartsAt a := by
    apply eq_of_subset_of_card_le (filter_subset _ _)
    rw [← bondsBetween_eq_card_darts M hab,hm]
    exact hd.le
  have hcp : 0 < ((M.dartsAt a).filter (fun x => M.atom (M.mate x) = c)).card := by
    rw [← bondsBetween_eq_card_darts M hac,hmc]
    decide
  obtain ⟨x,hx⟩ := card_pos.mp hcp
  obtain ⟨hx,hxc⟩ := mem_filter.mp hx
  have hxb : M.atom (M.mate x) = b := by
    have hxB : x ∈ (M.dartsAt a).filter (fun z => M.atom (M.mate z) = b) := by
      rw [hA]; exact hx
    exact (mem_filter.mp hxB).2
  have hcb : c = b := hxc.symm.trans hxb
  rw [hcb,hm] at hmc
  omega

end WaveTurbulence.Mole.AppbAlgorithm
