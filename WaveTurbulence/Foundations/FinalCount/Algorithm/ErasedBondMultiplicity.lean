/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBBridgeSpecialBonds
public import WaveTurbulence.Foundations.FinalCount.Algorithm.SimpleDegreeTwo
import Mathlib.Tactic

/-! # Single-bond removal preserves stars away from its two endpoints -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem eraseBond_bondsBetween_of_not_endpoint (M : Molecule V D) (e : D) {a : V}
    (ha : M.atom e ≠ a) (hb : M.atom (M.mate e) ≠ a) (b : V) :
    (eraseBond M e).bondsBetween a b = M.bondsBetween a b := by
  classical
  rw [appb_eraseBond_pair_count]
  unfold appbErasedPairCount Molecule.bondsBetween
  congr 1
  ext x
  simp only [mem_filter]
  constructor
  · rintro ⟨hx,_,_,he⟩; exact ⟨hx,he⟩
  · rintro ⟨hx,he⟩
    refine ⟨hx,?_,?_,he⟩
    · rintro rfl
      rcases Sym2.eq_iff.mp he with h | h
      · exact ha h.1
      · exact hb h.2
    · rintro rfl
      change s(M.atom (M.mate e),M.atom (M.mate (M.mate e))) = s(a,b) at he
      rw [M.mate_mate] at he
      rcases Sym2.eq_iff.mp he with h | h
      · exact hb h.1
      · exact ha h.2

theorem eraseBond_simpleDegreeTwo_iff_of_not_endpoint (M : Molecule V D) (e : D) {a : V}
    (ha : M.atom e ≠ a) (hb : M.atom (M.mate e) ≠ a) :
    SimpleDegreeTwo (eraseBond M e) a ↔ SimpleDegreeTwo M a := by
  have hd := appb_eraseBond_degree M e a
  simp only [ha,hb,ite_false,add_zero] at hd
  have heq : (eraseBond M e).deg a = M.deg a := by omega
  simp only [SimpleDegreeTwo,heq,eraseBond_bondsBetween_of_not_endpoint M e ha hb]
  rfl

end WaveTurbulence.Mole.AppbAlgorithm
