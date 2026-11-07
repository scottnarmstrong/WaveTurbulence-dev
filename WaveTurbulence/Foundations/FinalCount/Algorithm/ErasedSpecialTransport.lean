/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ErasedBondMultiplicity
import Mathlib.Tactic

/-! # Special-bond predicates transport away from the edited endpoints -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem eraseBond_special_iff_of_remote_endpoints (M : Molecule V D) (e : D)
    (x : {x : D // x ≠ e ∧ x ≠ M.mate e})
    (h11 : M.atom e ≠ M.atom x.val) (h21 : M.atom (M.mate e) ≠ M.atom x.val)
    (h12 : M.atom e ≠ M.atom (M.mate x.val))
    (h22 : M.atom (M.mate e) ≠ M.atom (M.mate x.val)) :
    AppbSpecial (eraseBond M e) x ↔ AppbSpecial M x.val := by
  classical
  have hp1 (b : V) : appbErasedPairCount M e (M.atom x.val) b = M.bondsBetween (M.atom x.val) b :=
    (appb_eraseBond_pair_count M e _ b).symm.trans (eraseBond_bondsBetween_of_not_endpoint M e h11 h21 b)
  have hp2 (b : V) : appbErasedPairCount M e (M.atom (M.mate x.val)) b =
      M.bondsBetween (M.atom (M.mate x.val)) b :=
    (appb_eraseBond_pair_count M e _ b).symm.trans (eraseBond_bondsBetween_of_not_endpoint M e h12 h22 b)
  rw [appb_eraseBond_special_iff]
  simp only [AppbErasedBondSpecial,AppbSpecial,h11,h21,h12,h22,ite_false,add_zero,hp1,hp2]

end WaveTurbulence.Mole.AppbAlgorithm
