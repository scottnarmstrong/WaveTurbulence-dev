/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.SpecialSingleIncidence
public import WaveTurbulence.Foundations.FinalCount.Algorithm.BridgeStructure
import Mathlib.Tactic

/-! # Only the removed bridge can be special at one of its old endpoints -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem special_at_bridge_endpoint_eq (M : Molecule V D) (hno : AppbNoLoops M)
    (e : D) (hb : Degen.IsBridge M e) (hout : M.out e = true)
    {x : D} (hs : AppbSpecial M x)
    (hinc : (M.atom e = M.atom x ∨ M.atom e = M.atom (M.mate x)) ∨
      (M.atom (M.mate e) = M.atom x ∨ M.atom (M.mate e) = M.atom (M.mate x))) : x = e := by
  have hm := bridge_multiplicity_eq_one M e hb
  have hne := appb_bridge_endpoints_distinct M e hb
  have hend : M.ends e = M.ends x := by
    rcases hinc with h | h
    · exact special_single_incidence_ends M hno hs hne hm h
    · have hm' : M.bondsBetween (M.atom (M.mate e)) (M.atom e) = 1 :=
        (bondsBetween_symm M _ _).trans hm
      have he := special_single_incidence_ends M hno hs hne.symm hm' h
      exact (Sym2.eq_swap (a := M.atom e) (b := M.atom (M.mate e))).trans he
  exact single_outgoing_eq M hs.1 hout hend.symm hm

end WaveTurbulence.Mole.AppbAlgorithm
