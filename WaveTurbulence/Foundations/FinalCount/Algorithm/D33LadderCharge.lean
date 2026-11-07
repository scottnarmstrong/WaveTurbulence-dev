/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33DisplayedLink
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ChargedTrace
import Mathlib.Tactic

/-! # Zero potential charge for an actual normal double-rung step -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
universe u v
variable {V : Type v} [DecidableEq V]

theorem d33_normal_activePotential_change_by_rung
    {D : Type u} [Fintype D] [DecidableEq D] (M : Molecule V D) (hM : M.IsMolecule)
    (r : AppbRealization M AppbPatternKind.d33.pattern)
    (h3 : M.deg (r.vertex 3) = 4) (h4 : M.deg (r.vertex 4) = 4)
    (hopp : AppbD33BoundaryOpposite M r) :
    activeLinkPotential r.post = activeLinkPotential M-
      (if M.bondsBetween (r.vertex 3) (r.vertex 4) = 2 then 0 else 2) := by
  classical
  rw [d33_normal_activePotential_change M hM r h3 h4]
  simp only [d33_displayed_link_iff_double M hM r hopp]

/-- A continuing double rung is uncharged because its actual link is
present; membership in the link family is derived from the source geometry. -/
theorem d33_zero_charge_of_double (s : State.{u,v} V) (hM : s.graph.IsMolecule)
    (r : AppbRealization s.graph AppbPatternKind.d33.pattern)
    (h3 : s.graph.deg (r.vertex 3) = 4) (h4 : s.graph.deg (r.vertex 4) = 4)
    (hdouble : s.graph.bondsBetween (r.vertex 3) (r.vertex 4) = 2)
    (hopp : AppbD33BoundaryOpposite s.graph r) :
    ChargedStep s (ofMolecule r.post) 0 :=
  .ladder s r hM h3 h4 (d33_displayed_link_of_double s.graph r hdouble hopp)

end WaveTurbulence.Mole.AppbAlgorithm
