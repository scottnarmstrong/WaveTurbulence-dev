/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ActivePotential
public import WaveTurbulence.Foundations.FinalCount.Algorithm.DoublePairPotential
public import WaveTurbulence.Foundations.FinalCount.Algorithm.NormalIsolatedCounts
public import WaveTurbulence.Foundations.FinalCount.Algorithm.SimpleTablePotential
import Mathlib.Tactic

/-! # Exact active-potential effects of normal single and double removals -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem d33_normal_activePotential_change (M : Molecule V D) (hM : M.IsMolecule)
    (r : AppbRealization M AppbPatternKind.d33.pattern)
    (h3 : M.deg (r.vertex 3) = 4) (h4 : M.deg (r.vertex 4) = 4) :
    activeLinkPotential r.post = activeLinkPotential M-
      (if appbD33LinkAtoms r ∈ appbLinks M then 0 else 2) := by
  have hi := d33_normal_isolated_count M r h3 h4
  have he : (appbDegreeAtoms r.post 0).card = (appbDegreeAtoms M 0).card := by omega
  unfold activeLinkPotential
  rw [d33_linkPotential_change M hM r,he]
  ring

theorem s33_normal_activePotential_change (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.s33.pattern)
    (h3 : M.deg (r.vertex 3) = 4) (h4 : M.deg (r.vertex 4) = 4)
    (h5 : M.deg (r.vertex 5) = 4) (h6 : M.deg (r.vertex 6) = 4) :
    activeLinkPotential r.post = activeLinkPotential M-2 := by
  have hi := s33_normal_isolated_count M r h3 h4 h5 h6
  have he : (appbDegreeAtoms r.post 0).card = (appbDegreeAtoms M 0).card := by omega
  have hk := simple_table_linkPotential_change r (by decide)
  have hcard : AppbPatternKind.s33.pattern.removed.card = 2 := by decide
  rw [hcard] at hk
  unfold activeLinkPotential
  rw [hk,he]
  ring

theorem r3_normal_activePotential_change (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.r3.pattern)
    (h2 : M.deg (r.vertex 2) = 4) (h3 : M.deg (r.vertex 3) = 4)
    (h4 : M.deg (r.vertex 4) = 4) :
    activeLinkPotential r.post = activeLinkPotential M-1 := by
  have hi := r3_normal_isolated_count M r h2 h3 h4
  have he : (appbDegreeAtoms r.post 0).card = (appbDegreeAtoms M 0).card := by omega
  have hk := simple_table_linkPotential_change r (by decide)
  have hcard : AppbPatternKind.r3.pattern.removed.card = 1 := by decide
  rw [hcard] at hk
  unfold activeLinkPotential
  rw [hk,he]
  ring

end WaveTurbulence.Mole.AppbAlgorithm
