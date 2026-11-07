/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.LinkPotential
public import WaveTurbulence.Foundations.FinalCount.AppBSimpleLocalBonds
import Mathlib.Tactic

/-! # A simple removed incidence table loses no selected link -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem simple_table_links_eq {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)
    (hP : Function.Injective (fun i : Fin P.edges.length => s(P.edges[i].1,P.edges[i].2))) :
    appbLinks r.post = appbLinks M := by
  apply appbLinks_eraseAtoms_no_double_partner
  intro a ha b hb hne
  have hh := r.bondsBetween_le_one_of_table hP ha b
  omega

theorem simple_table_linkPotential_change {M : Molecule V D} {P : AppbPattern}
    (r : AppbRealization M P)
    (hP : Function.Injective (fun i : Fin P.edges.length => s(P.edges[i].1,P.edges[i].2))) :
    linkPotential r.post = linkPotential M-(P.removed.card : ℤ) := by
  have hl := simple_table_links_eq r hP
  have hv := r.post_card_atoms
  unfold linkPotential
  rw [hl]
  omega

end WaveTurbulence.Mole.AppbAlgorithm
