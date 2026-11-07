/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.DeletionReroute
import Mathlib.Tactic

/-! # Global component preservation from actual cut paths

This permits local normal-operation computations in a molecule with other
untouched components. No component-count identity is a premise.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def eraseAtomsComponentForget (M : Molecule V D) (Y : Finset V) :
    AppbComponents (Degen.eraseAtoms M Y) → AppbComponents M :=
  Quot.lift (fun a => appbComponent M ⟨a.val,(mem_sdiff.mp a.property).1⟩) (by
    intro a b hab
    obtain ⟨x,hx,hy⟩ := hab
    exact Quot.sound ⟨x.val,hx,hy⟩)

/-- Actual old and new paths, rather than assumed quotient cardinalities,
produce a bijection on all components, including untouched components. -/
theorem eraseAtomsComponentForget_bijective (M : Molecule V D) (Y : Finset V)
    (b : V) (hb : b ∈ M.atoms \ Y)
    (hremoved : ∀ a ∈ Y,M.SameComponent a b)
    (hboundary : ∀ x ∈ Degen.boundaryDarts M Y,
      (Degen.eraseAtoms M Y).SameComponent b (M.atom (M.mate x))) :
    Function.Bijective (eraseAtomsComponentForget M Y) := by
  constructor
  · intro q q' he
    induction q using Quot.inductionOn with | h a =>
      induction q' using Quot.inductionOn with | h c =>
        have hp := (quotient_eq_iff_sameComponent M
          ⟨a.val,(mem_sdiff.mp a.property).1⟩ ⟨c.val,(mem_sdiff.mp c.property).1⟩).mp he
        apply (quotient_eq_iff_sameComponent (Degen.eraseAtoms M Y) a c).mpr
        exact eraseAtoms_sameComponent_of_boundary_connected M Y b hboundary
          (mem_sdiff.mp a.property).2 (mem_sdiff.mp c.property).2 hp
  · intro q
    induction q using Quot.inductionOn with | h a =>
      by_cases ha : a.val ∈ Y
      · refine ⟨appbComponent (Degen.eraseAtoms M Y) ⟨b,hb⟩,?_⟩
        apply (quotient_eq_iff_sameComponent M ⟨b,(mem_sdiff.mp hb).1⟩ a).mpr
        exact (hremoved a.val ha).symm
      · exact ⟨appbComponent (Degen.eraseAtoms M Y) ⟨a.val,mem_sdiff.mpr ⟨a.property,ha⟩⟩,rfl⟩

theorem numComponents_eraseAtoms_eq_of_cut_paths (M : Molecule V D) (Y : Finset V)
    (b : V) (hb : b ∈ M.atoms \ Y)
    (hremoved : ∀ a ∈ Y,M.SameComponent a b)
    (hboundary : ∀ x ∈ Degen.boundaryDarts M Y,
      (Degen.eraseAtoms M Y).SameComponent b (M.atom (M.mate x))) :
    (Degen.eraseAtoms M Y).numComponents = M.numComponents :=
  Nat.card_congr (Equiv.ofBijective (eraseAtomsComponentForget M Y)
    (eraseAtomsComponentForget_bijective M Y b hb hremoved hboundary))

end WaveTurbulence.Mole.AppbAlgorithm
