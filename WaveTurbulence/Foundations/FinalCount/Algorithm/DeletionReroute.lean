/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBBridgeComponents
public import WaveTurbulence.Foundations.Molecule.Degen.ComponentQuotient
import Mathlib.Tactic

/-! # Rerouting old paths through one surviving component of an actual cut -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def rerouteAtom (Y : Finset V) (b : V) (a : V) : V := if a ∈ Y then b else a

/-- Conditional path helper. Its premise is actual connectivity of the
surviving boundary atoms, not a component-count or operation-count bound. -/
theorem eraseAtoms_reroute_path (M : Molecule V D) (Y : Finset V) (b : V)
    (hboundary : ∀ x ∈ Degen.boundaryDarts M Y,
      (Degen.eraseAtoms M Y).SameComponent b (M.atom (M.mate x)))
    {a c : V} (hp : M.SameComponent a c) :
    (Degen.eraseAtoms M Y).SameComponent (rerouteAtom Y b a) (rerouteAtom Y b c) := by
  have hstep (a c : V) (h : M.Adj a c) :
      (Degen.eraseAtoms M Y).SameComponent (rerouteAtom Y b a) (rerouteAtom Y b c) := by
    obtain ⟨x,rfl,rfl⟩ := h
    by_cases hx : M.atom x ∈ Y <;> by_cases hy : M.atom (M.mate x) ∈ Y
    · simp only [rerouteAtom,hx,hy,ite_true]
      exact Relation.EqvGen.refl _
    · have hb := hboundary x (mem_filter.mpr ⟨mem_univ _,hx,hy⟩)
      simpa only [rerouteAtom,hx,hy,ite_true,ite_false] using hb
    · have hm : M.mate x ∈ Degen.boundaryDarts M Y := by
        exact mem_filter.mpr ⟨mem_univ _,hy,by simpa only [M.mate_mate] using hx⟩
      simp only [rerouteAtom,hx,hy,ite_true,ite_false]
      have hb := hboundary (M.mate x) hm
      rw [M.mate_mate] at hb
      exact Relation.EqvGen.symm _ _ hb
    · simp only [rerouteAtom,hx,hy,ite_false]
      exact Relation.EqvGen.rel _ _ ⟨⟨x,hx,hy⟩,rfl,rfl⟩
  induction hp with
  | rel a c h => exact hstep a c h
  | refl a => exact Relation.EqvGen.refl _
  | symm a c hp ih => exact ih.symm
  | trans a c d hp hp' ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'

theorem eraseAtoms_sameComponent_of_boundary_connected (M : Molecule V D)
    (Y : Finset V) (b : V)
    (hboundary : ∀ x ∈ Degen.boundaryDarts M Y,
      (Degen.eraseAtoms M Y).SameComponent b (M.atom (M.mate x)))
    {a c : V} (ha : a ∉ Y) (hc : c ∉ Y) (hp : M.SameComponent a c) :
    (Degen.eraseAtoms M Y).SameComponent a c := by
  simpa only [rerouteAtom,ha,hc,ite_false] using eraseAtoms_reroute_path M Y b hboundary hp

end WaveTurbulence.Mole.AppbAlgorithm
