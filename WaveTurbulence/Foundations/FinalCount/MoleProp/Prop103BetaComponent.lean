/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103BetaCut
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103SelectedCore
import Mathlib.Tactic

/-! # Selecting an actual component does not create a source beta split -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A two-bond old cut inside an actual whole component is also an old cut
of the original graph; every old incident dart remains in that component. -/
theorem boundary_pair_of_induced_component (M : Molecule V D) (a : V)
    (U : Finset V) (hU : U ⊆ componentSet M a)
    {x y : {z : D // M.InGroup (componentSet M a) z}}
    (hb : boundaryDarts (Mole.induced M (componentSet M a)) U =
      {(Mole.induced M (componentSet M a)).mate x,(Mole.induced M (componentSet M a)).mate y}) :
    boundaryDarts M U = {M.mate x.val,M.mate y.val} := by
  classical
  rw [boundary_eq_image_induced_component M a U hU,hb,image_insert,image_singleton]
  rfl

/-- In a loopless bridgeless graph, selecting a whole actual component
cannot newly enable a permitted source beta operation. -/
theorem admitsBetaSplit_before_component_selection (M : Molecule V D)
    (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z)) (hbridge : ∀ e, ¬ IsBridge M e)
    (a : V) : AdmitsBetaSplit (Mole.induced M (componentSet M a)) → AdmitsBetaSplit M := by
  let N := Mole.induced M (componentSet M a)
  rintro ⟨v,x,y,hd,h4,hnb,hdisc⟩
  have hvC : v ∈ componentSet M a := by
    obtain ⟨b,hb,hbv⟩ := mem_map.mp hd.1
    change some b = some v at hbv
    exact Option.some.inj hbv ▸ hb
  have hx : M.atom x.val = v := Option.some.inj hd.2.2.1
  have hy : M.atom y.val = v := Option.some.inj hd.2.2.2.1
  have hloopN : ∀ z, N.atom z ≠ N.atom (N.mate z) := fun z => hloop z.val
  obtain ⟨U,hU,hcut,_,_⟩ := exists_old_cut_of_beta_split N hloopN hx hy hdisc
  have hU' : U ⊆ M.atoms \ {v} := by
    intro b hb
    have hh := mem_sdiff.mp (hU hb)
    exact mem_sdiff.mpr ⟨((mem_componentSet _ _ _).mp hh.1).1,hh.2⟩
  have hboundary := boundary_pair_of_induced_component M a U
    (fun b hb => (mem_sdiff.mp (hU hb)).1) hcut
  apply admitsBetaSplit_of_old_mixed_cut M ((mem_componentSet _ _ _).mp hvC).1
    ((induced_component_degree M a hvC).symm.trans h4) hx hy
    hd.2.2.2.2.2.1 hd.2.2.2.2.2.2 (fun e _ => hbridge e) U hU' hboundary

end WaveTurbulence.MoleProp
