/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103CutParity
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103BetaCut
public import WaveTurbulence.Foundations.FinalCount.MoleProp.SimpleGraphRank
import Mathlib.Tactic

/-! # The actual two-degree-three profile on the retained beta side -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A side with old degree four and two distinct boundary endpoints has
exactly two degree-three vertices in its actual induced graph. -/
theorem induced_profile_of_four_and_two_boundary (M : Molecule V D) (U : Finset V)
    {x y : D} (hboundary : boundaryDarts M U = {x,y})
    (hne : M.atom x ≠ M.atom y) (hfull : ∀ a ∈ U, M.deg a = 4) :
    M.atom x ∈ U ∧ M.atom y ∈ U ∧
      (Mole.induced M U).deg (M.atom x) = 3 ∧
      (Mole.induced M U).deg (M.atom y) = 3 ∧
      ∀ a ∈ U, a ≠ M.atom x → a ≠ M.atom y → (Mole.induced M U).deg a = 4 := by
  classical
  have hxmem : x ∈ boundaryDarts M U := by rw [hboundary]; simp
  have hymem : y ∈ boundaryDarts M U := by rw [hboundary]; simp
  have hxu : M.atom x ∈ U := (mem_filter.mp hxmem).2.1
  have hyu : M.atom y ∈ U := (mem_filter.mp hymem).2.1
  have hd (a : V) (ha : a ∈ U) := degreeIn_add_boundaryAt M U ha
  have hxcard : ((boundaryDarts M U).filter (fun z => M.atom z = M.atom x)).card = 1 := by
    rw [hboundary]
    simp [filter_insert,filter_singleton,Ne.symm hne]
  have hycard : ((boundaryDarts M U).filter (fun z => M.atom z = M.atom y)).card = 1 := by
    rw [hboundary]
    simp [filter_insert,filter_singleton,hne]
  have hdx := hd (M.atom x) hxu
  have hdy := hd (M.atom y) hyu
  rw [hxcard,hfull _ hxu] at hdx
  rw [hycard,hfull _ hyu] at hdy
  refine ⟨hxu,hyu,?_,?_,?_⟩
  · rw [Mole.induced_deg]
    omega
  · rw [Mole.induced_deg]
    omega
  · intro a ha hax hay
    have he := hd a ha
    have hc : ((boundaryDarts M U).filter (fun z => M.atom z = a)).card = 0 := by
      rw [hboundary]
      simp [filter_insert,filter_singleton,Ne.symm hax,Ne.symm hay]
    rw [hc,hfull a ha] at he
    rw [Mole.induced_deg]
    omega

/-- Source simplicity makes the two selected beta neighbors distinct. -/
theorem beta_neighbors_ne (M : Molecule V D)
    (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z))
    (hsimple : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1)
    {v : V} {x y : D} (hx : M.atom x = v) (hy : M.atom y = v) (hxy : x ≠ y) :
    M.atom (M.mate x) ≠ M.atom (M.mate y) := by
  intro hh
  apply hxy
  exact otherEndpoint_injOn_dartsAt M hloop hsimple v
    ((Mole.mem_dartsAt M v x).mpr hx) ((Mole.mem_dartsAt M v y).mpr hy) hh

end WaveTurbulence.MoleProp
