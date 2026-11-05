/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineBalancedCuts
import Mathlib.Tactic

/-! # Block balance and the source two-cut direction fact -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- Restricting the atomic group can only decrease the outgoing degree. -/
theorem outIn_le_outdeg (M : Molecule V D) (S : Finset V) (v : V) :
    M.outIn S v ≤ M.outdeg v := by
  unfold Molecule.outIn Molecule.outdeg
  apply card_le_card
  intro x hx
  exact mem_filter.mpr ⟨(mem_filter.mp hx).1,(mem_filter.mp hx).2.2⟩

omit [DecidableEq D] in
/-- Restricting the atomic group can only decrease the incoming degree. -/
theorem inIn_le_indeg (M : Molecule V D) (S : Finset V) (v : V) :
    M.inIn S v ≤ M.indeg v := by
  unfold Molecule.inIn Molecule.indeg
  apply card_le_card
  intro x hx
  exact mem_filter.mpr ⟨(mem_filter.mp hx).1,(mem_filter.mp hx).2.2⟩

omit [DecidableEq D] in
/-- Every block is internally balanced: its joints have one incidence in
each direction and its full-degree atoms have two in each direction. -/
theorem block_balanced (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (hB : M.IsBlock S a b) :
    ∀ v ∈ S,M.outIn S v=M.inIn S v := by
  obtain ⟨hS,_ha,_hb,_hab,hoa,hia,hob,hib,hint,_hconn⟩ := hB
  intro v hv
  by_cases ha : v=a
  · subst v
    omega
  by_cases hb : v=b
  · subst v
    omega
  have hd := hint v hv ha hb
  have hh := Mole.outIn_add_inIn M S v
  have ho := outIn_le_outdeg M S v
  have hi := inIn_le_indeg M S v
  have hbnd := hM.1 v (hS hv)
  omega

omit [DecidableEq D] in
/-- The induced oriented degree is exactly the restricted oriented degree. -/
theorem induced_oriented_degree (M : Molecule V D) (S : Finset V) (v : V) (o : Bool) :
    (((Mole.induced M S).dartsAt v).filter (fun x => (Mole.induced M S).out x=o)).card=
      ((M.dartsAt v).filter (fun x => M.InGroup S x ∧ M.out x=o)).card := by
  apply card_bij (fun x _ => x.1)
  · intro x hx
    obtain ⟨ha,ho⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨(Mole.mem_dartsAt M v x.1).mpr
      ((Mole.mem_dartsAt (Mole.induced M S) v x).mp ha),x.2,ho⟩
  · intro x _hx y _hy he
    exact Subtype.ext he
  · intro y hy
    obtain ⟨ha,hg,ho⟩ := mem_filter.mp hy
    refine ⟨⟨y,hg⟩,mem_filter.mpr ⟨?_,ho⟩,rfl⟩
    exact (Mole.mem_dartsAt (Mole.induced M S) v _).mpr ((Mole.mem_dartsAt M v y).mp ha)

/-- TARGET defvine: every two-bond cut inside an actual block has opposite
directions. This derives the figure's direction convention from block axioms. -/
theorem block_two_cut_opposite (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (hB : M.IsBlock S a b)
    (A : Finset V) (hA : A ⊆ S) (x y : {z : D // M.InGroup S z}) (hxy : x ≠ y)
    (hcut : boundary (Mole.induced M S) A={x,y}) : M.out x.1 ≠ M.out y.1 := by
  apply balanced_two_boundary_opposite (Mole.induced M S) _ A hA x y hxy hcut
  intro v hv
  change (((Mole.induced M S).dartsAt v).filter _).card=
    (((Mole.induced M S).dartsAt v).filter _).card
  rw [induced_oriented_degree,induced_oriented_degree]
  exact block_balanced M hM hB v hv

end WaveTurbulence.Vine
