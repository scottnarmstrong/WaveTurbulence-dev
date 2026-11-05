/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MarkedGardenChains
public import WaveTurbulence.Foundations.Molecule.ConcatenationDarts
public import WaveTurbulence.Foundations.Molecule.MoleculeJointSymmetry
import Mathlib.Tactic

/-! # All and only the distinguished ingredient's bonds survive chain splicing -/

public section
namespace WaveTurbulence.Mole
open TTree Finset
namespace MarkedGardenChain
variable {w : ℕ} {G : Garden w} {focus : GardenBlockSegment G}
variable {X : Finset (GBranch G.tree)} {left right : GBranch G.tree}

/-- Literal residual-dart condition for simultaneous molecular splicing. -/
@[expose] def ResidualDartCondition (C : MarkedGardenChain G focus X left right) (x : GardenDart G) : Prop :=
  G.molecule.InGroup X x ∧ ∀ S ∈ C.erasedGroups, ¬ G.molecule.InGroup S x

private theorem residual_filter_step {V D : Type*} [DecidableEq V] [Fintype D]
    (M : Molecule V D) (X A : Finset V) (groups : List (Finset V)) (x : D)
    (hcover : M.InGroup (X ∪ A) x ↔ M.InGroup X x ∨ M.InGroup A x)
    (hdis : ¬ (M.InGroup X x ∧ M.InGroup A x)) :
    (M.InGroup (X ∪ A) x ∧ ∀ S ∈ A :: groups, ¬ M.InGroup S x) ↔
      (M.InGroup X x ∧ ∀ S ∈ groups, ¬ M.InGroup S x) := by
  constructor
  · rintro ⟨hu,hn⟩
    exact ⟨(hcover.mp hu).resolve_right (hn A List.mem_cons_self),
      fun S hS => hn S (List.mem_cons_of_mem _ hS)⟩
  · rintro ⟨hx,hn⟩
    refine ⟨hcover.mpr (Or.inl hx),?_⟩
    intro S hS
    rcases List.mem_cons.mp hS with rfl | hS
    · exact fun ha => hdis ⟨hx,ha⟩
    · exact hn S hS

/-- TARGET `blockchainprop`: the actual residual half-edge set equals
the distinguished ingredient's internal half-edge set, including multiplicities. -/
theorem residualDartCondition_iff_focus (C : MarkedGardenChain G focus X left right) (x : GardenDart G) :
    C.ResidualDartCondition x ↔ G.molecule.InGroup focus.atoms x := by
  induction C with
  | base =>
    constructor
    · exact fun h => h.1
    · intro h
      exact ⟨h,fun S hS => (List.not_mem_nil hS).elim⟩
  | @append X left right prev A hj hi hU hCL ih =>
    have hA : G.molecule.IsBlock A.atoms A.rightJoint right :=
      hj ▸ block_swap_joints G.molecule A.block
    have hcover := concatenation_internal_iff G.molecule (garden_isMolecule G) prev.block hA hU x
    have hdis := concatenation_internal_disjoint G.molecule prev.block prev.connected hi x
    exact (residual_filter_step G.molecule X A.atoms prev.erasedGroups x hcover hdis).trans ih
  | @prepend X left right prev A hj hi hU hCL ih =>
    have hA : G.molecule.IsBlock A.atoms A.leftJoint left := hj ▸ A.block
    have hprev := block_swap_joints G.molecule prev.block
    have hwhole := block_swap_joints G.molecule hU
    have hcover := concatenation_internal_iff G.molecule (garden_isMolecule G) hprev hA hwhole x
    have hdis := concatenation_internal_disjoint G.molecule hprev prev.connected hi x
    exact (residual_filter_step G.molecule X A.atoms prev.erasedGroups x hcover hdis).trans ih

end MarkedGardenChain
end WaveTurbulence.Mole
