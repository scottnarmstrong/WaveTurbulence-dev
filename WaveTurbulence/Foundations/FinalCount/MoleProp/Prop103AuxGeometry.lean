/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103SearchProgress
import Mathlib.Tactic

/-! # Actual nontrivial core selection for the auxiliary saving phase -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A connected nonempty minimum-degree-two graph has positive actual
circuit rank, by finite handshaking. -/
theorem circuitRank_pos_of_connected_min_two (M : Molecule V D)
    (hne : M.atoms.Nonempty)
    (hconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b)
    (hmin : ∀ a ∈ M.atoms, 2 ≤ M.deg a) : 0 < M.circuitRank := by
  have hs : (∑ _a ∈ M.atoms, (2 : ℕ)) ≤ ∑ a ∈ M.atoms, M.deg a := sum_le_sum hmin
  rw [Mole.sum_degrees_eq_two_mul_bonds] at hs
  have hf := Mole.numComponents_eq_one M hne hconn
  have hsum : (∑ _a ∈ M.atoms, (2 : ℕ)) = 2*M.atoms.card := by simp [sum_const,Nat.mul_comm]
  rw [hsum] at hs
  unfold Molecule.circuitRank
  rw [hf]
  omega

/-- An arbitrary positive-rank source graph has an actual connected,
simple, bridgeless, nonempty core component of minimum degree two.
The selected graph and its size bound are produced internally. -/
theorem exists_aux_core_component (M : Molecule V D) (hM : M.IsMolecule)
    (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z))
    (hsimple : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1) (hχ : 0 < M.circuitRank) :
    ∃ a ∈ M.atoms,
      let Q := Mole.induced (bridgeCore M) (componentSet (bridgeCore M) a)
      Q.IsMolecule ∧ (∀ z, Q.atom z ≠ Q.atom (Q.mate z)) ∧
      (∀ b c, b ≠ c → Q.bondsBetween b c ≤ 1) ∧ Q.atoms.Nonempty ∧
      (∀ b ∈ Q.atoms, ∀ c ∈ Q.atoms, Q.SameComponent b c) ∧
      (∀ b ∈ Q.atoms, 2 ≤ Q.deg b) ∧ (∀ e, ¬ IsBridge Q e) ∧
      0 < Q.circuitRank ∧ Q.atoms.card ≤ M.atoms.card := by
  have hχC : 0 < (bridgeCore M).circuitRank := by rw [(bridgeCore_bridgefree_and_circuitRank M).2]; exact hχ
  obtain ⟨a,ha,hpos⟩ := exists_positive_degree_of_circuitRank_pos (bridgeCore M) hχC
  let Q := Mole.induced (bridgeCore M) (componentSet (bridgeCore M) a)
  have haC : a ∈ Q.atoms := (mem_componentSet _ _ _).mpr ⟨ha,Relation.EqvGen.refl a⟩
  have hconn := selected_core_connected M a
  have hmin : ∀ b ∈ Q.atoms, 2 ≤ Q.deg b := by
    intro b hb
    rw [induced_component_degree _ _ hb]
    have hn1 := degree_ne_one_of_bridgeless (bridgeCore M) (bridgeCore_bridgefree_and_circuitRank M).1 b
    have hn0 : (bridgeCore M).deg b ≠ 0 := by
      intro hz
      have heq := sameComponent_eq_of_degree_zero (bridgeCore M) hz
        (Relation.EqvGen.symm _ _ ((mem_componentSet _ _ _).mp hb).2)
      rw [heq,hz] at hpos
      omega
    omega
  refine ⟨a,ha,induced_component_isMolecule _ (bridgeCore_isMolecule M hM) a,
    fun z => hloop z.val.val,induced_simple _ _ (bridgeCore_simple M hsimple),⟨a,haC⟩,
    hconn,hmin,induced_component_bridgeless _ (bridgeCore_bridgefree_and_circuitRank M).1 a,
    circuitRank_pos_of_connected_min_two Q ⟨a,haC⟩ hconn hmin,?_⟩
  apply card_le_card
  intro b hb
  exact ((mem_componentSet _ _ _).mp hb).1

/-- If the actual selected auxiliary component has neither a degree-two
atom nor a beta operation, its minimum degree becomes three and it is a
literal ordinary-search input. -/
theorem searchInput_of_min_two_no_two_no_beta (M : Molecule V D) (hM : M.IsMolecule)
    (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z))
    (hsimple : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1) (hne : M.atoms.Nonempty)
    (hconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b)
    (hmin : ∀ a ∈ M.atoms, 2 ≤ M.deg a) (hbridge : ∀ e, ¬ IsBridge M e)
    (hNoTwo : ¬ ∃ a ∈ M.atoms, M.deg a = 2) (hNoBeta : ¬ AdmitsBetaSplit M) : SearchInput M := by
  refine ⟨hM,hloop,hsimple,hne,hconn,?_,hbridge,hNoBeta⟩
  intro a ha
  have hlo := hmin a ha
  have hne2 : M.deg a ≠ 2 := fun h => hNoTwo ⟨a,ha,h⟩
  omega

end WaveTurbulence.MoleProp
