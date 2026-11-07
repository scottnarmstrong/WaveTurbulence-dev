/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBBridgeComponents
public import WaveTurbulence.Foundations.Molecule.MoleculeComponentPartitions
import Mathlib.Tactic

/-! # Counting two actual residual components for 3S3 -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

private theorem appb_induced_path_ambient (M : Molecule V D) (S : Finset V) :
    ∀ {u v}, (induced M S).SameComponent u v → M.SameComponent u v := by
  intro u v h
  induction h with
  | rel u v h => exact Relation.EqvGen.rel _ _ ((induced_adj_iff M S u v).mp h).1
  | refl u => exact Relation.EqvGen.refl u
  | symm u v _ ih => exact ih.symm
  | trans u v w _ _ ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'

/-- Two actual nonempty connected pieces with no cross bond have exactly
two components. The partition is source topology, not a cardinal hypothesis. -/
theorem appb_numComponents_eq_two (M : Molecule V D) {a b : V}
    (h : TwoComponents M M.atoms a b) : M.numComponents = 2 := by
  classical
  obtain ⟨U,W,hcover,hdis,hU,hW,ha,hb,hno⟩ := h
  have haM : a ∈ M.atoms := hcover ▸ mem_union_left _ ha
  have hbM : b ∈ M.atoms := hcover ▸ mem_union_right _ hb
  have hbU : b ∉ U := fun hh => disjoint_left.mp hdis hh hb
  let classify : AppbComponents M → Bool := Quot.lift (fun v : M.atoms => decide (v.val ∈ U)) (by
    intro u v huv
    have he : u.val ∈ U ↔ v.val ∈ U := by
      constructor
      · intro hu
        by_contra hv
        have hvW : v.val ∈ W := ((mem_union.mp (hcover.symm ▸ v.property))).resolve_left hv
        exact hno u.val hu v.val hvW huv
      · intro hv
        by_contra hu
        have huW : u.val ∈ W := ((mem_union.mp (hcover.symm ▸ u.property))).resolve_left hu
        exact hno v.val hv u.val huW (adj_symmetric M huv)
    by_cases hu : u.val ∈ U
    · simp only [decide_eq_true hu,decide_eq_true (he.mp hu)]
    · have hv : v.val ∉ U := fun hv => hu (he.mpr hv)
      simp only [decide_eq_false hu,decide_eq_false hv])
  let representative : Bool → AppbComponents M := fun t =>
    if t then appbComponent M ⟨a,haM⟩ else appbComponent M ⟨b,hbM⟩
  let eqv : AppbComponents M ≃ Bool := {
    toFun := classify
    invFun := representative
    left_inv := by
      intro q
      induction q using Quot.inductionOn with | h v =>
        by_cases hvU : v.val ∈ U
        · change representative (decide (v.val ∈ U)) = appbComponent M v
          rw [show decide (v.val ∈ U) = true from decide_eq_true hvU]
          change appbComponent M ⟨a,haM⟩ = appbComponent M v
          exact quotient_eq_of_sameComponent M (appb_induced_path_ambient M U (hU.2 a ha v.val hvU)) haM v.property
        · have hvW : v.val ∈ W := ((mem_union.mp (hcover.symm ▸ v.property))).resolve_left hvU
          change representative (decide (v.val ∈ U)) = appbComponent M v
          rw [show decide (v.val ∈ U) = false from decide_eq_false hvU]
          change appbComponent M ⟨b,hbM⟩ = appbComponent M v
          exact quotient_eq_of_sameComponent M (appb_induced_path_ambient M W (hW.2 b hb v.val hvW)) hbM v.property
    right_inv := by
      intro t
      cases t <;> simp [classify,representative,appbComponent,ha,hbU] }
  change Nat.card (AppbComponents M) = 2
  rw [Nat.card_congr eqv]
  rw [Nat.card_eq_fintype_card]
  rfl

end WaveTurbulence.Mole
