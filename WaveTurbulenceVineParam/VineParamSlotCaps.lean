/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulence.Foundations.Molecule.VineTemplates
public import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic

/-! # Disjoint symmetric caps at every marked insertion slot

These literal finite-core certificates support arbitrary ladder insertion.
Only the chosen slot crosses its cap boundary. Reflection interchanges
its two cap ports, fixes the joints and all other slots, and preserves
internal bonds and the source coherence groups. Type II uses its single
joint cap, so the Q-block endpoint m=1 is included.
-/

public section
namespace WaveTurbulence.Vine.Param
open Finset

/-- A cap and its reflection for each literal marked slot, in slot order. -/
@[expose] def slotCapData : VineType → List ((Finset ℕ) × (ℕ ≃ ℕ))
  | .I => []
  | .II => [({1},Equiv.refl ℕ)]
  | .III => [({0,2,3},Equiv.swap 2 3),({1,7,8},Equiv.swap 7 8)]
  | .IV => [({0,2,3},Equiv.swap 2 3),({1,7,8},Equiv.swap 7 8)]
  | .V => [({4,5,6,7,8},(Equiv.swap 4 5).trans (Equiv.swap 6 7))]
  | .VI => [({0,2,3},Equiv.swap 2 3),({10,11,12},Equiv.swap 10 11),
      ({1,13,14},Equiv.swap 13 14)]
  | .VII => [({0,2,3},Equiv.swap 2 3),({4,5,6},Equiv.swap 5 6),({1,9,10},Equiv.swap 9 10)]
  | .VIII => [({1,4,5},Equiv.swap 4 5),({8,9,10},Equiv.swap 8 9)]

/-- Exactly one cap is supplied for each marked slot. -/
theorem slotCapData_length (X : VineType) : (slotCapData X).length=X.template.slots.length := by
  cases X <;> rfl

/-- The finite cap at a specified actual slot index. -/
@[expose] def slotCap (X : VineType) (i : Fin X.template.slots.length) : Finset ℕ :=
  ((slotCapData X)[i.1]'(by rw [slotCapData_length]; exact i.2)).1

/-- The graph reflection at that cap. Its inverse is part of the data. -/
@[expose] def slotReflection (X : VineType) (i : Fin X.template.slots.length) : ℕ ≃ ℕ :=
  ((slotCapData X)[i.1]'(by rw [slotCapData_length]; exact i.2)).2

/-- The endpoint inside a cap, for a bond crossing its boundary. -/
@[expose] def capEndpoint (C : Finset ℕ) (e : ℕ×ℕ) : ℕ := if e.1 ∈ C then e.1 else e.2

/-- Every cap reflection fixes both source joints. -/
theorem slotReflection_joints (X : VineType) : ∀ i,
    slotReflection X i 0=0 ∧ slotReflection X i 1=1 := by
  cases X <;> decide

/-- The two actual cap ports are interchanged, including coincident II ports. -/
theorem slotReflection_ports (X : VineType) : ∀ i,
    slotReflection X i (capEndpoint (slotCap X i) X.template.slots[i.1].1)=
      capEndpoint (slotCap X i) X.template.slots[i.1].2 ∧
    slotReflection X i (capEndpoint (slotCap X i) X.template.slots[i.1].2)=
      capEndpoint (slotCap X i) X.template.slots[i.1].1 := by
  cases X <;> decide

/-- The marked pair is exactly the only possible boundary crossing. -/
theorem slotCap_cut (X : VineType) : ∀ i,∀ e ∈ X.template.bonds,
    (e.1 ∈ slotCap X i ↔ e.2 ∈ slotCap X i) ∨
      e=X.template.slots[i.1].1 ∨ e=X.template.slots[i.1].2 := by
  cases X <;> decide

/-- Caps of different marked slots are disjoint. -/
theorem slotCaps_disjoint (X : VineType) : ∀ i j,i ≠ j → Disjoint (slotCap X i) (slotCap X j) := by
  cases X <;> decide

/-- Every other slot lies entirely outside the selected cap. -/
theorem other_slot_outside_cap (X : VineType) : ∀ i j,i ≠ j →
    X.template.slots[j.1].1.1 ∉ slotCap X i ∧ X.template.slots[j.1].1.2 ∉ slotCap X i ∧
    X.template.slots[j.1].2.1 ∉ slotCap X i ∧ X.template.slots[j.1].2.2 ∉ slotCap X i := by
  cases X <;> decide

/-- Reflection fixes every old atom outside its cap. -/
theorem slotReflection_outside (X : VineType) : ∀ i,∀ v : Fin X.template.n,
    v.1 ∉ slotCap X i → slotReflection X i v.1=v.1 := by
  cases X <;> decide

/-- The source coherence groups are invariant under each cap reflection. -/
theorem slotReflection_groups (X : VineType) : ∀ i,∀ g ∈ X.template.groups,
    ∀ v : Fin X.template.n,slotReflection X i v.1 ∈ g ↔ v.1 ∈ g := by
  cases X <;> decide

/-- Internal undirected bond multiplicities are preserved by reflection. -/
theorem slotReflection_internal_bonds (X : VineType) : ∀ i,
    (((X.template.bonds.filter (fun e => e.1 ∈ slotCap X i ∧ e.2 ∈ slotCap X i)).map
      (fun e => s(slotReflection X i e.1,slotReflection X i e.2))) : Multiset (Sym2 ℕ))=
    (((X.template.bonds.filter (fun e => e.1 ∈ slotCap X i ∧ e.2 ∈ slotCap X i)).map
      (fun e => s(e.1,e.2))) : Multiset (Sym2 ℕ)) := by
  cases X <;> decide

end WaveTurbulence.Vine.Param
