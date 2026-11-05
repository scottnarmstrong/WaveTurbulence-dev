/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSlotDoubleStart
public import WaveTurbulence.Foundations.Molecule.VineZeroSlotPropagation
public import WaveTurbulence.Foundations.Molecule.VineEmptySlots
import Mathlib.Tactic

/-! # Slot propagation for every nonnegative rung count -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Empty initial endpoints force the old doubled terminal pair absent
for every nonnegative rung count, with the zero convention included. -/
theorem block_slot_double_end_absent_all (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    {A : Finset V} {x y : V} (hA : M.IsBlock A x y) (hC : GroupConnected M A) (hcard : 2<A.card)
    (pre post : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ)
    (hloc : X.template.slots.zip R.k=pre++(s,k)::post)
    (hdouble : 2 ≤ X.template.bonds.count (s.1.2,s.2.2)) (hne : s.1.2 ≠ s.2.2)
    (hstart : ∀ v ∈ S,R.f v=s.1.1 ∨ R.f v=s.2.1 → v ∉ A) :
    ∀ v ∈ S,R.f v=s.1.2 ∨ R.f v=s.2.2 → v ∉ A := by
  by_cases hk : k=0
  · subst k
    exact block_zero_slot_double_end_absent M hM R hA hC hcard pre post s hloc hdouble hne hstart
  · exact block_slot_double_end_absent M hM R hA hC hcard pre post s k (by omega)
      hloc hdouble hne hstart

/-- Empty terminal endpoints force the old doubled initial pair absent
for every nonnegative rung count, including the unexpanded slot. -/
theorem block_slot_double_start_absent_all (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    {A : Finset V} {x y : V} (hA : M.IsBlock A x y) (hC : GroupConnected M A) (hcard : 2<A.card)
    (pre post : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ)
    (hloc : X.template.slots.zip R.k=pre++(s,k)::post)
    (hdouble : 2 ≤ X.template.bonds.count (s.1.1,s.2.1)) (hne : s.1.1 ≠ s.2.1)
    (hend : ∀ v ∈ S,R.f v=s.1.2 ∨ R.f v=s.2.2 → v ∉ A) :
    ∀ v ∈ S,R.f v=s.1.1 ∨ R.f v=s.2.1 → v ∉ A := by
  by_cases hk : k=0
  · subst k
    exact block_zero_slot_double_start_absent M hM R hA hC hcard pre post s hloc hdouble hne hend
  · exact block_slot_double_start_absent M hM R hA hC hcard pre post s k (by omega)
      hloc hdouble hne hend

end WaveTurbulence.Vine
