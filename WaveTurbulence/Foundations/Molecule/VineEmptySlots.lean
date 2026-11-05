/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSlotPorts
public import WaveTurbulence.Foundations.Molecule.VineAllocatedReduction
public import WaveTurbulence.Foundations.Molecule.VineEmptyRungsReverse
import Mathlib.Tactic

/-! # Empty endpoint labels force an entire expanded slot to be absent -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- All fresh atoms in a slot are absent if its two initial endpoint atoms
are absent. This is an actual-source reduction valid even for k=0,1,2. -/
theorem block_empty_slot_from_start (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    {A : Finset V} {x y : V} (hA : M.IsBlock A x y) (hC : GroupConnected M A) (hcard : 2<A.card)
    (pre post : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ)
    (hloc : X.template.slots.zip R.k=pre++(s,k)::post)
    (hstart : ∀ v ∈ S,R.f v=s.1.1 ∨ R.f v=s.2.1 → v ∉ A) :
    let N := (pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n
    ∀ v ∈ S,N ≤ R.f v → R.f v<N+2*k → v ∉ A := by
  obtain ⟨Q,hmem,hports,hlabels⟩ := R.has_rungSequence_ports pre post s k hloc
  dsimp only at hlabels ⊢
  have hu0 := hstart (Q.u 0) (hmem 0).1 (Or.inl hports.1)
  have hv0 := hstart (Q.v 0) (hmem 0).2 (Or.inr hports.2.1)
  have hempty := block_empty_fullRungSequence M hM hA hC hcard Q hu0 hv0
  intro v hv hlo hhi
  obtain ⟨i,hi,hin,he⟩ := allocatedSequence_covers M S R.f R.injOn Q
    (fun i hi hin => ⟨(hmem i).1,(hmem i).2,hlabels i hi hin⟩) hv hlo hhi
  rcases he with rfl | rfl
  · exact (hempty i hi hin).1
  · exact (hempty i hi hin).2

/-- The terminal endpoint pair gives the same conclusion, in the reverse
direction, with no lower bound on the slot length. -/
theorem block_empty_slot_from_end (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    {A : Finset V} {x y : V} (hA : M.IsBlock A x y) (hC : GroupConnected M A) (hcard : 2<A.card)
    (pre post : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ)
    (hloc : X.template.slots.zip R.k=pre++(s,k)::post)
    (hend : ∀ v ∈ S,R.f v=s.1.2 ∨ R.f v=s.2.2 → v ∉ A) :
    let N := (pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n
    ∀ v ∈ S,N ≤ R.f v → R.f v<N+2*k → v ∉ A := by
  obtain ⟨Q,hmem,hports,hlabels⟩ := R.has_rungSequence_ports pre post s k hloc
  dsimp only at hlabels ⊢
  have huN := hend (Q.u (k+1)) (hmem (k+1)).1 (Or.inl hports.2.2.1)
  have hvN := hend (Q.v (k+1)) (hmem (k+1)).2 (Or.inr hports.2.2.2)
  have hempty := block_empty_fullRungSequence_reverse M hM hA hC hcard Q huN hvN
  intro v hv hlo hhi
  obtain ⟨i,hi,hin,he⟩ := allocatedSequence_covers M S R.f R.injOn Q
    (fun i hi hin => ⟨(hmem i).1,(hmem i).2,hlabels i hi hin⟩) hv hlo hhi
  rcases he with rfl | rfl
  · exact (hempty i hi hin).1
  · exact (hempty i hi hin).2

end WaveTurbulence.Vine
