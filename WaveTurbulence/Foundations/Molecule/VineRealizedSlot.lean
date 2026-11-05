/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSlotPorts
public import WaveTurbulence.Foundations.Molecule.VineSlotRailFrame
public import WaveTurbulence.Foundations.Molecule.VineAllocatedReduction
public import WaveTurbulence.Foundations.Molecule.VineFoldAllocationCover
public import WaveTurbulence.Foundations.Molecule.VineGroupAllocation
public import WaveTurbulence.Foundations.Molecule.VineDoubleNeighborUnique
import Mathlib.Tactic

/-! # Bundled actual slot coordinates for intrinsic group recognition -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- An actual slot with its exact allocation and original four ports. -/
structure RealizedSlot {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (R : VineRealization M X S a b) where
  pre : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)
  post : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)
  s : (ℕ×ℕ)×(ℕ×ℕ)
  k : ℕ
  loc : X.template.slots.zip R.k=pre++(s,k)::post
  Q : FullRungSequence M k
  mem : ∀ i,Q.u i ∈ S ∧ Q.v i ∈ S
  ports : R.f (Q.u 0)=s.1.1 ∧ R.f (Q.v 0)=s.2.1 ∧
    R.f (Q.u (k+1))=s.1.2 ∧ R.f (Q.v (k+1))=s.2.2
  labels : ∀ i,1 ≤ i → i ≤ k →
    R.f (Q.u i)=(pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n+(i-1) ∧
    R.f (Q.v i)=(pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n+k+(i-1)

/-- Every fresh actual atom occurs in a realized slot. -/
theorem VineRealization.fresh_slot {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b v : V} (R : VineRealization M X S a b)
    (hv : v ∈ S) (hf : X.template.n ≤ R.f v) :
    ∃ A : RealizedSlot R,∃ i,1 ≤ i ∧ i ≤ A.k ∧ (v=A.Q.u i ∨ v=A.Q.v i) := by
  have hhi : R.f v<(X.expand R.k).n := mem_range.mp (R.image_eq ▸ mem_image_of_mem R.f hv)
  obtain ⟨pre,post,s,k,hloc,hlo,hhi⟩ := fold_fresh_allocation X.template
    (X.template.slots.zip R.k) (R.f v) hf hhi
  obtain ⟨Q,hmem,hports,hlabels⟩ := R.has_rungSequence_ports pre post s k hloc
  have hQ i hi hin := And.intro (hmem i).1 (And.intro (hmem i).2 (hlabels i hi hin))
  obtain ⟨i,hi,hin,he⟩ := allocatedSequence_covers M S R.f R.injOn Q hQ hv hlo hhi
  exact ⟨⟨pre,post,s,k,hloc,Q,hmem,hports,hlabels⟩,i,hi,hin,he⟩

namespace RealizedSlot
variable {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    {R : VineRealization M X S a b} (A : RealizedSlot R)

/-- Each actual slot supplies an injective coordinate frame on both rails. -/
@[expose] def frame : RailLabelFrame A.Q :=
  R.slot_rail_frame A.pre A.post A.s A.k A.loc A.Q A.ports A.labels

omit [DecidableEq D] in
/-- The literal group of an allocated actual rung persists in the expansion. -/
theorem rung_group (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ A.k) :
    [R.f (A.Q.u i),R.f (A.Q.v i)] ∈ (X.expand R.k).groups := by
  rw [(A.labels i hi hin).1,(A.labels i hi hin).2]
  have hh := fold_allocated_group X.template A.pre A.post A.s A.k (i-1) (by omega)
  rw [← A.loc] at hh
  exact hh

/-- The two rung incidences can be restricted from its complete upper row. -/
@[expose] def double (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ A.k) :
    TwoIncidences M (A.Q.u i) (A.Q.v i) where
  dart := fun j => (A.Q.upper i hi hin).dart ⟨j.1,by omega⟩
  injective := by
    intro j l he
    exact Fin.ext (congrArg (fun j : Fin 4 => j.1) ((A.Q.upper i hi hin).injective he))
  atom_eq := fun _ => (A.Q.upper i hi hin).atom_eq _
  neighbor_eq := by intro j; fin_cases j <;> exact (A.Q.upper i hi hin).neighbor_eq _

end RealizedSlot
end WaveTurbulence.Vine
