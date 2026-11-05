/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.Order.Partition.Finpartition
/-! Reading a finite-set partition as a partition of its subtype carrier. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset
open scoped Classical

noncomputable def subtypePartition {α : Type*} [DecidableEq α] {s : Finset α} (P : Finpartition s) :
    Finpartition (univ : Finset ↥s) :=
  Finpartition.ofSetoid (Setoid.ker (fun a : ↥s => P.part a.1))

theorem subtypePartition_mem_part {α : Type*} [DecidableEq α] {s : Finset α} (P : Finpartition s) (a b : ↥s) :
    b ∈ (subtypePartition P).part a ↔ b.1 ∈ P.part a.1 := by
  rw [subtypePartition, Finpartition.mem_part_ofSetoid_iff_rel]
  change (P.part a.1 = P.part b.1) ↔ _
  exact eq_comm.trans (P.mem_part_iff_part_eq_part b.2 a.2).symm

end WaveTurbulence.Induct
