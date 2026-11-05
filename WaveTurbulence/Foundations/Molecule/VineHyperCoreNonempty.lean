/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineFoldAllocationCover
public import WaveTurbulence.Foundations.Molecule.VineSlotPorts
public import WaveTurbulence.Foundations.Molecule.VineAllocatedReduction
public import WaveTurbulence.Foundations.Molecule.VineHyperEmptySequence
import Mathlib.Tactic

/-! # Every hyper-block subset contains an original vine-core atom -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- TARGET subsetvc, nonempty core reduction: a hyper-block subset cannot
live entirely on newly inserted rungs. Every fresh atom belongs to one slot,
and a slot with all four old endpoints absent has no hyper-block rung atoms. -/
theorem hyperBlock_has_core_label (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S A : Finset V} {a b x y : V}
    (R : VineRealization M X S a b) (hAS : A ⊆ S) (hH : Mole.IsHyperBlock M A x y) :
    ∃ z ∈ A,R.f z<X.template.n := by
  by_contra hh
  have hold (v : V) (_hv : v ∈ S) (hi : R.f v<X.template.n) : v ∉ A := by
    intro hvA
    exact hh ⟨v,hvA,hi⟩
  obtain ⟨e,_he,hB⟩ := hH
  have hxA : x ∈ A := hB.2.1
  have hxS := hAS hxA
  have hxlo : X.template.n ≤ R.f x := by
    by_contra hx
    exact hh ⟨x,hxA,by omega⟩
  have hxhi := mem_range.mp (R.image_eq ▸ mem_image_of_mem R.f hxS)
  obtain ⟨pre,post,s,k,hloc,hlo,hhi⟩ :=
    fold_fresh_allocation X.template (X.template.slots.zip R.k) (R.f x) hxlo hxhi
  obtain ⟨Q,hmem,hports,hlabels⟩ := R.has_rungSequence_ports pre post s k hloc
  have hslot : s ∈ X.template.slots := by
    have hs : (s,k) ∈ X.template.slots.zip R.k := by
      rw [hloc]
      exact List.mem_append_right _ List.mem_cons_self
    exact (List.of_mem_zip hs).1
  have hs := template_slot_endpoints X s hslot
  have hu0 := hold (Q.u 0) (hmem 0).1 (hports.1.symm ▸ hs.1)
  have hv0 := hold (Q.v 0) (hmem 0).2 (hports.2.1.symm ▸ hs.2.2.1)
  have huN := hold (Q.u (k+1)) (hmem (k+1)).1 (hports.2.2.1.symm ▸ hs.2.1)
  have hvN := hold (Q.v (k+1)) (hmem (k+1)).2 (hports.2.2.2.symm ▸ hs.2.2.2)
  have hH : Mole.IsHyperBlock M A x y := ⟨e,_he,hB⟩
  have hempty := hyperBlock_empty_ended_sequence M hM hH Q hu0 hv0 huN hvN
  obtain ⟨i,hi,hin,he⟩ := allocatedSequence_covers M S R.f R.injOn Q
    (fun i hi hin => ⟨(hmem i).1,(hmem i).2,hlabels i hi hin⟩) hxS hlo hhi
  rcases he with h | h
  · exact (hempty i hi hin).1 (h ▸ hxA)
  · exact (hempty i hi hin).2 (h ▸ hxA)

end WaveTurbulence.Vine
