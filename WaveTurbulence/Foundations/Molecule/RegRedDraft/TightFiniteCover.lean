/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionNodeCoverage
public import Mathlib.Data.Fintype.EquivFin

/-! # A covering at the exact cardinality budget is an actual disjoint partition -/

public section
namespace WaveTurbulence.RegRed
open Finset

/-- A finite cover whose total multiplicity fits the covered set has neither
stray elements nor repeated ownership. This constructs the literal address map. -/
theorem tightCover_equiv {ι β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β]
    (A : Finset β) (B : ι → Finset β)
    (hcover : A ⊆ univ.biUnion B) (hbudget : (∑ i, (B i).card) ≤ A.card) :
    ∃ e : (Σ i, ↥(B i)) ≃ ↥A, ∀ p, (e p).1 = p.2.1 := by
  classical
  have hEq : univ.biUnion B = A :=
    (eq_of_subset_of_card_le hcover (card_biUnion_le.trans hbudget)).symm
  let f : (Σ i, ↥(B i)) → ↥A := fun p => ⟨p.2.1,by
    rw [← hEq]
    exact mem_biUnion.mpr ⟨p.1,mem_univ _,p.2.2⟩⟩
  have hsurj : Function.Surjective f := by
    intro a
    obtain ⟨i,hi,hb⟩ := mem_biUnion.mp (hcover a.2)
    exact ⟨⟨i,⟨a.1,hb⟩⟩,Subtype.ext rfl⟩
  have hle : Fintype.card (Σ i, ↥(B i)) ≤ Fintype.card ↥A := by
    simpa only [Fintype.card_sigma,Fintype.card_coe] using hbudget
  have hcard : Fintype.card (Σ i, ↥(B i)) = Fintype.card ↥A :=
    Nat.le_antisymm hle (Fintype.card_le_of_surjective f hsurj)
  exact ⟨Equiv.ofBijective f ((Fintype.bijective_iff_surjective_and_card f).mpr ⟨hsurj,hcard⟩),fun _ => rfl⟩

end WaveTurbulence.RegRed
