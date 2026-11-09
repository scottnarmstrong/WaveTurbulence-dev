/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.SourceVinePartitionInput
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.SourceVinePartitionInput`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 Literal TARGET vinechainlem L1930–L1933 (DH23 Lemma 8.1), provider S1 STAGE1-COMB. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open Set Finset

/-- The source collection consists of disjoint actual atomic groups. Its coverage
is over actual designated vine-like objects, including hyper-adjoint objects. -/
def IsSourceVinePartition {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    (M : Molecule V D) (collection : Set (Finset V)) : Prop :=
  (∀ S ∈ collection, ∃ a b,
    Src.IsHV Src.γL M S a b ∨ Src.IsVC Src.γL M S a b ∨
      Src.IsHVC Src.γL M S a b ∨ Src.IsDV Src.γL M S a b) ∧
  collection.Pairwise (fun S T => Disjoint S T) ∧
  ∀ P : Src.Object Src.γL M, ∃ S ∈ collection, P.atoms ⊆ S

/-- TARGET vinechainlem, L1930–L1933. This separate combinatorial input has no gamma
restriction or analytic estimate. Provider: S1 STAGE1-COMB, upstream of S2a/S2/S4. -/
abbrev VinePartitionGate : Prop :=
  ∀ (V D : Type) [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ M : Molecule V D, M.IsMolecule → ∃! collection, IsSourceVinePartition M collection

/-- Every selected atomic group belongs to the actual finite atom set. -/
theorem IsSourceVinePartition.subset_atoms {V D : Type*} [DecidableEq V] [Fintype D]
    [DecidableEq D] {M : Molecule V D} {collection : Set (Finset V)}
    (h : IsSourceVinePartition M collection) {S : Finset V} (hS : S ∈ collection) : S ⊆ M.atoms := by
  obtain ⟨a, b, hHV | hVC | hHVC | hDV⟩ := h.1 S hS
  · obtain ⟨e, _, hX⟩ := hHV
    exact hX.block.1
  · exact hVC.1.1
  · obtain ⟨e, _, hblock, _⟩ := hHVC
    exact hblock.1
  · obtain ⟨-, A, B, hA, hB, _, rfl⟩ := hDV
    exact Finset.union_subset (Src.isBlock_of_isSomeVine hA).1 (Src.isBlock_of_isSomeVine hB).1

/-- The source collection is finite without assuming a finite ambient atom-name type. -/
theorem IsSourceVinePartition.finite {V D : Type*} [DecidableEq V] [Fintype D]
    [DecidableEq D] {M : Molecule V D} {collection : Set (Finset V)}
    (h : IsSourceVinePartition M collection) : collection.Finite := by
  classical
  apply (M.atoms.powerset.finite_toSet).subset
  intro S hS
  exact Finset.mem_powerset.mpr (h.subset_atoms hS)

end WaveTurbulence.GammaLow.FinalCount.H
