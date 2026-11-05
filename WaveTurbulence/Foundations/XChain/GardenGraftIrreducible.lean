/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LowerRootSelection
public import WaveTurbulence.Foundations.XChain.TopPartitionExpansion
/-! Irreducible leaf partitions and lower gardens give an irreducible graft. -/
public section
namespace WaveTurbulence.Induct
open Finset
open scoped Classical

theorem gardenGraft_irreducible {w : ℕ} (sig : Fin w → ℤˣ)
    (top : Fin w → TTree) (P : Finpartition (univ : Finset (GLeaf top)))
    (low : (B : P.parts) → Garden B.1.card) (hplain : ∀ B, (low B).IsPlain)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hP : TopPartitionIrreducible top P) (hirr : ∀ B, (low B).Irreducible) :
    (gardenGraft sig top P low hplain hsig).Irreducible := by
  intro A hAn hAu hcp
  have hall : ∀ B, selectedLowerRoots top P B A = ∅ ∨
      selectedLowerRoots top P B A = univ := by
    intro B
    by_cases he : selectedLowerRoots top P B A = ∅
    · exact Or.inl he
    · right
      by_contra hn
      exact hirr B _ (Finset.nonempty_iff_ne_empty.mpr he) hn
        (selectedLowerRoots_completelyPaired sig top P low hplain hsig A hcp B)
  let Q := P.parts.filter (fun B => ∀ a ∈ B, a.1.1 ∈ A)
  apply hP A (Finset.subset_univ _) hAn hAu
  refine ⟨Q, Finset.filter_subset _ _, ?_⟩
  ext a
  have hleft : a ∈ A.biUnion (topLeafGroups top) ↔ a.1.1 ∈ A := by
    simp [topLeafGroups]
  rw [hleft]
  constructor
  · intro ha
    let z := blockRootEquiv top P a
    have hz : (blockRootEquiv top P).symm ⟨z.1, z.2⟩ = a :=
      (blockRootEquiv top P).symm_apply_apply a
    have hsel : z.2 ∈ selectedLowerRoots top P z.1 A :=
      (mem_selectedLowerRoots top P z.1 A z.2).mpr (hz ▸ ha)
    have hu : selectedLowerRoots top P z.1 A = univ := by
      rcases hall z.1 with he | hu
      · exact False.elim (Finset.notMem_empty _ (he ▸ hsel))
      · exact hu
    have hzall : ∀ b ∈ z.1.1, b.1.1 ∈ A := by
      intro b hb
      have hek : ∃ k' : Fin z.1.1.card, (blockRootEquiv top P).symm ⟨z.1, k'⟩ = b := by
        refine ⟨z.1.1.equivFin ⟨b, hb⟩, ?_⟩
        rw [blockRootEquiv_symm_eq, Equiv.symm_apply_apply]
      obtain ⟨k', hk'⟩ := hek
      have hm : k' ∈ selectedLowerRoots top P z.1 A := hu ▸ mem_univ _
      exact hk' ▸ (mem_selectedLowerRoots top P z.1 A k').mp hm
    exact Finset.mem_biUnion.mpr ⟨z.1.1, Finset.mem_filter.mpr ⟨z.1.2, hzall⟩,
      hz ▸ blockRootEquiv_symm_mem top P z.1 z.2⟩
  · intro ha
    obtain ⟨B, hB, hab⟩ := Finset.mem_biUnion.mp ha
    exact (Finset.mem_filter.mp hB).2 a hab

end WaveTurbulence.Induct
