/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.X2EDraft.FlowerKernel
public import WaveTurbulence.Foundations.XChain.LeafPairUniqueness
public import WaveTurbulence.Foundations.XChain.GraftExpansionFinite
public import WaveTurbulence.Foundations.XChain.BlockRootMembership

/-!
# X2E-3, step 6: the index sets

For flower trees `tops` of width `2P`:
- `pbF j = {𝔣_j, 𝔣_{j⊕1}}` (the pair blocks) and `pairSet`;
- `pairPartitionEquiv`: the partitions `Q` of the non-flower leaves `≃` the partitions of all leaves containing every
  pair block (`withPairs`, `dropPairs`);
- `sigP`: the block signatures; on a pair block the lower data are unique (`lowerData_unique_of_pair`);
- `mkFlowerAt`: flower graft data at `tops` from a partition with pair blocks and a family of lower data.
-/

@[expose] public section

namespace WaveTurbulence.X2E

open Finset Induct SysAPI
open scoped Classical

/-! ## Pair blocks -/

section Pairs

variable {Pm : ℕ} (tops : Fin (2 * Pm) → FTree)

/-- The pair block of tree `j`: its flower and the flower of its partner. -/
noncomputable def pbF (j : Fin (2 * Pm)) : Finset (GLeaf (ftop tops)) :=
  {flowerAt tops j, flowerAt tops (partner j)}

/-- The pair blocks. -/
noncomputable def pairSet : Finset (Finset (GLeaf (ftop tops))) := univ.image (pbF tops)

theorem flowerAt_injective : Function.Injective (flowerAt tops) := fun _ _ h =>
  congrArg (fun l : GLeaf (ftop tops) => l.1.1) h

theorem pbF_partner (j : Fin (2 * Pm)) : pbF tops (partner j) = pbF tops j := by
  unfold pbF
  rw [partner_partner, pair_comm]

theorem mem_pbF (j : Fin (2 * Pm)) (ℓ : GLeaf (ftop tops)) :
    ℓ ∈ pbF tops j ↔ ℓ = flowerAt tops j ∨ ℓ = flowerAt tops (partner j) := by
  unfold pbF
  rw [mem_insert, mem_singleton]

theorem flowerAt_mem_pbF (j : Fin (2 * Pm)) : flowerAt tops j ∈ pbF tops j :=
  (mem_pbF tops j _).mpr (Or.inl rfl)

theorem disjoint_pbF_nfLeaves (j : Fin (2 * Pm)) : Disjoint (pbF tops j) (nfLeaves tops) := by
  rw [Finset.disjoint_left]
  intro ℓ hℓ hn
  rcases (mem_pbF tops j ℓ).mp hℓ with rfl | rfl
  · exact flowerAt_notMem_nfLeaves tops j hn
  · exact flowerAt_notMem_nfLeaves tops _ hn

theorem pbF_eq_or_disjoint (i j : Fin (2 * Pm)) : pbF tops i = pbF tops j ∨ Disjoint (pbF tops i) (pbF tops j) := by
  by_cases h1 : i = j
  · exact Or.inl (by rw [h1])
  by_cases h2 : i = partner j
  · left
    rw [h2, pbF_partner]
  right
  rw [Finset.disjoint_left]
  intro ℓ hi hj
  rcases (mem_pbF tops i ℓ).mp hi with rfl | rfl <;> rcases (mem_pbF tops j _).mp hj with h | h
  · exact h1 (flowerAt_injective tops h)
  · exact h2 (flowerAt_injective tops h)
  · exact h2 (by rw [← flowerAt_injective tops h, partner_partner])
  · have h' := congrArg partner (flowerAt_injective tops h)
    rw [partner_partner, partner_partner] at h'
    exact h1 h'

theorem pbF_nonempty (j : Fin (2 * Pm)) : (pbF tops j).Nonempty := ⟨flowerAt tops j, flowerAt_mem_pbF tops j⟩

theorem card_pbF (j : Fin (2 * Pm)) : (pbF tops j).card = 2 := by
  unfold pbF
  exact card_pair fun h => partner_ne j (flowerAt_injective tops h).symm

theorem pbF_mem_pairSet (j : Fin (2 * Pm)) : pbF tops j ∈ pairSet tops := mem_image_of_mem _ (mem_univ j)

theorem empty_notMem_pairSet : ∅ ∉ pairSet tops := by
  intro h
  obtain ⟨j, -, hj⟩ := mem_image.mp h
  exact (pbF_nonempty tops j).ne_empty hj

theorem mem_pbF_self_of_notMem (ℓ : GLeaf (ftop tops)) (hℓ : ℓ ∉ nfLeaves tops) : ℓ ∈ pbF tops ℓ.1.1 :=
  (mem_pbF tops _ ℓ).mpr (Or.inl (eq_flowerAt_of_notMem_nfLeaves tops hℓ))

theorem notMem_nfLeaves_of_mem_pairSet {B : Finset (GLeaf (ftop tops))} (hB : B ∈ pairSet tops)
    {ℓ : GLeaf (ftop tops)} (hℓ : ℓ ∈ B) : ℓ ∉ nfLeaves tops := by
  obtain ⟨j, -, rfl⟩ := mem_image.mp hB
  exact fun hn => Finset.disjoint_left.mp (disjoint_pbF_nfLeaves tops j) hℓ hn

end Pairs

/-! ## Partitions with pair blocks -/

section Partitions

variable {Pm : ℕ} (tops : Fin (2 * Pm) → FTree)

/-- **Adding the pair blocks** to a partition of the non-flower leaves. -/
noncomputable def withPairs (Q : Finpartition (nfLeaves tops)) : Finpartition (univ : Finset (GLeaf (ftop tops))) :=
  Finpartition.ofErase (Q.parts ∪ pairSet tops) (by
    rw [Finset.supIndep_iff_pairwiseDisjoint, coe_union, Set.pairwiseDisjoint_union]
    refine ⟨Q.disjoint, ?_, ?_⟩
    · intro B₁ h₁ B₂ h₂ hne
      obtain ⟨i, -, rfl⟩ := mem_image.mp h₁
      obtain ⟨j, -, rfl⟩ := mem_image.mp h₂
      exact (pbF_eq_or_disjoint tops i j).resolve_left hne
    · intro B₁ h₁ B₂ h₂ _
      exact Finset.disjoint_left.mpr fun _ hℓ₁ hℓ₂ =>
        notMem_nfLeaves_of_mem_pairSet tops h₂ hℓ₂ (Q.le h₁ hℓ₁))
    (by
      rw [sup_union, Q.sup_parts]
      refine eq_univ_of_forall fun ℓ => ?_
      rw [sup_eq_union, mem_union]
      by_cases h : ℓ ∈ nfLeaves tops
      · exact Or.inl h
      · exact Or.inr (Finset.mem_sup.mpr ⟨pbF tops ℓ.1.1, pbF_mem_pairSet tops _, mem_pbF_self_of_notMem tops ℓ h⟩))

theorem withPairs_parts (Q : Finpartition (nfLeaves tops)) : (withPairs tops Q).parts = Q.parts ∪ pairSet tops := by
  unfold withPairs
  rw [Finpartition.ofErase_parts]
  refine erase_eq_of_notMem fun h => ?_
  rcases mem_union.mp h with h | h
  · exact Q.bot_notMem h
  · exact empty_notMem_pairSet tops h

theorem disjoint_parts_pairSet (Q : Finpartition (nfLeaves tops)) : Disjoint Q.parts (pairSet tops) := by
  rw [Finset.disjoint_left]
  intro B hQ hP
  obtain ⟨ℓ, hℓ⟩ := Q.nonempty_of_mem_parts hQ
  exact notMem_nfLeaves_of_mem_pairSet tops hP hℓ (Q.le hQ hℓ)

theorem sup_sdiff_pairSet (P : Finpartition (univ : Finset (GLeaf (ftop tops))))
    (hP : ∀ j, pbF tops j ∈ P.parts) : (P.parts \ pairSet tops).sup id = nfLeaves tops := by
  ext ℓ
  rw [Finset.mem_sup]
  constructor
  · rintro ⟨B, hB, hℓ⟩
    by_contra hn
    have hBP := (mem_sdiff.mp hB)
    have he := P.eq_of_mem_parts hBP.1 (hP ℓ.1.1) hℓ (mem_pbF_self_of_notMem tops ℓ hn)
    exact hBP.2 (he ▸ pbF_mem_pairSet tops _)
  · intro hn
    obtain ⟨B, hB, hℓ⟩ := P.exists_mem (mem_univ ℓ)
    refine ⟨B, mem_sdiff.mpr ⟨hB, fun hp => notMem_nfLeaves_of_mem_pairSet tops hp hℓ hn⟩, hℓ⟩

/-- **Removing the pair blocks.** -/
noncomputable def dropPairs (P : Finpartition (univ : Finset (GLeaf (ftop tops))))
    (hP : ∀ j, pbF tops j ∈ P.parts) : Finpartition (nfLeaves tops) :=
  P.ofSubset sdiff_subset (sup_sdiff_pairSet tops P hP)

theorem dropPairs_parts (P : Finpartition (univ : Finset (GLeaf (ftop tops)))) (hP : ∀ j, pbF tops j ∈ P.parts) :
    (dropPairs tops P hP).parts = P.parts \ pairSet tops := rfl

theorem pairSet_subset (P : Finpartition (univ : Finset (GLeaf (ftop tops)))) (hP : ∀ j, pbF tops j ∈ P.parts) :
    pairSet tops ⊆ P.parts := by
  intro B hB
  obtain ⟨j, -, rfl⟩ := mem_image.mp hB
  exact hP j

/-- **Partitions of the non-flower leaves are partitions of all leaves with the pair blocks.** -/
noncomputable def pairPartitionEquiv :
    Finpartition (nfLeaves tops) ≃
      {P : Finpartition (univ : Finset (GLeaf (ftop tops))) // ∀ j, pbF tops j ∈ P.parts} where
  toFun Q := ⟨withPairs tops Q, fun j => by
    rw [withPairs_parts]
    exact mem_union_right _ (pbF_mem_pairSet tops j)⟩
  invFun P := dropPairs tops P.1 P.2
  left_inv Q := by
    apply Finpartition.ext
    change (withPairs tops Q).parts \ pairSet tops = Q.parts
    rw [withPairs_parts, union_sdiff_right, sdiff_eq_self_of_disjoint (disjoint_parts_pairSet tops Q)]
  right_inv P := by
    apply Subtype.ext
    apply Finpartition.ext
    change (withPairs tops (dropPairs tops P.1 P.2)).parts = P.1.parts
    rw [withPairs_parts, dropPairs_parts, sdiff_union_of_subset (pairSet_subset tops P.1 P.2)]

end Partitions

/-! ## Lower data -/

section Lower

/-- The signature of a block. -/
noncomputable def sigP {Pm : ℕ} (tops : Fin (2 * Pm) → FTree) (P : Finpartition (univ : Finset (GLeaf (ftop tops))))
    (B : P.parts) : Fin B.1.card → ℤˣ :=
  fun k => nodeSign (altFlowerSig Pm) ((blockRootEquiv (ftop tops) P).symm ⟨B, k⟩).1

theorem lowerData_subsingleton_of_card {w p N : ℕ} (hw : w = 2) (sig : Fin w → ℤˣ) :
    Subsingleton (LowerGraftData sig p N) := by
  subst hw
  infer_instance

theorem lowerData_nonempty_of_card {w p N : ℕ} (hw : w = 2) (sig : Fin w → ℤˣ)
    (hs : sig ⟨1, by omega⟩ = -sig ⟨0, by omega⟩) : Nonempty (LowerGraftData sig p N) := by
  subst hw
  exact ⟨leafPairLowerData sig hs p N⟩

variable {Pm : ℕ} {ζ : ℤˣ} {tops : Fin (2 * Pm) → FTree} (hsign : ∀ j, (tops j).sign = ζ)

include hsign in
theorem nodeSign_flowerAt (j : Fin (2 * Pm)) :
    nodeSign (altFlowerSig Pm) (flowerAt tops j).1 = ζ * altFlowerSig Pm j :=
  FlowerAt.fl_sign hsign j

include hsign in
theorem nodeSign_partner (j : Fin (2 * Pm)) :
    nodeSign (altFlowerSig Pm) (flowerAt tops (partner j)).1 = -nodeSign (altFlowerSig Pm) (flowerAt tops j).1 := by
  rw [nodeSign_flowerAt hsign, nodeSign_flowerAt hsign, altFlowerSig_partner, mul_neg]

include hsign in
/-- On a pair block, the lower data are unique. -/
theorem lowerData_unique_of_pair (P : Finpartition (univ : Finset (GLeaf (ftop tops)))) (B : P.parts)
    (hB : B.1 ∈ pairSet tops) (p N : ℕ) : Nonempty (Unique (LowerGraftData (sigP tops P B) p N)) := by
  obtain ⟨j, -, hj⟩ := mem_image.mp hB
  have hc : B.1.card = 2 := hj ▸ card_pbF tops j
  have := lowerData_subsingleton_of_card (p := p) (N := N) hc (sigP tops P B)
  have hmem : ∀ k : Fin B.1.card, (B.1.equivFin.symm k).1 = flowerAt tops j ∨
      (B.1.equivFin.symm k).1 = flowerAt tops (partner j) := by
    intro k
    have h : (B.1.equivFin.symm k).1 ∈ pbF tops j := by
      rw [hj]
      exact (B.1.equivFin.symm k).2
    exact (mem_pbF tops j _).mp h
  have hne : (B.1.equivFin.symm ⟨1, by omega⟩).1 ≠ (B.1.equivFin.symm ⟨0, by omega⟩).1 := by
    intro h
    have h' := B.1.equivFin.symm.injective (Subtype.ext h)
    exact absurd (congrArg Fin.val h') (by simp)
  have hs : sigP tops P B ⟨1, by omega⟩ = -sigP tops P B ⟨0, by omega⟩ := by
    change nodeSign (altFlowerSig Pm) (B.1.equivFin.symm ⟨1, by omega⟩).1.1 =
      -nodeSign (altFlowerSig Pm) (B.1.equivFin.symm ⟨0, by omega⟩).1.1
    rcases hmem ⟨1, by omega⟩ with h1 | h1 <;> rcases hmem ⟨0, by omega⟩ with h0 | h0
    · exact absurd (h1.trans h0.symm) hne
    · rw [h1, h0, nodeSign_partner hsign, neg_neg]
    · rw [h1, h0, nodeSign_partner hsign]
    · exact absurd (h1.trans h0.symm) hne
  obtain ⟨D⟩ := lowerData_nonempty_of_card (p := p) (N := N) hc (sigP tops P B) hs
  exact ⟨uniqueOfSubsingleton D⟩

end Lower

/-! ## Flower data from a partition and lower data -/

section Make

variable {Pm p N : ℕ} {tops : Fin (2 * Pm) → FTree}

/-- **Flower graft data** from a partition with pair blocks and lower data on every block. -/
def mkFlowerAt (P : Finpartition (univ : Finset (GLeaf (ftop tops)))) (hP : ∀ j, pbF tops j ∈ P.parts)
    (fam : (B : P.parts) → LowerGraftData (sigP tops P B) p N) : FlowerAt Pm p tops where
  partition := P
  low B := (fam B).low
  plain B := (fam B).plain
  sign B k := congrFun (fam B).sign k
  component B := (fam B).component
  pair_mem j := hP j

end Make

end WaveTurbulence.X2E
