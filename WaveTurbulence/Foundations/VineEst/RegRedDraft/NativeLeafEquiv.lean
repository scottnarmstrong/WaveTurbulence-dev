/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeLeafMap

/-! # All actual leaves occur once among the native replacement leaves -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

theorem card_chainInternalLeaf {w : ℕ} {S : Garden w} (D : ReconstructionData S) (b : GBranch S.tree) :
    Fintype.card (ChainInternalLeaf D b) = 2 * (D.tree b).size := by
  classical
  let H := decodedTree (D.tree b) (nodeSign S.sig b.1)
  let L : GLeaf H.tree := chainLoneLeaf (D.tree b) (nodeSign S.sig b.1)
  have hi (ℓ : GLeaf H.tree) : ℓ.1.2 ≠ (D.tree b).lonePath ↔ ¬ ℓ = L := by
    apply not_congr
    exact ⟨fun h => Subtype.ext (Prod.ext (Subsingleton.elim _ _) h),fun h => congrArg (fun ℓ => ℓ.1.2) h⟩
  have hc : Fintype.card (ChainInternalLeaf D b) = Fintype.card {ℓ : GLeaf H.tree // ¬ ℓ = L} :=
    Fintype.card_congr (Equiv.subtypeEquivRight hi)
  rw [hc,Fintype.card_subtype_compl]
  have h1 : Fintype.card {ℓ : GLeaf H.tree // ℓ = L} = 1 := by simp
  rw [h1,Comb.card_gleaf]
  have he : (∑ j, (H.tree j).order) = (D.tree b).size := decodedTree_order _ _
  rw [he]
  omega

theorem card_nativeLeaf_couple {w : ℕ} {S : Garden w} (D : ReconstructionData S) (p : SourcePair S) :
    Fintype.card (NativeLeaf D (.inl p)) = 2 * (D.couple p).size + 2 := by
  change Fintype.card (GLeaf (decodedCouple (D.couple p)).tree) = _
  rw [Comb.card_gleaf]
  exact congrArg (fun n => 2*n+2) (decodedCouple_order _)

theorem card_nativeLeaves {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) :
    Fintype.card (Σ s : ReplacementSlot S, NativeLeaf D s) = 2 * (S.order + D.size) + w := by
  classical
  rw [Fintype.card_sigma,Fintype.sum_sum_type]
  have ht (b : GBranch S.tree) : Fintype.card (NativeLeaf D (.inr b)) = 2 * (D.tree b).size :=
    card_chainInternalLeaf D b
  simp only [card_nativeLeaf_couple,ht,Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,smul_eq_mul]
  have hp := sourcePair_card_twice S hS
  unfold ReconstructionData.size
  omega

theorem nativeLeafMap_bijective {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) : Function.Bijective (nativeLeafMap D hS) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨nativeLeafMap_injective D hS,?_⟩
  rw [card_nativeLeaves D hS,Comb.card_gleaf,D.forest_order hS]

/-- The actual full leaves are precisely the native couple leaves and the
nonlone native paired-tree leaves. In particular, no input factor is lost. -/
noncomputable def nativeLeafEquiv {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) : (Σ s : ReplacementSlot S, NativeLeaf D s) ≃ GLeaf (D.forest hS) :=
  Equiv.ofBijective (nativeLeafMap D hS) (nativeLeafMap_bijective D hS)

end WaveTurbulence.RegRed
