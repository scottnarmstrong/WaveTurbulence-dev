/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.RegRedDraft.NativeBranchMap

/-! # The complete native skeleton / replacement clock-coordinate equivalence -/

@[expose] public section
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

theorem card_chainBranchPath {w : ℕ} {S : Garden w} (D : ReconstructionData S) (b : GBranch S.tree) :
    Fintype.card (ChainBranchPath D b) = (D.tree b).size := by
  rw [Fintype.card_coe,Comb.card_branching,code_plug_order]
  rfl

theorem card_nativeBranches {w : ℕ} {S : Garden w} (D : ReconstructionData S) :
    Fintype.card (Σ slot : ReplacementSlot S, NativeBranch D slot) = S.order + D.size := by
  classical
  rw [Fintype.card_sigma,Fintype.sum_sum_type]
  have hc (p : SourcePair S) : Fintype.card (NativeBranch D (.inl p)) = (D.couple p).size :=
    (Comb.card_gbranch (decodedCouple (D.couple p)).tree).trans (decodedCouple_order _)
  have ht (b : GBranch S.tree) : Fintype.card (NativeBranch D (.inr b)) = (D.tree b).size+1 := by
    change Fintype.card (Option (ChainBranchPath D b)) = _
    rw [Fintype.card_option,card_chainBranchPath]
  simp only [hc,ht,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    smul_eq_mul,mul_one,Comb.card_gbranch]
  unfold ReconstructionData.size Garden.order
  omega

theorem nativeBranchMap_bijective {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) : Function.Bijective (nativeBranchMap D hS) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨nativeBranchMap_injective D hS,?_⟩
  rw [card_nativeBranches,Comb.card_gbranch,D.forest_order hS]

/-- Every clock of the actual full garden is a unique core or native replacement
clock; the equivalence is constructed from the literal source embeddings. -/
noncomputable def nativeBranchEquiv {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) : (Σ slot : ReplacementSlot S, NativeBranch D slot) ≃ GBranch (D.forest hS) :=
  Equiv.ofBijective (nativeBranchMap D hS) (nativeBranchMap_bijective D hS)

end WaveTurbulence.RegRed
