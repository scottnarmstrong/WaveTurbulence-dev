/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TopPartitionExpansion
public import WaveTurbulence.Foundations.XChain.LowerEmbeddings
public import WaveTurbulence.Foundations.XChain.BlockRootMembership
/-! Irreducibility of a graft forces irreducibility of its top-leaf partition. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem mem_biUnion_topLeafGroups {w : ℕ} (top : Fin w → TTree) (A : Finset (Fin w)) (a : GLeaf top) :
    a ∈ A.biUnion (topLeafGroups top) ↔ a.1.1 ∈ A := by
  simp [topLeafGroups]

theorem selected_block_of_attach_root {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (A : Finset (Fin w))
    (Q : Finset (Finset (GLeaf top))) (hQ : Q ⊆ P.parts)
    (hu : A.biUnion (topLeafGroups top) = Q.biUnion id) (B : P.parts) (k : Fin B.1.card)
    (hk : ((blockRootEquiv top P).symm ⟨B, k⟩).1.1 ∈ A) : B.1 ∈ Q := by
  classical
  let a := (blockRootEquiv top P).symm ⟨B, k⟩
  have hm := (mem_biUnion_topLeafGroups top A a).mpr hk
  have hq : a ∈ Q.biUnion id := (congrArg (fun S => a ∈ S) hu).mp hm
  obtain ⟨C, hCQ, haC⟩ := Finset.mem_biUnion.mp hq
  have haB := blockRootEquiv_symm_mem top P B k
  have he : B.1 = C := (P.part_eq_of_mem B.2 haB).symm.trans (P.part_eq_of_mem (hQ hCQ) haC)
  exact he.symm ▸ hCQ

theorem graft_lower_leaf_root {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (B : P.parts) (ℓ : GLeaf (low B).tree) :
    (((gardenLeafEquiv top P low).symm ⟨B, ℓ⟩).1.1) =
      ((blockRootEquiv top P).symm ⟨B, ℓ.1.1⟩).1.1 := by
  have he := congrArg (fun z : Fin w × TTree.Path => z.1) (gardenLeafEquiv_symm_val top P low B ℓ)
  exact he

theorem topPartitionIrreducible_of_graft {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hplain : ∀ B, (low B).IsPlain)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hirr : (gardenGraft sig top P low hplain hsig).Irreducible) : TopPartitionIrreducible top P := by
  classical
  intro A _ hAn hAu hQ
  obtain ⟨Q, hQP, hu⟩ := hQ
  apply hirr A hAn hAu
  intro ℓ hℓ
  refine ⟨fun he => ((gardenGraft sig top P low hplain hsig).pair_eq_iff ℓ).mp he rfl, ?_⟩
  obtain ⟨⟨B, l⟩, rfl⟩ := (gardenLeafEquiv top P low).symm.surjective ℓ
  have hr := graft_lower_leaf_root top P low B l
  have hroot : ((blockRootEquiv top P).symm ⟨B, l.1.1⟩).1.1 ∈ A := hr ▸ (Finset.mem_filter.mp hℓ).2
  have hBQ := selected_block_of_attach_root top P A Q hQP hu B l.1.1 hroot
  let l' := (low B).pair l
  let a' := (blockRootEquiv top P).symm ⟨B, l'.1.1⟩
  have hmemQ : a' ∈ Q.biUnion id := Finset.mem_biUnion.mpr
    ⟨B.1, hBQ, blockRootEquiv_symm_mem top P B l'.1.1⟩
  have hmemA := (congrArg (fun S => a' ∈ S) hu).mpr hmemQ
  have hroot' := (mem_biUnion_topLeafGroups top A a').mp hmemA
  have hr' := graft_lower_leaf_root top P low B l'
  have hm : (gardenLeafEquiv top P low).symm ⟨B, l'⟩ ∈
      (gardenGraft sig top P low hplain hsig).leavesOf A :=
    Finset.mem_filter.mpr ⟨mem_univ _, hr'.symm ▸ hroot'⟩
  exact (gardenGraft_pair_lower sig top P low hplain hsig B l).symm ▸ hm

end WaveTurbulence.Induct
