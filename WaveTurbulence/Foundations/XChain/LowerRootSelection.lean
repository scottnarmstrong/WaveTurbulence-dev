/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LowerEmbeddings
public import WaveTurbulence.Foundations.XChain.BlockRootMembership
/-! A selection of top roots induces a literal selection in each lower garden. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

noncomputable def selectedLowerRoots {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (B : P.parts)
    (A : Finset (Fin w)) : Finset (Fin B.1.card) :=
  univ.filter (fun k => ((blockRootEquiv top P).symm ⟨B, k⟩).1.1 ∈ A)

theorem mem_selectedLowerRoots {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (B : P.parts)
    (A : Finset (Fin w)) (k : Fin B.1.card) :
    k ∈ selectedLowerRoots top P B A ↔
      ((blockRootEquiv top P).symm ⟨B, k⟩).1.1 ∈ A := by
  simp only [selectedLowerRoots, mem_filter, mem_univ, true_and]

theorem lowerLeaf_mem_leavesOf_iff {w : ℕ} (sig : Fin w → ℤˣ)
    (top : Fin w → TTree) (P : Finpartition (univ : Finset (GLeaf top)))
    (low : (B : P.parts) → Garden B.1.card) (hplain : ∀ B, (low B).IsPlain)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (B : P.parts) (A : Finset (Fin w)) (ℓ : GLeaf (low B).tree) :
    lowerLeafEmbedding top P low B ℓ ∈ (gardenGraft sig top P low hplain hsig).leavesOf A ↔
      ℓ ∈ (low B).leavesOf (selectedLowerRoots top P B A) := by
  have he : (lowerLeafEmbedding top P low B ℓ).1.1 =
      ((blockRootEquiv top P).symm ⟨B, ℓ.1.1⟩).1.1 :=
    by
      have hraw := gardenLeafEquiv_symm_val top P low B ℓ
      have he0 := congrArg (fun x : Fin w × TTree.Path => x.1) hraw
      exact he0
  constructor
  · intro h
    have hm := (Finset.mem_filter.mp h).2
    exact Finset.mem_filter.mpr ⟨mem_univ _,
      (mem_selectedLowerRoots top P B A ℓ.1.1).mpr (he ▸ hm)⟩
  · intro h
    have hm := (mem_selectedLowerRoots top P B A ℓ.1.1).mp (Finset.mem_filter.mp h).2
    exact Finset.mem_filter.mpr ⟨mem_univ _, he.symm ▸ hm⟩

theorem selectedLowerRoots_completelyPaired {w : ℕ} (sig : Fin w → ℤˣ)
    (top : Fin w → TTree) (P : Finpartition (univ : Finset (GLeaf top)))
    (low : (B : P.parts) → Garden B.1.card) (hplain : ∀ B, (low B).IsPlain)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (A : Finset (Fin w))
    (hA : (gardenGraft sig top P low hplain hsig).CompletelyPaired
      ((gardenGraft sig top P low hplain hsig).leavesOf A)) (B : P.parts) :
    (low B).CompletelyPaired ((low B).leavesOf (selectedLowerRoots top P B A)) := by
  intro ℓ hℓ
  obtain ⟨hne, hmem⟩ := hA (lowerLeafEmbedding top P low B ℓ)
    ((lowerLeaf_mem_leavesOf_iff sig top P low hplain hsig B A ℓ).mpr hℓ)
  have hp := lowerLeafEmbedding_pair sig top P low hplain hsig B ℓ
  refine ⟨fun he => hne (hp.trans (congrArg (lowerLeafEmbedding top P low B) he)), ?_⟩
  have hm : lowerLeafEmbedding top P low B ((low B).pair ℓ) ∈
      (gardenGraft sig top P low hplain hsig).leavesOf A := hp ▸ hmem
  exact (lowerLeaf_mem_leavesOf_iff sig top P low hplain hsig B A _).mp hm

end WaveTurbulence.Induct
