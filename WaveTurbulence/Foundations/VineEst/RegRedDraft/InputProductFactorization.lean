/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.InputLeafTransport

/-! # Exact input-product factorization in the actual skeleton reduction -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

noncomputable def inputFactor {w : ℕ} (G : Garden w) {M : Type*} [One M]
    (f : GNode G.tree → M) (ℓ : GLeaf G.tree) : M :=
  if ℓ ∈ inputLeaves G then f ℓ.toNode else 1

theorem inputFactor_eq_of_mem_iff {w v : ℕ} (G : Garden w) (H : Garden v)
    {M : Type*} [One M] (f : GNode G.tree → M) (g : GNode H.tree → M)
    (ℓ : GLeaf G.tree) (q : GLeaf H.tree) (hp : ℓ ∈ inputLeaves G ↔ q ∈ inputLeaves H)
    (hf : f ℓ.toNode = g q.toNode) : inputFactor G f ℓ = inputFactor H g q := by
  unfold inputFactor
  exact ite_congr (propext hp) (fun _ => hf) (fun _ => rfl)

theorem prod_inputLeaves_eq_prod_inputFactor {w : ℕ} (G : Garden w) {M : Type*} [CommMonoid M]
    (f : GNode G.tree → M) : (∏ ℓ ∈ inputLeaves G, f ℓ.toNode) = ∏ ℓ, inputFactor G f ℓ := by
  classical
  simp only [inputLeaves,Finset.prod_filter,inputFactor,Finset.mem_filter,Finset.mem_univ,true_and]

/-- TARGET redkg: every source input factor belongs to exactly one actual native
replacement, with its original node value. The paired-tree lower leaf contributes
no input, exactly as in KTstar. -/
theorem inputProduct_reconstruction {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) {M : Type*} [CommMonoid M] (f : GNode (D.forest hS) → M) :
    (∏ ℓ ∈ inputLeaves (D.garden hS), f ℓ.toNode) =
      (∏ p : SourcePair S, ∏ ℓ ∈ inputLeaves (nativeCoupleGarden D hS p),
        f ((nativeCoupleForest D hS p).nodeEmbedding ℓ.toNode)) *
      (∏ b : GBranch S.tree, ∏ ℓ ∈ inputLeaves (decodedTree (D.tree b) (nodeSign S.sig b.1)),
        f (chainContextNode D hS b ℓ.toNode)) := by
  classical
  apply (prod_inputLeaves_eq_prod_inputFactor (D.garden hS) f).trans
  apply ((nativeLeafEquiv D hS).prod_comp (inputFactor (D.garden hS) f)).symm.trans
  rw [Fintype.prod_sigma,Fintype.prod_sum_type]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro p _
    let g : GNode (nativeCoupleGarden D hS p).tree → M :=
      fun a => f ((nativeCoupleForest D hS p).nodeEmbedding a)
    apply Eq.trans (b := ∏ ℓ : GLeaf (nativeCoupleGarden D hS p).tree,
      inputFactor (nativeCoupleGarden D hS p) g ℓ)
    · apply Finset.prod_congr rfl
      intro ℓ _
      change inputFactor (D.garden hS) f ((nativeCoupleForest D hS p).leafEmbedding ℓ) = _
      exact inputFactor_eq_of_mem_iff (D.garden hS) (nativeCoupleGarden D hS p) f g _ ℓ
        (mem_inputLeaves_couple D hS p ℓ)
        (congrArg f (subforest_node_leaf (nativeCoupleForest D hS p) ℓ)).symm
    · exact (prod_inputLeaves_eq_prod_inputFactor (nativeCoupleGarden D hS p) g).symm
  · apply Finset.prod_congr rfl
    intro b _
    let H := decodedTree (D.tree b) (nodeSign S.sig b.1)
    let g : GNode H.tree → M := fun a => f (chainContextNode D hS b a)
    apply Eq.trans (b := ∏ ℓ : ChainInternalLeaf D b, inputFactor H g ℓ.1)
    · apply Finset.prod_congr rfl
      intro ℓ _
      change inputFactor (D.garden hS) f (chainContextLeaf D hS b ℓ) = _
      exact inputFactor_eq_of_mem_iff (D.garden hS) H f g _ ℓ.1
        (mem_inputLeaves_chain D hS b ℓ) (congrArg f (chainContextLeaf_toNode D hS b ℓ))
    · apply (prod_chainInternalLeaf D b (inputFactor H g) (fun ℓ hℓ => ?_)).trans
        (prod_inputLeaves_eq_prod_inputFactor H g).symm
      exact ite_eq_right (not_mem_inputLeaves_chain_lone D b ℓ hℓ)

end WaveTurbulence.RegRed
