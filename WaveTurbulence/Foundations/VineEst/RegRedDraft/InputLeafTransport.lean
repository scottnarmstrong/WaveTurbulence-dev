/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeLeafEquiv
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.RelativeDecorations
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeSigns

/-! # Exact source input-leaf predicates under native leaf transport -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

theorem mem_inputLeaves_iff {w : ℕ} (G : Garden w) (ℓ : GLeaf G.tree) :
    ℓ ∈ inputLeaves G ↔ G.sign ℓ.toNode = 1 ∧ G.mark ℓ = none := by
  simp only [inputLeaves,Finset.mem_filter,Finset.mem_univ,true_and]

theorem mem_inputLeaves_couple {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (p : SourcePair S) (ℓ : GLeaf (nativeCoupleGarden D hS p).tree) :
    (nativeCoupleForest D hS p).leafEmbedding ℓ ∈ inputLeaves (D.garden hS) ↔
      ℓ ∈ inputLeaves (nativeCoupleGarden D hS p) := by
  classical
  let E := nativeCoupleForest D hS p
  have hs : (D.garden hS).sign (E.leafEmbedding ℓ).toNode =
      (nativeCoupleGarden D hS p).sign ℓ.toNode :=
    (congrArg (D.garden hS).sign (subforest_node_leaf E ℓ)).symm.trans
      (subforest_node_sign E S.sig ℓ.toNode).symm
  have hm := Comb.RootedSubforest.inducedGarden_plain (G := D.garden hS) E
    (nativeCoupleForest_closed D hS p) ℓ
  change (nativeCoupleGarden D hS p).mark ℓ = none at hm
  constructor
  · intro h
    have hp := (mem_inputLeaves_iff _ _).mp h
    exact (mem_inputLeaves_iff _ _).mpr ⟨hs.symm.trans hp.1,hm⟩
  · intro h
    have hp := (mem_inputLeaves_iff _ _).mp h
    exact (mem_inputLeaves_iff _ _).mpr ⟨hs.trans hp.1,D.garden_plain hS _⟩

theorem mem_inputLeaves_chain {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (b : GBranch S.tree) (ℓ : ChainInternalLeaf D b) :
    chainContextLeaf D hS b ℓ ∈ inputLeaves (D.garden hS) ↔
      ℓ.1 ∈ inputLeaves (decodedTree (D.tree b) (nodeSign S.sig b.1)) := by
  classical
  have hs := (congrArg (D.garden hS).sign (chainContextLeaf_toNode D hS b ℓ)).trans
    (chainContextNode_sign D hS b ℓ.1.toNode)
  have hm : (decodedTree (D.tree b) (nodeSign S.sig b.1)).mark ℓ.1 = none :=
    ((decodedTree_decodes _ _).2.1 ℓ.1).trans (ite_eq_right ℓ.2)
  constructor
  · intro h
    have hp := (mem_inputLeaves_iff _ _).mp h
    exact (mem_inputLeaves_iff _ _).mpr ⟨hs.symm.trans hp.1,hm⟩
  · intro h
    have hp := (mem_inputLeaves_iff _ _).mp h
    exact (mem_inputLeaves_iff _ _).mpr ⟨hs.trans hp.1,D.garden_plain hS _⟩

theorem not_mem_inputLeaves_chain_lone {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (b : GBranch S.tree) (ℓ : GLeaf (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree)
    (hℓ : ℓ.1.2 = (D.tree b).lonePath) :
    ℓ ∉ inputLeaves (decodedTree (D.tree b) (nodeSign S.sig b.1)) := by
  intro hm
  have hmark := (Finset.mem_filter.mp hm).2.2
  have he := (decodedTree_decodes (D.tree b) (nodeSign S.sig b.1)).2.1 ℓ
  rw [ite_eq_left hℓ] at he
  exact (by decide : (some MarkTag.lower : Option MarkTag) ≠ none) (he.symm.trans hmark)

theorem prod_chainInternalLeaf {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (b : GBranch S.tree) {M : Type*} [CommMonoid M]
    (f : GLeaf (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree → M)
    (hf : ∀ ℓ, ℓ.1.2 = (D.tree b).lonePath → f ℓ = 1) :
    (∏ ℓ : ChainInternalLeaf D b, f ℓ.1) = ∏ ℓ, f ℓ := by
  classical
  let A := Finset.univ.filter (fun ℓ : GLeaf (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree =>
    ℓ.1.2 ≠ (D.tree b).lonePath)
  have hA : ∀ ℓ, ℓ ∈ A ↔ ℓ.1.2 ≠ (D.tree b).lonePath := by
    intro ℓ
    simp only [A,Finset.mem_filter,Finset.mem_univ,true_and]
  apply (Finset.prod_subtype A hA f).symm.trans
  apply Finset.prod_subset (Finset.subset_univ _)
  intro ℓ _ hn
  exact hf ℓ (by simpa only [hA,not_not] using hn)

end WaveTurbulence.RegRed
