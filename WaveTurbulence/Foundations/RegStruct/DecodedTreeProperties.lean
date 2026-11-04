/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.DecodedTree

/-! # The actual tree carrier: pairedness, uniqueness, order and bare source regularity -/

public section
namespace WaveTurbulence.Reg
open TTree Finset

/-- The exact B2 tree decoder already implies source paired-tree typing. -/
theorem isPairedTree_of_decodesTree {X : RegChain} {G : Garden 1} (hX : X.DecodesTree G) : IsPairedTree G := by
  let L : GLeaf G.tree := ⟨(0,X.lonePath),by rw [hX.1]; exact chain_lone_mem_leaves X (G.sig 0)⟩
  have he : ∀ ℓ : GLeaf G.tree, ℓ = L ↔ ℓ.1.2 = X.lonePath := by
    intro ℓ
    constructor
    · intro h; exact congrArg (fun ℓ => ℓ.1.2) h
    · intro h; exact Subtype.ext (Prod.ext (Subsingleton.elim _ _) h)
  have hm : ∀ ℓ : GLeaf G.tree, G.mark ℓ ≠ none ↔ ℓ = L := by
    intro ℓ
    rw [hX.2.1 ℓ]
    by_cases hp : ℓ.1.2 = X.lonePath
    · rw [ite_eq_left hp]
      exact iff_of_true (by decide) ((he ℓ).mpr hp)
    · rw [ite_eq_right hp]
      exact iff_of_false (not_not_intro rfl) (fun h => hp ((he ℓ).mp h))
  have hset : (Finset.univ.filter fun ℓ : GLeaf G.tree => G.mark ℓ ≠ none) = {L} := by
    ext ℓ
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton,hm ℓ]
  constructor
  · rw [hset,Finset.card_singleton]
  · intro ℓ hmark
    exact (decodesTree_lone_iff hX ℓ).mpr ((he ℓ).mp ((hm ℓ).mp hmark))

/-- The constructed carrier is an actual source paired tree. -/
theorem decodedTree_isPairedTree (X : RegChain) (ζ : ℤˣ) : IsPairedTree (decodedTree X ζ) :=
  isPairedTree_of_decodesTree (decodedTree_decodes X ζ)

/-- A fixed code and root sign determine exactly one actual tree carrier. -/
theorem decodedTree_unique (X : RegChain) (ζ : ℤˣ) (G : Garden 1)
    (hX : X.DecodesTree G) (hζ : G.sig 0 = ζ) : G = decodedTree X ζ := by
  have hMG := decodesTree_matches_aux hX
  rw [hζ] at hMG
  have hMH := decodesTree_matches_aux (decodedTree_decodes X ζ)
  change (decodedTree X ζ).MatchesTreeCouple (treeAuxCode X ζ).raw at hMH
  apply tree_carrier_unique (isPairedTree_of_decodesTree hX) (decodedTree_isPairedTree X ζ) _ hMG hMH
  funext j
  fin_cases j
  exact hζ

/-- The actual constructed tree has precisely the code's branching order. -/
theorem decodedTree_order (X : RegChain) (ζ : ℤˣ) : (decodedTree X ζ).order = X.size := by
  change (∑ _ : Fin 1, (X.plug ζ .leaf).order) = _
  simp only [Fin.sum_univ_one,code_plug_order,TTree.order,Nat.add_zero]

/-- Fixed-sign actual tree decoding is injective on well-formed data. -/
theorem decodedTree_wf_injective (ζ : ℤˣ) :
    Function.Injective (fun X : {X : RegChain // X.wf = true} => decodedTree X.1 ζ) := by
  intro X Y he
  change decodedTree X.1 ζ = decodedTree Y.1 ζ at he
  have hx := decodedTree_decodes X.1 ζ
  rw [he] at hx
  exact Subtype.ext (wf_decodesTree_unique X.2 Y.2 hx (decodedTree_decodes Y.1 ζ))

/-- Source regularity of the actual auxiliary couple supplies source tree regularity. -/
theorem decodedTree_isRegular_of_aux (X : RegChain) (ζ : ℤˣ)
    (hAux : IsRegularCouple (decodedCouple (treeAuxCode X ζ))) : IsRegularTree (decodedTree X ζ) := by
  obtain ⟨R,hR,hrep⟩ := exists_rawRep_of_isRegularCouple (treeAuxCode X ζ) hAux
  have hM := decodesTree_matches_aux (decodedTree_decodes X ζ)
  change (decodedTree X ζ).MatchesTreeCouple (treeAuxCode X ζ).raw at hM
  exact ⟨decodedTree_isPairedTree X ζ,R,hR,(hrep.matchesTreeCouple_iff _).mpr hM⟩

/-- Every bare legal-chain code has an actual source-regular tree carrier of either sign. -/
theorem bareChain_decodedTree_isRegular (X : RegChain) (hX : BareChain X) (ζ : ℤˣ) :
    IsRegularTree (decodedTree X ζ) :=
  decodedTree_isRegular_of_aux X ζ (bareChain_aux_isRegular X hX ζ)

end WaveTurbulence.Reg
