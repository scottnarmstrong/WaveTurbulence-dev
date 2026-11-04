/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.TreeAuxiliaryPairs

/-! # The source-regular tree structure theorem with all chain data unique -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- An actual paired tree matched to a single-chain auxiliary code has that chain decoding. -/
theorem matches_aux_decodesTree (X : RegChain) (G : Garden 1) (hG : IsPairedTree G)
    (hM : G.MatchesTreeCouple (treeAuxCode X (G.sig 0)).raw) : X.DecodesTree G := by
  refine ⟨?_,?_,?_⟩
  · have ht := hM.1
    by_cases hζ : G.sig 0 = 1
    · change (treeAuxCode X (G.sig 0)).raw.tree (if G.sig 0 = 1 then 0 else 1) = G.tree 0 at ht
      rw [hζ,ite_eq_left rfl] at ht
      change (treeAuxCode X 1).trees.1 = G.tree 0 at ht
      rw [treeAuxCode_trees,ite_eq_left rfl] at ht
      simpa only [hζ] using ht.symm
    · have hm : G.sig 0 = -1 := (Int.units_eq_one_or _).resolve_left hζ
      change (treeAuxCode X (G.sig 0)).raw.tree (if G.sig 0 = 1 then 0 else 1) = G.tree 0 at ht
      rw [ite_eq_right hζ,hm] at ht
      change (treeAuxCode X (-1)).trees.2 = G.tree 0 at ht
      rw [treeAuxCode_trees,ite_eq_right (by decide)] at ht
      simpa only [hm] using ht.symm
  · intro ℓ
    by_cases he : ℓ.1.2 = X.lonePath
    · rw [ite_eq_left he]
      exact (matching_aux_lone_iff X G hM ℓ).mpr he
    · rw [ite_eq_right he]
      by_contra hm
      have hl := hG.2 ℓ hm
      exact he ((matching_aux_lone_iff X G hM ℓ).mp hl)
  · intro ℓ hn
    have hl : ¬ G.IsLone ℓ := fun he => hn ((matching_aux_lone_iff X G hM ℓ).mp he)
    have hp := hM.2.2 ℓ
    by_cases hζ : G.sig 0 = 1
    · change (((if G.sig 0 = 1 then 0 else 1 : Fin 2),ℓ.1.2),
        if G.IsLone ℓ then (1-(if G.sig 0 = 1 then 0 else 1),[]) else
          ((if G.sig 0 = 1 then 0 else 1),(G.pair ℓ).1.2)) ∈
        symmPairs (treeAuxCode X (G.sig 0)).raw.2 at hp
      rw [hζ,ite_eq_left rfl,ite_eq_right hl] at hp
      have hi := treeAuxCode_positive_internal X ℓ.1.2 (G.pair ℓ).1.2 hp
      have hx := chain_pairs_project X 1 0 ℓ.1.2 (G.pair ℓ).1.2 hi
      rw [hζ]
      have he0 : ((0 : Fin 1),ℓ.1.2) = ℓ.1 := Prod.ext (Subsingleton.elim _ _) rfl
      have he1 : ((0 : Fin 1),(G.pair ℓ).1.2) = (G.pair ℓ).1 := Prod.ext (Subsingleton.elim _ _) rfl
      rw [he0,he1] at hx
      exact hx
    · have hm : G.sig 0 = -1 := (Int.units_eq_one_or _).resolve_left hζ
      change (((if G.sig 0 = 1 then 0 else 1 : Fin 2),ℓ.1.2),
        if G.IsLone ℓ then (1-(if G.sig 0 = 1 then 0 else 1),[]) else
          ((if G.sig 0 = 1 then 0 else 1),(G.pair ℓ).1.2)) ∈
        symmPairs (treeAuxCode X (G.sig 0)).raw.2 at hp
      rw [ite_eq_right hζ,ite_eq_right hl,hm] at hp
      have hi := treeAuxCode_negative_internal X ℓ.1.2 (G.pair ℓ).1.2 hp
      have hx := chain_pairs_project X (-1) 1 ℓ.1.2 (G.pair ℓ).1.2 hi
      rw [hm]
      have he0 : ((0 : Fin 1),ℓ.1.2) = ℓ.1 := Prod.ext (Subsingleton.elim _ _) rfl
      have he1 : ((0 : Fin 1),(G.pair ℓ).1.2) = (G.pair ℓ).1 := Prod.ext (Subsingleton.elim _ _) rfl
      rw [he0,he1] at hx
      exact hx

/-- Every actual source-regular tree has well-formed chain structure data. -/
theorem isRegularTree_exists_wf_decodes (G : Garden 1) (hG : IsRegularTree G) :
    ∃ X : RegChain, X.wf = true ∧ X.DecodesTree G := by
  obtain ⟨C,hw,_,hM⟩ := isRegularTree_exists_wf_matching G hG
  obtain ⟨X,hX,he⟩ := wf_matchingTree_aux_shape C G hw hM
  rw [he] at hM
  exact ⟨X,hX,matches_aux_decodesTree X G hG.1 hM⟩

/-- TARGET's tree structure theorem: all its chain, mini-tree and inserted-couple data are unique. -/
theorem isRegularTree_existsUnique_structure (G : Garden 1) (hG : IsRegularTree G) :
    ∃! X : {X : RegChain // X.wf = true}, X.1.DecodesTree G := by
  obtain ⟨X,hw,hX⟩ := isRegularTree_exists_wf_decodes G hG
  exact ⟨⟨X,hw⟩,hX,fun Y hY => Subtype.ext (wf_decodesTree_unique Y.2 hw hY hX)⟩

end WaveTurbulence.Reg
