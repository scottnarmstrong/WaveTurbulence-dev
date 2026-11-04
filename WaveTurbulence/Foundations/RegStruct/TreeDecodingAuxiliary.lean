/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.TreeAuxiliaryCode

/-! # A decoded paired tree matches its actual auxiliary couple code -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- The auxiliary code has exactly the source's two tree shapes. -/
theorem treeAuxCode_trees (X : RegChain) (ζ : ℤˣ) :
    (treeAuxCode X ζ).trees = if ζ = 1 then (X.plug 1 .leaf,.leaf) else (.leaf,X.plug (-1) .leaf) := by
  by_cases hζ : ζ = 1 <;> simp only [treeAuxCode,hζ,ite_true,ite_false,joinChains_trees]
  · rfl
  · rfl

/-- In the actual decoder, a leaf is lone exactly at the recorded terminal path. -/
theorem decodesTree_lone_iff {X : RegChain} {G : Garden 1} (hX : X.DecodesTree G) (ℓ : GLeaf G.tree) :
    G.IsLone ℓ ↔ ℓ.1.2 = X.lonePath := by
  change G.mark ℓ = some MarkTag.lower ↔ _
  rw [hX.2.1 ℓ]
  by_cases he : ℓ.1.2 = X.lonePath <;> simp [he]

/-- The tree-code decoder supplies the source's literal tree-to-couple matching relation. -/
theorem decodesTree_matches_aux {X : RegChain} {G : Garden 1} (hX : X.DecodesTree G) :
    G.MatchesTreeCouple (treeAuxCode X (G.sig 0)).raw := by
  by_cases hζ : G.sig 0 = 1
  · simp only [Garden.MatchesTreeCouple,hζ,ite_true]
    refine ⟨?_,?_,?_⟩
    · have ht := treeAuxCode_trees X 1
      change (treeAuxCode X 1).trees.1 = G.tree 0
      rw [ht,ite_eq_left rfl]
      simpa only [hζ] using hX.1.symm
    · have ht := treeAuxCode_trees X 1
      change (treeAuxCode X 1).trees.2 = .leaf
      rw [ht,ite_eq_left rfl]
    · intro ℓ
      by_cases hl : G.IsLone ℓ
      · rw [ite_eq_left hl]
        have hp := (decodesTree_lone_iff hX ℓ).mp hl
        rw [hp]
        exact (mem_symmPairs_iff _ _).mpr (Or.inl (treeAuxCode_positive_terminal_pair X))
      · rw [ite_eq_right hl]
        have hn : ℓ.1.2 ≠ X.lonePath := fun he => hl ((decodesTree_lone_iff hX ℓ).mpr he)
        have hp := hX.2.2 ℓ hn
        rw [hζ] at hp
        exact symmPairs_subset_of_pairs_subset (treeAuxCode_positive_pair_inclusion X) _
          (chain_pairs_lift X 1 0 _ hp)
  · have hm : G.sig 0 = -1 := (Int.units_eq_one_or (G.sig 0)).resolve_left hζ
    simp only [Garden.MatchesTreeCouple,hζ,ite_false]
    rw [hm]
    refine ⟨?_,?_,?_⟩
    · have ht := treeAuxCode_trees X (-1)
      change (treeAuxCode X (-1)).trees.2 = G.tree 0
      rw [ht,ite_eq_right (by decide)]
      simpa only [hm] using hX.1.symm
    · have ht := treeAuxCode_trees X (-1)
      change (treeAuxCode X (-1)).trees.1 = .leaf
      rw [ht,ite_eq_right (by decide)]
    · intro ℓ
      by_cases hl : G.IsLone ℓ
      · rw [ite_eq_left hl]
        have hp := (decodesTree_lone_iff hX ℓ).mp hl
        rw [hp]
        exact (mem_symmPairs_iff _ _).mpr (Or.inr (treeAuxCode_negative_terminal_pair X))
      · rw [ite_eq_right hl]
        have hn : ℓ.1.2 ≠ X.lonePath := fun he => hl ((decodesTree_lone_iff hX ℓ).mpr he)
        have hp := hX.2.2 ℓ hn
        rw [hm] at hp
        exact symmPairs_subset_of_pairs_subset (treeAuxCode_negative_pair_inclusion X) _
          (chain_pairs_lift X (-1) 1 _ hp)

/-- The actual paired-tree decoder is injective on all well-formed chain data. -/
theorem wf_decodesTree_unique {X Y : RegChain} {G : Garden 1}
    (hwX : X.wf = true) (hwY : Y.wf = true) (hX : X.DecodesTree G) (hY : Y.DecodesTree G) : X = Y := by
  have he := decodedCouple_eq_of_matchingTree _ _ G (decodesTree_matches_aux hX) (decodesTree_matches_aux hY)
  exact treeAuxCode_injective (G.sig 0)
    (wf_code_unique (treeAuxCode_wf X _ hwX) (treeAuxCode_wf Y _ hwY) he)

end WaveTurbulence.Reg
