/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.EmbeddedCodeDecoding
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.EmbeddedCouple

/-! # Included literal code pairs decode the actual induced subcouple -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem subCoupleGarden_decodes_of_block {w : ℕ} (C : RegCpl) (G : Garden w)
    (a b : GNode G.tree) (hc : Comb.IsSubCouple G a b) (hs : G.sign a = 1)
    (ha : Comb.subtree (G.tree a.1.1) a.1.2 = some C.trees.1)
    (hb : Comb.subtree (G.tree b.1.1) b.1.2 = some C.trees.2)
    (hP : ∀ p ∈ C.pairsAt a.1 b.1, p ∈ sourcePairs G) :
    C.Decodes (Comb.subCoupleGarden hc) := by
  let E := Comb.twoRootSubforest a b (Comb.subCouple_incomparable hc)
  have ht : (Comb.subCoupleGarden hc).tree = coupleForest C := by
    funext i
    have hna : Comb.nodeSubtree a = C.trees.1 := Option.some.inj ((Comb.nodeSubtree_spec a).symm.trans ha)
    have hnb : Comb.nodeSubtree b = C.trees.2 := Option.some.inj ((Comb.nodeSubtree_spec b).symm.trans hb)
    change Comb.nodeSubtree (![a,b] i) = coupleForest C i
    fin_cases i
    · exact hna
    · exact hnb
  apply decodes_of_actual_embedding C (Comb.subCoupleGarden hc) G
    (Comb.subCoupleGarden_isCouple_of_positive_left hc hs) ht a.1 b.1
    (Comb.RootedSubforest.leafEmbedding E)
  · intro ℓ
    change ((![a,b] ℓ.1.1).1.1,(![a,b] ℓ.1.1).1.2 ++ ℓ.1.2) = frameAddress a.1 b.1 ℓ.1
    obtain ⟨⟨i,p⟩,hi⟩ := ℓ
    fin_cases i <;> rfl
  · exact E.inducedGarden_pair (Comb.subCouple_forest_closed hc)
  · exact hP

end WaveTurbulence.Reg.Skeleton
