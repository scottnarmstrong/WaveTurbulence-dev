/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.ChainSideSubCouples

/-! # Unique external continuation children in a type-2 decoding -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- The terminal couple is an actual closed sub-couple, with both original roots retained. -/
theorem type2_terminal_subCoupleAt (p n : RegChain) (q : RegCpl) :
    SubCoupleAt (decodedCouple (.type2 p n q)) ((0 : Fin 2),p.lonePath) (1,n.lonePath) := by
  apply subCoupleAt_of_decoded_block (.type2 p n q) q _ (decodedCouple_decodes _)
  · change Comb.subtree (p.plug 1 q.trees.1) p.lonePath = some q.trees.1
    exact plug_subtree_lonePath p 1 q.trees.1
  · change Comb.subtree (n.plug (-1) q.trees.2) n.lonePath = some q.trees.2
    exact plug_subtree_lonePath n (-1) q.trees.2
  · intro z hz
    change z ∈ p.pairsAt 1 (0,[]) ++ n.pairsAt (-1) (1,[]) ++ q.pairsAt (0,p.lonePath) (1,n.lonePath)
    exact List.mem_append_right _ hz

/-- Both terminal roots satisfy property L. -/
theorem type2_terminal_external (p n : RegChain) (q : RegCpl) :
    ExternalAt (decodedCouple (.type2 p n q)) ((0 : Fin 2),p.lonePath) ∧
      ExternalAt (decodedCouple (.type2 p n q)) (1,n.lonePath) := by
  have hs := type2_terminal_subCoupleAt p n q
  exact ⟨hs.external (by exact (by decide : (1 : Fin 2) ≠ 0)),
    hs.symm.external (by exact (by decide : (0 : Fin 2) ≠ 1))⟩

/-- At a nonempty positive outer chain, the continuation slot is the unique L-child. -/
theorem type2_positive_child_external_iff (k : MiniTreeCode) (r g q : RegCpl)
    (i s n : RegChain) (j : Fin 3) :
    ExternalAt (decodedCouple (.type2 (.pair k r g i s) n q)) ((0 : Fin 2),[j]) ↔ j = k.c := by
  apply chain_child_external_iff (.type2 (.pair k r g i s) n q) _ (decodedCouple_decodes _)
    (0,[]) k r g i s 1 q.trees.1
  · change Comb.subtree ((RegChain.pair k r g i s).plug 1 q.trees.1) [] = _
    simp [Comb.subtree]
  · intro z hz
    change z ∈ (RegChain.pair k r g i s).pairsAt 1 (0,[]) ++ n.pairsAt (-1) (1,[]) ++ _
    exact List.mem_append_left _ (List.mem_append_left _ hz)
  · exact (type2_terminal_external (.pair k r g i s) n q).1

/-- The same reconstruction holds at a nonempty negative outer chain. -/
theorem type2_negative_child_external_iff (k : MiniTreeCode) (r g q : RegCpl)
    (i s p : RegChain) (j : Fin 3) :
    ExternalAt (decodedCouple (.type2 p (.pair k r g i s) q)) ((1 : Fin 2),[j]) ↔ j = k.c := by
  apply chain_child_external_iff (.type2 p (.pair k r g i s) q) _ (decodedCouple_decodes _)
    (1,[]) k r g i s (-1) q.trees.2
  · change Comb.subtree ((RegChain.pair k r g i s).plug (-1) q.trees.2) [] = _
    simp [Comb.subtree]
  · intro z hz
    change z ∈ p.pairsAt 1 (0,[]) ++ (RegChain.pair k r g i s).pairsAt (-1) (1,[]) ++ _
    exact List.mem_append_left _ (List.mem_append_right _ hz)
  · exact (type2_terminal_external p (.pair k r g i s) q).2

end WaveTurbulence.Reg
