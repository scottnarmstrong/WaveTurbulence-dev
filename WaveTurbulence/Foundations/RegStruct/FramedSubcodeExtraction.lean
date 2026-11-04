/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.ChainExternalSegments
public import WaveTurbulence.Foundations.RegStruct.Type1ComponentRecovery

/-! # Transport of actual code extractions into an arbitrary ambient frame -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- Extracting through a two-root frame agrees with extracting in the code's original trees. -/
theorem frameAddress_subtree (tree : Fin 2 → TTree) (a b : Fin 2 × Path) (C : RegCpl)
    (ha : Comb.subtree (tree a.1) a.2 = some C.trees.1)
    (hb : Comb.subtree (tree b.1) b.2 = some C.trees.2) (z : Fin 2 × Path) :
    Comb.subtree (tree (frameAddress a b z).1) (frameAddress a b z).2 =
      Comb.subtree (coupleForest C z.1) z.2 := by
  obtain ⟨j,p⟩ := z
  fin_cases j
  · simpa [frameAddress,coupleForest] using subtree_addrExt tree a _ ha p
  · simpa [frameAddress,coupleForest] using subtree_addrExt tree b _ hb p

/-- Literal inclusion of a code pair block is preserved by global frame transport. -/
theorem framed_pair_inclusion (C D : RegCpl) (a b x y : Fin 2 × Path)
    (h : ∀ p ∈ D.pairsAt x y, p ∈ C.raw.2) :
    ∀ p ∈ D.pairsAt (frameAddress a b x) (frameAddress a b y), p ∈ C.pairsAt a b := by
  intro p hp
  rw [couple_pairsAt_map D (frameAddress a b) (frameAddress_respects a b) x y] at hp
  rw [pairsAt_frameAddress]
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact List.mem_map.mpr ⟨q,h q hq,rfl⟩

/-- Every child of an actual framed type-1 block is an actual ambient sub-couple. -/
theorem framed_type1_side_subCoupleAt (Q : RegCpl) (G : Garden 2) (hG : Q.Decodes G)
    (c : MiniCplCode) (r g d : RegCpl) (a b : Fin 2 × Path)
    (ha : Comb.subtree (G.tree a.1) a.2 = some (RegCpl.type1 c r g d).trees.1)
    (hb : Comb.subtree (G.tree b.1) b.2 = some (RegCpl.type1 c r g d).trees.2)
    (hP : ∀ p ∈ (RegCpl.type1 c r g d).pairsAt a b, p ∈ Q.raw.2) (j : Fin 3) :
    SubCoupleAt G (frameAddress a b (type1Frame c j).1) (frameAddress a b (type1Frame c j).2) := by
  apply subCoupleAt_of_decoded_block Q (type1Side r g d j) G hG
  · rw [frameAddress_subtree G.tree a b _ ha hb,(type1_frame_extraction c r g d j).1]
  · rw [frameAddress_subtree G.tree a b _ ha hb,(type1_frame_extraction c r g d j).2]
  · intro p hp
    exact hP p (framed_pair_inclusion (.type1 c r g d) _ a b _ _
      (type1_frame_pair_inclusion c r g d j) p hp)

/-- The two global roots of a framed side couple remain in distinct original trees. -/
theorem framed_type1_indices_ne (c : MiniCplCode) (a b : Fin 2 × Path) (hidx : b.1 ≠ a.1) (j : Fin 3) :
    (frameAddress a b (type1Frame c j).2).1 ≠ (frameAddress a b (type1Frame c j).1).1 := by
  fin_cases j
  · simpa [type1Frame,frameAddress,addrExt] using hidx
  · simpa [type1Frame,frameAddress,addrExt] using hidx.symm
  · simpa [type1Frame,frameAddress,addrExt] using hidx

/-- Every child of either root in a framed type-1 block has property L. -/
theorem framed_type1_all_children_external (Q : RegCpl) (G : Garden 2) (hG : Q.Decodes G)
    (c : MiniCplCode) (r g d : RegCpl) (a b : Fin 2 × Path)
    (ha : Comb.subtree (G.tree a.1) a.2 = some (RegCpl.type1 c r g d).trees.1)
    (hb : Comb.subtree (G.tree b.1) b.2 = some (RegCpl.type1 c r g d).trees.2)
    (hP : ∀ p ∈ (RegCpl.type1 c r g d).pairsAt a b, p ∈ Q.raw.2)
    (hidx : b.1 ≠ a.1) (j : Fin 3) :
    ExternalAt G (addrExt a [j]) ∧ ExternalAt G (addrExt b [j]) := by
  have hs := framed_type1_side_subCoupleAt Q G hG c r g d a b ha hb hP
  have h0 := (hs 0).external (framed_type1_indices_ne c a b hidx 0)
  have h1 := (hs 1).external (framed_type1_indices_ne c a b hidx 1)
  have h2 := (hs 2).external (framed_type1_indices_ne c a b hidx 2)
  have h3 := (hs 0).symm.external (framed_type1_indices_ne c a b hidx 0).symm
  have h4 := (hs 1).symm.external (framed_type1_indices_ne c a b hidx 1).symm
  have h5 := (hs 2).symm.external (framed_type1_indices_ne c a b hidx 2).symm
  constructor <;> fin_cases j <;> fin_cases c
  all_goals first
    | simpa [type1Frame,frameAddress,MiniCplCode.partner] using h0
    | simpa [type1Frame,frameAddress,MiniCplCode.partner] using h1
    | simpa [type1Frame,frameAddress,MiniCplCode.partner] using h2
    | simpa [type1Frame,frameAddress,MiniCplCode.partner] using h3
    | simpa [type1Frame,frameAddress,MiniCplCode.partner] using h4
    | simpa [type1Frame,frameAddress,MiniCplCode.partner] using h5

end WaveTurbulence.Reg
