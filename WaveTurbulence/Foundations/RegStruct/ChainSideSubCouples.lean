/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.ExternalAddresses

/-! # Actual side sub-couples of a represented chain block -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- A literal red side pair block is included in its chain's pair list. -/
theorem chain_red_pair_inclusion {w : ℕ} (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain)
    (ζ : ℤˣ) (a : Fin w × Path) :
    ∀ p ∈ r.pairsAt (chainRedFrame k i ζ a).1 (chainRedFrame k i ζ a).2,
      p ∈ (RegChain.pair k r g i s).pairsAt ζ a := by
  intro p hp
  rw [chain_pairsAt_frames]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hp))

/-- A literal green side pair block is included in its chain's pair list. -/
theorem chain_green_pair_inclusion {w : ℕ} (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain)
    (ζ : ℤˣ) (a : Fin w × Path) :
    ∀ p ∈ g.pairsAt (chainGreenFrame k i ζ a).1 (chainGreenFrame k i ζ a).2,
      p ∈ (RegChain.pair k r g i s).pairsAt ζ a := by
  intro p hp
  rw [chain_pairsAt_frames]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hp))

/-- The source red side couple is actually completely paired in the ambient carrier. -/
theorem chain_red_subCoupleAt (Q : RegCpl) (G : Garden 2) (hG : Q.Decodes G)
    (a : Fin 2 × Path) (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain) (ζ : ℤˣ) (h : TTree)
    (ha : Comb.subtree (G.tree a.1) a.2 = some ((RegChain.pair k r g i s).plug ζ h))
    (hP : ∀ p ∈ (RegChain.pair k r g i s).pairsAt ζ a, p ∈ Q.raw.2) :
    SubCoupleAt G (chainRedFrame k i ζ a).1 (chainRedFrame k i ζ a).2 := by
  have he := chain_red_frame_extraction G.tree a k r g i s ζ h ha
  exact subCoupleAt_of_decoded_block Q r G hG _ _ he.1 he.2
    (fun p hp => hP p (chain_red_pair_inclusion k r g i s ζ a p hp))

/-- The source green side couple is actually completely paired in the ambient carrier. -/
theorem chain_green_subCoupleAt (Q : RegCpl) (G : Garden 2) (hG : Q.Decodes G)
    (a : Fin 2 × Path) (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain) (ζ : ℤˣ) (h : TTree)
    (ha : Comb.subtree (G.tree a.1) a.2 = some ((RegChain.pair k r g i s).plug ζ h))
    (hP : ∀ p ∈ (RegChain.pair k r g i s).pairsAt ζ a, p ∈ Q.raw.2) :
    SubCoupleAt G (chainGreenFrame k i ζ a).1 (chainGreenFrame k i ζ a).2 := by
  have he := chain_green_frame_extraction G.tree a k r g i s ζ h ha
  exact subCoupleAt_of_decoded_block Q g G hG _ _ he.1 he.2
    (fun p hp => hP p (chain_green_pair_inclusion k r g i s ζ a p hp))

/-- Erasing the sign orientation only exchanges an actual sub-couple's two roots. -/
theorem subCoupleAt_physical {w : ℕ} (G : Garden w) (ε : ℤˣ) (front back : Fin w × Path)
    (h : SubCoupleAt G (orientedFrame ε front back).1 (orientedFrame ε front back).2) :
    SubCoupleAt G front back := by
  by_cases he : ε = 1
  · simpa only [orientedFrame,he,ite_true] using h
  · have hh : SubCoupleAt G back front := by simpa only [orientedFrame,he,ite_false] using h
    exact hh.symm

/-- The front red off-spine child never has property L. -/
theorem chain_red_front_not_external (Q : RegCpl) (G : Garden 2) (hG : Q.Decodes G)
    (a : Fin 2 × Path) (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain) (ζ : ℤˣ) (h : TTree)
    (ha : Comb.subtree (G.tree a.1) a.2 = some ((RegChain.pair k r g i s).plug ζ h))
    (hP : ∀ p ∈ (RegChain.pair k r g i s).pairsAt ζ a, p ∈ Q.raw.2) :
    ¬ ExternalAt G (addrExt a [k.red.1]) :=
  (subCoupleAt_physical G _ _ _ (chain_red_subCoupleAt Q G hG a k r g i s ζ h ha hP)).not_external rfl

/-- The front green off-spine child never has property L. -/
theorem chain_green_front_not_external (Q : RegCpl) (G : Garden 2) (hG : Q.Decodes G)
    (a : Fin 2 × Path) (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain) (ζ : ℤˣ) (h : TTree)
    (ha : Comb.subtree (G.tree a.1) a.2 = some ((RegChain.pair k r g i s).plug ζ h))
    (hP : ∀ p ∈ (RegChain.pair k r g i s).pairsAt ζ a, p ∈ Q.raw.2) :
    ¬ ExternalAt G (addrExt a [k.green.1]) :=
  (subCoupleAt_physical G _ _ _ (chain_green_subCoupleAt Q G hG a k r g i s ζ h ha hP)).not_external rfl

/-- The two front side slots and the continuation slot exhaust the three children. -/
theorem miniTree_front_slots_cover (k : MiniTreeCode) (j : Fin 3) (hj : j ≠ k.c) :
    j = k.red.1 ∨ j = k.green.1 := by
  obtain ⟨c,b⟩ := k
  fin_cases c <;> fin_cases b <;> fin_cases j <;>
    simp_all [MiniTreeCode.red,MiniTreeCode.green]

/-- Every off-spine front child fails property L, with the actual pairing retained. -/
theorem chain_offspine_not_external (Q : RegCpl) (G : Garden 2) (hG : Q.Decodes G)
    (a : Fin 2 × Path) (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain) (ζ : ℤˣ) (h : TTree)
    (ha : Comb.subtree (G.tree a.1) a.2 = some ((RegChain.pair k r g i s).plug ζ h))
    (hP : ∀ p ∈ (RegChain.pair k r g i s).pairsAt ζ a, p ∈ Q.raw.2)
    (j : Fin 3) (hj : j ≠ k.c) : ¬ ExternalAt G (addrExt a [j]) := by
  rcases miniTree_front_slots_cover k j hj with rfl | rfl
  · exact chain_red_front_not_external Q G hG a k r g i s ζ h ha hP
  · exact chain_green_front_not_external Q G hG a k r g i s ζ h ha hP

/-- The unique child with property L is exactly the continuation child. -/
theorem chain_child_external_iff (Q : RegCpl) (G : Garden 2) (hG : Q.Decodes G)
    (a : Fin 2 × Path) (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain) (ζ : ℤˣ) (h : TTree)
    (ha : Comb.subtree (G.tree a.1) a.2 = some ((RegChain.pair k r g i s).plug ζ h))
    (hP : ∀ p ∈ (RegChain.pair k r g i s).pairsAt ζ a, p ∈ Q.raw.2)
    (hL : ExternalAt G (addrExt a (RegChain.pair k r g i s).lonePath)) (j : Fin 3) :
    ExternalAt G (addrExt a [j]) ↔ j = k.c := by
  constructor
  · intro he
    by_contra hj
    exact chain_offspine_not_external Q G hG a k r g i s ζ h ha hP j hj he
  · rintro rfl
    apply hL.ancestor
    rw [below_same_root,RegChain.lonePath]
    exact List.prefix_append _ _

end WaveTurbulence.Reg
