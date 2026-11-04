/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.ChainContinuationExtraction

/-! # The unique property-L child of a chain pair's lower node -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- The lower side slots and lower continuation exhaust its three children. -/
theorem miniTree_back_slots_cover (k : MiniTreeCode) (j : Fin 3) (hj : j ≠ k.lone) :
    j = k.red.2 ∨ j = k.green.2 := by
  obtain ⟨c,b⟩ := k
  fin_cases c <;> fin_cases b <;> fin_cases j <;>
    simp_all [MiniTreeCode.lone,MiniTreeCode.red,MiniTreeCode.green]

/-- A red back-side child is closed inside its original tree and fails property L. -/
theorem chain_red_back_not_external (Q : RegCpl) (G : Garden 2) (hG : Q.Decodes G)
    (a : Fin 2 × Path) (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain) (ζ : ℤˣ) (h : TTree)
    (ha : Comb.subtree (G.tree a.1) a.2 = some ((RegChain.pair k r g i s).plug ζ h))
    (hP : ∀ p ∈ (RegChain.pair k r g i s).pairsAt ζ a, p ∈ Q.raw.2) :
    ¬ ExternalAt G (backRoot a k i k.red.2) :=
  (subCoupleAt_physical G _ _ _ (chain_red_subCoupleAt Q G hG a k r g i s ζ h ha hP)).symm.not_external rfl

/-- A green back-side child likewise fails property L. -/
theorem chain_green_back_not_external (Q : RegCpl) (G : Garden 2) (hG : Q.Decodes G)
    (a : Fin 2 × Path) (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain) (ζ : ℤˣ) (h : TTree)
    (ha : Comb.subtree (G.tree a.1) a.2 = some ((RegChain.pair k r g i s).plug ζ h))
    (hP : ∀ p ∈ (RegChain.pair k r g i s).pairsAt ζ a, p ∈ Q.raw.2) :
    ¬ ExternalAt G (backRoot a k i k.green.2) :=
  (subCoupleAt_physical G _ _ _ (chain_green_subCoupleAt Q G hG a k r g i s ζ h ha hP)).symm.not_external rfl

/-- At the actual lower branching node the lone slot is the unique L-child. -/
theorem chain_lower_child_external_iff (Q : RegCpl) (G : Garden 2) (hG : Q.Decodes G)
    (a : Fin 2 × Path) (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain) (ζ : ℤˣ) (h : TTree)
    (ha : Comb.subtree (G.tree a.1) a.2 = some ((RegChain.pair k r g i s).plug ζ h))
    (hP : ∀ p ∈ (RegChain.pair k r g i s).pairsAt ζ a, p ∈ Q.raw.2)
    (hL : ExternalAt G (addrExt a (RegChain.pair k r g i s).lonePath)) (j : Fin 3) :
    ExternalAt G (addrExt (secondRoot a k i) [j]) ↔ j = k.lone := by
  rw [← backRoot_eq]
  constructor
  · intro he
    by_contra hj
    rcases miniTree_back_slots_cover k j hj with rfl | rfl
    · exact chain_red_back_not_external Q G hG a k r g i s ζ h ha hP he
    · exact chain_green_back_not_external Q G hG a k r g i s ζ h ha hP he
  · rintro rfl
    apply hL.ancestor
    rw [chain_hole_as_rest]
    exact below_extend _ _

/-- Every actual inner-chain pair lies in the original chain's list. -/
theorem chain_inner_pair_inclusion {w : ℕ} (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain)
    (ζ : ℤˣ) (a : Fin w × Path) :
    ∀ p ∈ i.pairsAt (slotSign ζ k.c) (addrExt a [k.c]),
      p ∈ (RegChain.pair k r g i s).pairsAt ζ a := by
  intro p hp
  rw [chain_pairsAt_blocks]
  exact List.mem_append_left _ (List.mem_append_right _ hp)

/-- Every actual rest-chain pair lies in the original chain's list. -/
theorem chain_rest_pair_inclusion {w : ℕ} (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain)
    (ζ : ℤˣ) (a : Fin w × Path) :
    ∀ p ∈ s.pairsAt (slotSign (slotSign ζ k.c) k.lone) (backRoot a k i k.lone),
      p ∈ (RegChain.pair k r g i s).pairsAt ζ a := by
  intro p hp
  rw [chain_pairsAt_blocks]
  exact List.mem_append_right _ hp

end WaveTurbulence.Reg
