/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.ChainInnerTransport

/-! # Constructor congruence for B insertion in inner and rest chains -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- An inner-spine insertion changes only the inner chain code. -/
theorem insertMiniChain_inner (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain)
    (ζ : ℤˣ) (a target : Fin 2 × Path) (m : MiniTreeCode)
    (ha : target ≠ a) (hb : target ≠ secondRoot a k i)
    (ht : target ∈ chainNodes i (slotSign ζ k.c) (addrExt a [k.c])) :
    insertMiniChain (.pair k r g i s) ζ a target m =
      .pair k r g (insertMiniChain i (slotSign ζ k.c) (addrExt a [k.c]) target m) s := by
  have hr := chain_inner_side_not_mem k i r ζ (slotSign ζ k.red.1) a target k.red.1 k.red.2
    (miniTree_slots_separate k).1 ht
  have hg := chain_inner_side_not_mem k i g ζ (slotSign ζ k.green.1) a target k.green.1 k.green.2
    (miniTree_slots_separate k).2.1 ht
  have hs : target ∉ chainNodes s (slotSign (slotSign ζ k.c) k.lone) (backRoot a k i k.lone) := by
    intro hm
    exact chain_inner_not_in_back k i ζ a target k.lone ht (chainNodes_below s _ _ _ hm)
  rw [insertMiniChain_components k r g i s ζ a target m ha hb,
    insertMiniCouple_outside r _ _ target m hr,insertMiniCouple_outside g _ _ target m hg,
    insertMiniChain_outside s _ _ target m hs]

/-- A rest-chain insertion changes only the rest chain code. -/
theorem insertMiniChain_rest (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain)
    (ζ : ℤˣ) (a target : Fin 2 × Path) (m : MiniTreeCode)
    (ha : target ≠ a) (hb : target ≠ secondRoot a k i)
    (ht : target ∈ chainNodes s (slotSign (slotSign ζ k.c) k.lone) (backRoot a k i k.lone)) :
    insertMiniChain (.pair k r g i s) ζ a target m =
      .pair k r g i (insertMiniChain s (slotSign (slotSign ζ k.c) k.lone) (backRoot a k i k.lone) target m) := by
  have hr := incomp_orientedFrame (slotSign ζ k.red.1) target _ _
    (chain_rest_side_incomp k i s ζ a target _ _ (miniTree_slots_separate k).1
      (miniTree_slots_separate k).2.2.2.1 ht)
  have hg := incomp_orientedFrame (slotSign ζ k.green.1) target _ _
    (chain_rest_side_incomp k i s ζ a target _ _ (miniTree_slots_separate k).2.1
      (miniTree_slots_separate k).2.2.2.2.1 ht)
  have hi : target ∉ chainNodes i (slotSign ζ k.c) (addrExt a [k.c]) := by
    intro hm
    exact chainNodes_not_below_lone i _ _ _ hm (chain_rest_below_inner_hole k i s ζ a target ht)
  rw [insertMiniChain_components k r g i s ζ a target m ha hb,
    insertMiniCouple_of_incomparable r _ _ target m hr.1 hr.2,
    insertMiniCouple_of_incomparable g _ _ target m hg.1 hg.2,
    insertMiniChain_outside i _ _ target m hi]

/-- Pair-list congruence for arbitrary replacement data in the inner chain. -/
theorem chain_inner_constructor_perm (k : MiniTreeCode) (r g : RegCpl) (i i' s : RegChain)
    (ζ : ℤˣ) (a target : Fin 2 × Path) (m : MiniTreeCode)
    (N : List ((Fin 2 × Path) × (Fin 2 × Path)))
    (ht : target ∈ chainNodes i (slotSign ζ k.c) (addrExt a [k.c]))
    (hh : addrExt (addrExt a [k.c]) i'.lonePath =
      RawCpl.relocate target m.c m.lone (addrExt (addrExt a [k.c]) i.lonePath))
    (hlocal : (i'.pairsAt (slotSign ζ k.c) (addrExt a [k.c])).Perm
      ((i.pairsAt (slotSign ζ k.c) (addrExt a [k.c])).map (fun p =>
        (RawCpl.relocate target m.c m.lone p.1,RawCpl.relocate target m.c m.lone p.2)) ++ N)) :
    ((RegChain.pair k r g i' s).pairsAt ζ a).Perm
      (((RegChain.pair k r g i s).pairsAt ζ a).map (fun p =>
        (RawCpl.relocate target m.c m.lone p.1,RawCpl.relocate target m.c m.lone p.2)) ++ N) := by
  rw [chain_pairsAt_blocks,inner_sidePairs_transport k i i' r ζ _ a target m _ _
      (miniTree_slots_separate k).1 ht hh,
    inner_sidePairs_transport k i i' g ζ _ a target m _ _ (miniTree_slots_separate k).2.1 ht hh,
    inner_rest_pairs_transport k i i' s ζ a target m ht hh,chain_pairsAt_blocks]
  simp only [List.map_append]
  exact perm_lift_middle _ _ _ _ N hlocal

/-- Pair-list congruence for arbitrary replacement data in the rest chain. -/
theorem chain_rest_constructor_perm (k : MiniTreeCode) (r g : RegCpl) (i s s' : RegChain)
    (ζ : ℤˣ) (a target : Fin 2 × Path) (m : MiniTreeCode)
    (N : List ((Fin 2 × Path) × (Fin 2 × Path)))
    (ht : target ∈ chainNodes s (slotSign (slotSign ζ k.c) k.lone) (backRoot a k i k.lone))
    (hlocal : (s'.pairsAt (slotSign (slotSign ζ k.c) k.lone) (backRoot a k i k.lone)).Perm
      ((s.pairsAt (slotSign (slotSign ζ k.c) k.lone) (backRoot a k i k.lone)).map (fun p =>
        (RawCpl.relocate target m.c m.lone p.1,RawCpl.relocate target m.c m.lone p.2)) ++ N)) :
    ((RegChain.pair k r g i s').pairsAt ζ a).Perm
      (((RegChain.pair k r g i s).pairsAt ζ a).map (fun p =>
        (RawCpl.relocate target m.c m.lone p.1,RawCpl.relocate target m.c m.lone p.2)) ++ N) := by
  have hr := incomp_orientedFrame (slotSign ζ k.red.1) target _ _
    (chain_rest_side_incomp k i s ζ a target _ _ (miniTree_slots_separate k).1
      (miniTree_slots_separate k).2.2.2.1 ht)
  have hg := incomp_orientedFrame (slotSign ζ k.green.1) target _ _
    (chain_rest_side_incomp k i s ζ a target _ _ (miniTree_slots_separate k).2.1
      (miniTree_slots_separate k).2.2.2.2.1 ht)
  have hpr := relocate_couple_pairs_fixed r _ _ target m hr.1 hr.2
  have hpg := relocate_couple_pairs_fixed g _ _ target m hg.1 hg.2
  have hpi := relocate_pairs_below_chain_hole i (slotSign ζ k.c) _ target m.c m.lone
    (chain_rest_below_inner_hole k i s ζ a target ht)
  simp only [chain_pairsAt_frames,List.map_append]
  rw [hpr,hpg,hpi]
  exact perm_lift_last _ _ _ _ N hlocal

/-- Rest-chain hole transport is exactly the whole chain's hole transport. -/
theorem rest_chain_hole_transport {w : ℕ} (k : MiniTreeCode) (r g : RegCpl) (i s s' : RegChain)
    (a : Fin w × Path) (f : (Fin w × Path) → (Fin w × Path))
    (hh : addrExt (backRoot a k i k.lone) s'.lonePath = f (addrExt (backRoot a k i k.lone) s.lonePath)) :
    addrExt a (RegChain.pair k r g i s').lonePath = f (addrExt a (RegChain.pair k r g i s).lonePath) := by
  simpa only [backRoot,RegChain.lonePath,addrExt_append,List.append_assoc] using hh

end WaveTurbulence.Reg
