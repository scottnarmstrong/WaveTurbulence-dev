/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Raw
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.BContext.RelocationGeometry
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.BContext.ChainAddresses


/-! # Operation B at the lower branching node of a chain pair

The inner chain's existing pairs stay outside its terminal hole. Both back side
roots and the rest chain move together; the newly inserted mini-tree pairs are
tracked literally, with their correct lower-node sign.
-/

public section
namespace WaveTurbulence.Reg.Skeleton.BContext
open TTree
variable {w : ℕ}

/-- A side couple's front root stays fixed and its back root is relocated. -/
theorem lower_sidePairs_map (Q : RegCpl) (ε : ℤˣ) (a : Fin w × Path)
    (k m : MiniTreeCode) (i : RegChain) (front back : Fin 3) (hfront : front ≠ k.c) :
    sidePairs Q ε (addrExt a [front]) (backRoot a k (appendChain i (miniChain m)) back) =
      (sidePairs Q ε (addrExt a [front]) (backRoot a k i back)).map
        (fun p => (WaveTurbulence.Reg.Skeleton.relocate (secondRoot a k i) m.c m.lone p.1,
          WaveTurbulence.Reg.Skeleton.relocate (secondRoot a k i) m.c m.lone p.2)) := by
  by_cases he : ε = 1
  · simp only [sidePairs,he,ite_true]
    have hm := couple_pairsAt_map_local Q (WaveTurbulence.Reg.Skeleton.relocate (secondRoot a k i) m.c m.lone)
      (addrExt a [front]) (backRoot a k i back)
      (relocate_respects_front a k m i front hfront) (relocate_respects_back a k m i back)
    rw [relocate_frontRoot a k m i front hfront,relocate_backRoot] at hm
    exact hm
  · simp only [sidePairs,he,ite_false]
    have hm := couple_pairsAt_map_local Q (WaveTurbulence.Reg.Skeleton.relocate (secondRoot a k i) m.c m.lone)
      (backRoot a k i back) (addrExt a [front])
      (relocate_respects_back a k m i back) (relocate_respects_front a k m i front hfront)
    rw [relocate_frontRoot a k m i front hfront,relocate_backRoot] at hm
    exact hm

/-- The rest-chain pair block is transported as a complete rooted subtree. -/
theorem lower_rest_pairs_map (s : RegChain) (ζ : ℤˣ) (a : Fin w × Path)
    (k m : MiniTreeCode) (i : RegChain) :
    s.pairsAt ζ (backRoot a k (appendChain i (miniChain m)) k.lone) =
      (s.pairsAt ζ (backRoot a k i k.lone)).map
        (fun p => (WaveTurbulence.Reg.Skeleton.relocate (secondRoot a k i) m.c m.lone p.1,
          WaveTurbulence.Reg.Skeleton.relocate (secondRoot a k i) m.c m.lone p.2)) := by
  have hm := chain_pairsAt_map_local s (WaveTurbulence.Reg.Skeleton.relocate (secondRoot a k i) m.c m.lone)
    (backRoot a k i k.lone) (relocate_respects_back a k m i k.lone) ζ
  rw [relocate_backRoot] at hm
  exact hm

/-- Existing inner-chain pairs are outside the insertion root and remain fixed. -/
theorem lower_inner_pairs_fixed (i : RegChain) (ζ : ℤˣ) (a : Fin w × Path) (k m : MiniTreeCode) :
    (i.pairsAt ζ (addrExt a [k.c])).map
        (fun p => (WaveTurbulence.Reg.Skeleton.relocate (secondRoot a k i) m.c m.lone p.1,
          WaveTurbulence.Reg.Skeleton.relocate (secondRoot a k i) m.c m.lone p.2)) = i.pairsAt ζ (addrExt a [k.c]) := by
  apply relocate_pairs_below_chain_hole
  rw [← secondRoot_as_hole]
  exact ⟨rfl,List.prefix_refl _⟩

/-- Appending the new mini-tree to the inner chain places its pairs at the old lower root. -/
theorem lower_inner_pairs_append (i : RegChain) (ζ : ℤˣ) (a : Fin w × Path) (k m : MiniTreeCode) :
    (appendChain i (miniChain m)).pairsAt ζ (addrExt a [k.c]) =
      i.pairsAt ζ (addrExt a [k.c]) ++ (miniChain m).pairsAt ζ (secondRoot a k i) := by
  rw [appendChain_pairsAt,← secondRoot_as_hole]

private theorem perm_move_inserted_block {α : Type*} (A B C D N : List α) :
    (A ++ B ++ (C ++ N) ++ D).Perm ((A ++ B ++ C ++ D) ++ N) := by
  simpa only [List.append_assoc] using
    ((List.perm_append_comm : (N ++ D).Perm (D ++ N)).append_left (A ++ B ++ C))

/-- Full pair-list fidelity of B at the lower node, including nested inner chains. -/
theorem insertMiniChain_lower_pairs (k m : MiniTreeCode) (r g : RegCpl) (i s : RegChain)
    (ζ : ℤˣ) (a : Fin w × Path) :
    ((insertMiniChain (.pair k r g i s) ζ a (secondRoot a k i) m).pairsAt ζ a).Perm
      (((RegChain.pair k r g i s).pairsAt ζ a).map
        (fun p => (WaveTurbulence.Reg.Skeleton.relocate (secondRoot a k i) m.c m.lone p.1,
          WaveTurbulence.Reg.Skeleton.relocate (secondRoot a k i) m.c m.lone p.2)) ++
        (miniChain m).pairsAt (slotSign ζ k.c) (secondRoot a k i)) := by
  rw [insertMiniChain,ite_eq_right (secondRoot_ne a k i),ite_eq_left rfl,chain_pairsAt_blocks]
  rw [lower_sidePairs_map r _ a k m i k.red.1 k.red.2 (miniTree_slots_separate k).1,
    lower_sidePairs_map g _ a k m i k.green.1 k.green.2 (miniTree_slots_separate k).2.1,
    lower_inner_pairs_append,lower_rest_pairs_map]
  rw [chain_pairsAt_blocks]
  simp only [List.map_append]
  rw [lower_inner_pairs_fixed]
  exact perm_move_inserted_block _ _ _ _ _

/-- The terminal hole moves with the old lower subtree. -/
theorem insertMiniChain_lower_lonePath (k m : MiniTreeCode) (r g : RegCpl) (i s : RegChain)
    (ζ : ℤˣ) (a : Fin w × Path) :
    addrExt a (insertMiniChain (.pair k r g i s) ζ a (secondRoot a k i) m).lonePath =
      WaveTurbulence.Reg.Skeleton.relocate (secondRoot a k i) m.c m.lone
        (addrExt a (RegChain.pair k r g i s).lonePath) := by
  rw [insertMiniChain,ite_eq_right (secondRoot_ne a k i),ite_eq_left rfl]
  simp only [RegChain.lonePath,appendChain_lonePath,miniChain_lonePath]
  have hold : addrExt a ([k.c] ++ i.lonePath ++ [k.lone] ++ s.lonePath) =
      addrExt (secondRoot a k i) ([k.lone] ++ s.lonePath) := by
    simp only [secondRoot,addrExt_append,List.append_assoc]
  rw [hold]
  have hlocal : RespectsAt (WaveTurbulence.Reg.Skeleton.relocate (secondRoot a k i) m.c m.lone) (secondRoot a k i) :=
    relocate_respects_desc _ _ _ _ ⟨rfl,List.prefix_refl _⟩
  rw [hlocal _,relocate_self]
  simp only [secondRoot,addrExt_append,List.append_assoc]

/-- The source's actual lower-node sign is the sign passed to the new mini-chain. -/
theorem nodeSign_secondRoot (σ : Fin w → ℤˣ) (a : Fin w × Path) (k : MiniTreeCode) (i : RegChain) :
    nodeSign σ (secondRoot a k i) = slotSign (nodeSign σ a) k.c := by
  rw [secondRoot_as_hole,nodeSign_spine,nodeSign_step]

end WaveTurbulence.Reg.Skeleton.BContext
