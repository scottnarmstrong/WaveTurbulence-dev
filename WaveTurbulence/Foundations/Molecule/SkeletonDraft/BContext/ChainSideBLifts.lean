/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Raw
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.BContext.RelocationGeometry
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.BContext.ChainSideSeparation
public import WaveTurbulence.Foundations.RegStruct.PermutationBlocks


/-! # B insertion in a chain's side couple: constructor congruence

Local pair-list permutations below are arbitrary replacement congruences. Their
use in the source closure proof requires the actual recursively proved B step.
-/

public section
namespace WaveTurbulence.Reg.Skeleton.BContext
open TTree
variable {w : ℕ}

/-- Express the four pair blocks using their oriented frames. -/
theorem chain_pairsAt_frames {w : ℕ} (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain)
    (ζ : ℤˣ) (a : Fin w × Path) :
    (RegChain.pair k r g i s).pairsAt ζ a =
      r.pairsAt (chainRedFrame k i ζ a).1 (chainRedFrame k i ζ a).2 ++
      g.pairsAt (chainGreenFrame k i ζ a).1 (chainGreenFrame k i ζ a).2 ++
      i.pairsAt (slotSign ζ k.c) (addrExt a [k.c]) ++
      s.pairsAt (slotSign (slotSign ζ k.c) k.lone) (backRoot a k i k.lone) := by
  rw [chain_pairsAt_blocks,sidePairs_eq_frame,sidePairs_eq_frame]

/-- Away from its two outer nodes, chain insertion recurses in its four blocks. -/
theorem insertMiniChain_components {w : ℕ} (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain)
    (ζ : ℤˣ) (a target : Fin w × Path) (m : MiniTreeCode)
    (ha : target ≠ a) (hb : target ≠ secondRoot a k i) :
    insertMiniChain (.pair k r g i s) ζ a target m = .pair k
      (insertMiniCouple r (chainRedFrame k i ζ a).1 (chainRedFrame k i ζ a).2 target m)
      (insertMiniCouple g (chainGreenFrame k i ζ a).1 (chainGreenFrame k i ζ a).2 target m)
      (insertMiniChain i (slotSign ζ k.c) (addrExt a [k.c]) target m)
      (insertMiniChain s (slotSign (slotSign ζ k.c) k.lone) (backRoot a k i k.lone) target m) := by
  rw [insertMiniChain,ite_eq_right ha,ite_eq_right hb]
  rw [insertMiniCouple_orientedFrame,insertMiniCouple_orientedFrame]

/-- A red-side insertion changes only the red code. -/
theorem insertMiniChain_red (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain)
    (ζ : ℤˣ) (a target : Fin w × Path) (m : MiniTreeCode)
    (ha : target ≠ a) (hb : target ≠ secondRoot a k i)
    (ht : target ∈ coupleNodes r (chainRedFrame k i ζ a).1 (chainRedFrame k i ζ a).2) :
    insertMiniChain (.pair k r g i s) ζ a target m =
      .pair k (insertMiniCouple r (chainRedFrame k i ζ a).1 (chainRedFrame k i ζ a).2 target m) g i s := by
  have hsep := chain_red_node_separation k r i ζ a target ht
  rw [insertMiniChain_components k r g i s ζ a target m ha hb,
    insertMiniCouple_of_incomparable g _ _ target m hsep.1.1 hsep.1.2,
    insertMiniChain_outside i _ _ target m hsep.2.2,
    insertMiniChain_of_incomparable s _ _ target m hsep.2.1]

/-- A green-side insertion changes only the green code. -/
theorem insertMiniChain_green (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain)
    (ζ : ℤˣ) (a target : Fin w × Path) (m : MiniTreeCode)
    (ha : target ≠ a) (hb : target ≠ secondRoot a k i)
    (ht : target ∈ coupleNodes g (chainGreenFrame k i ζ a).1 (chainGreenFrame k i ζ a).2) :
    insertMiniChain (.pair k r g i s) ζ a target m =
      .pair k r (insertMiniCouple g (chainGreenFrame k i ζ a).1 (chainGreenFrame k i ζ a).2 target m) i s := by
  have hsep := chain_green_node_separation k g i ζ a target ht
  rw [insertMiniChain_components k r g i s ζ a target m ha hb,
    insertMiniCouple_of_incomparable r _ _ target m hsep.1.1 hsep.1.2,
    insertMiniChain_outside i _ _ target m hsep.2.2,
    insertMiniChain_of_incomparable s _ _ target m hsep.2.1]

/-- Lift an arbitrary red replacement permutation through the other three blocks. -/
theorem chain_red_constructor_perm (k : MiniTreeCode) (r r' g : RegCpl) (i s : RegChain)
    (ζ : ℤˣ) (a target : Fin w × Path) (m : MiniTreeCode)
    (N : List ((Fin w × Path) × (Fin w × Path)))
    (ht : target ∈ coupleNodes r (chainRedFrame k i ζ a).1 (chainRedFrame k i ζ a).2)
    (hlocal : (r'.pairsAt (chainRedFrame k i ζ a).1 (chainRedFrame k i ζ a).2).Perm
      ((r.pairsAt (chainRedFrame k i ζ a).1 (chainRedFrame k i ζ a).2).map (fun p =>
        (WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone p.1,WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone p.2)) ++ N)) :
    ((RegChain.pair k r' g i s).pairsAt ζ a).Perm
      (((RegChain.pair k r g i s).pairsAt ζ a).map (fun p =>
        (WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone p.1,WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone p.2)) ++ N) := by
  have hsep := chain_red_node_separation k r i ζ a target ht
  have hg := relocate_couple_pairs_fixed g _ _ target m hsep.1.1 hsep.1.2
  have hi := chain_side_inner_pairs_fixed k i ζ a target m _ _ (miniTree_slots_separate k).1
    (orientedFrame_node_below r _ _ _ target ht)
  have hs := relocate_chain_pairs_fixed s (slotSign (slotSign ζ k.c) k.lone) _ target m hsep.2.1
  simp only [chain_pairsAt_frames,List.map_append]
  rw [hg,hi,hs]
  simpa only [List.append_assoc] using
    perm_lift_first _ _
      (g.pairsAt (chainGreenFrame k i ζ a).1 (chainGreenFrame k i ζ a).2)
      (i.pairsAt (slotSign ζ k.c) (addrExt a [k.c]) ++
        s.pairsAt (slotSign (slotSign ζ k.c) k.lone) (backRoot a k i k.lone)) N hlocal

/-- Lift an arbitrary green replacement permutation through the other three blocks. -/
theorem chain_green_constructor_perm (k : MiniTreeCode) (r g g' : RegCpl) (i s : RegChain)
    (ζ : ℤˣ) (a target : Fin w × Path) (m : MiniTreeCode)
    (N : List ((Fin w × Path) × (Fin w × Path)))
    (ht : target ∈ coupleNodes g (chainGreenFrame k i ζ a).1 (chainGreenFrame k i ζ a).2)
    (hlocal : (g'.pairsAt (chainGreenFrame k i ζ a).1 (chainGreenFrame k i ζ a).2).Perm
      ((g.pairsAt (chainGreenFrame k i ζ a).1 (chainGreenFrame k i ζ a).2).map (fun p =>
        (WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone p.1,WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone p.2)) ++ N)) :
    ((RegChain.pair k r g' i s).pairsAt ζ a).Perm
      (((RegChain.pair k r g i s).pairsAt ζ a).map (fun p =>
        (WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone p.1,WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone p.2)) ++ N) := by
  have hsep := chain_green_node_separation k g i ζ a target ht
  have hr := relocate_couple_pairs_fixed r _ _ target m hsep.1.1 hsep.1.2
  have hi := chain_side_inner_pairs_fixed k i ζ a target m _ _ (miniTree_slots_separate k).2.1
    (orientedFrame_node_below g _ _ _ target ht)
  have hs := relocate_chain_pairs_fixed s (slotSign (slotSign ζ k.c) k.lone) _ target m hsep.2.1
  simp only [chain_pairsAt_frames,List.map_append]
  rw [hr,hi,hs]
  simpa only [List.append_assoc] using
    perm_lift_middle
      (r.pairsAt (chainRedFrame k i ζ a).1 (chainRedFrame k i ζ a).2) _ _
      (i.pairsAt (slotSign ζ k.c) (addrExt a [k.c]) ++
        s.pairsAt (slotSign (slotSign ζ k.c) k.lone) (backRoot a k i k.lone)) N hlocal

/-- Changing a side couple leaves the global hole fixed by source relocation. -/
theorem chain_side_hole_fixed (k : MiniTreeCode) (i s : RegChain)
    (a target : Fin w × Path) (m : MiniTreeCode) (j l : Fin 3) (hj : j ≠ k.c) (hl : l ≠ k.lone)
    (ht : Below (addrExt a [j]) target ∨ Below (backRoot a k i l) target) :
    WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone
      (addrExt a ([k.c] ++ i.lonePath ++ [k.lone] ++ s.lonePath)) =
      addrExt a ([k.c] ++ i.lonePath ++ [k.lone] ++ s.lonePath) := by
  apply relocate_eq_of_not_below
  have h := chain_side_node_rest k i a target j l hj hl ht
  have hh : Below (backRoot a k i k.lone)
      (addrExt a ([k.c] ++ i.lonePath ++ [k.lone] ++ s.lonePath)) := by
    rw [← addrExt_append]
    exact below_extend _ _
  exact (h.descendants ⟨rfl,List.prefix_refl _⟩ hh).1

end WaveTurbulence.Reg.Skeleton.BContext
