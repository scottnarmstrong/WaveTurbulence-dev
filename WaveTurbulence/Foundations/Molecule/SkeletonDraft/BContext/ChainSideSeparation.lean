/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.RegStructWork
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Raw
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.BContext.FrameStability
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.BContext.RelocationGeometry
public import WaveTurbulence.Foundations.RegStruct.ChainFrames


/-! # Separation of a chain's side couples from its continuation -/

public section
namespace WaveTurbulence.Reg.Skeleton.BContext
open TTree
variable {w : ℕ}

/-- A physical side frame stays disjoint from the lower continuation. -/
theorem chain_side_rest_incomp {w : ℕ} (k : MiniTreeCode) (i : RegChain)
    (a : Fin w × Path) (j l : Fin 3) (hj : j ≠ k.c) (hl : l ≠ k.lone) :
    IncompAddr (addrExt a [j]) (backRoot a k i k.lone) ∧
      IncompAddr (backRoot a k i l) (backRoot a k i k.lone) := by
  constructor
  · exact incomp_distinct_children a j k.c [] (i.lonePath ++ [k.lone]) hj
  · rw [backRoot_eq,backRoot_eq]
    exact incomp_distinct_children _ l k.lone [] [] hl

/-- A node in either side root is incomparable with the whole lower continuation. -/
theorem chain_side_node_rest {w : ℕ} (k : MiniTreeCode) (i : RegChain)
    (a target : Fin w × Path) (j l : Fin 3) (hj : j ≠ k.c) (hl : l ≠ k.lone)
    (ht : Below (addrExt a [j]) target ∨ Below (backRoot a k i l) target) :
    IncompAddr target (backRoot a k i k.lone) := by
  have h := chain_side_rest_incomp k i a j l hj hl
  rcases ht with ht | ht
  · exact h.1.descendants ht ⟨rfl,List.prefix_refl _⟩
  · exact h.2.descendants ht ⟨rfl,List.prefix_refl _⟩

/-- A node in a side frame cannot belong to the inner spine. -/
theorem chain_side_node_not_inner {w : ℕ} (k : MiniTreeCode) (i : RegChain)
    (ζ : ℤˣ) (a target : Fin w × Path) (j l : Fin 3) (hj : j ≠ k.c)
    (ht : Below (addrExt a [j]) target ∨ Below (backRoot a k i l) target) :
    target ∉ chainNodes i (slotSign ζ k.c) (addrExt a [k.c]) := by
  rcases ht with ht | ht
  · exact not_mem_chainNodes_of_below i _ ht
      (incomp_distinct_children a j k.c [] [] hj)
  · intro h
    apply chainNodes_not_below_lone i (slotSign ζ k.c) (addrExt a [k.c]) target h
    apply below_trans _ ht
    rw [← secondRoot_as_hole,backRoot_eq]
    exact below_extend _ _

/-- Existing inner-spine pairs stay fixed under insertion in a side frame. -/
theorem chain_side_inner_pairs_fixed (k : MiniTreeCode) (i : RegChain)
    (ζ : ℤˣ) (a target : Fin w × Path) (m : MiniTreeCode) (j l : Fin 3) (hj : j ≠ k.c)
    (ht : Below (addrExt a [j]) target ∨ Below (backRoot a k i l) target) :
    (i.pairsAt (slotSign ζ k.c) (addrExt a [k.c])).map (fun p =>
      (WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone p.1,WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone p.2)) =
      i.pairsAt (slotSign ζ k.c) (addrExt a [k.c]) := by
  rcases ht with ht | ht
  · exact relocate_chain_pairs_fixed i _ _ _ m
      ((incomp_distinct_children a j k.c [] [] hj).descendants ht ⟨rfl,List.prefix_refl _⟩)
  · apply relocate_pairs_below_chain_hole
    apply below_trans _ ht
    rw [← secondRoot_as_hole,backRoot_eq]
    exact below_extend _ _

/-- A represented red-side node is separated from every other chain block. -/
theorem chain_red_node_separation (k : MiniTreeCode) (r : RegCpl) (i : RegChain)
    (ζ : ℤˣ) (a target : Fin w × Path)
    (ht : target ∈ coupleNodes r (chainRedFrame k i ζ a).1 (chainRedFrame k i ζ a).2) :
    (IncompAddr target (chainGreenFrame k i ζ a).1 ∧
      IncompAddr target (chainGreenFrame k i ζ a).2) ∧
      IncompAddr target (backRoot a k i k.lone) ∧
      target ∉ chainNodes i (slotSign ζ k.c) (addrExt a [k.c]) := by
  have hp := orientedFrame_node_below r _ _ _ target ht
  exact ⟨(chain_red_green_apart k i ζ a).of_node r target ht,
    chain_side_node_rest k i a target _ _ (miniTree_slots_separate k).1
      (miniTree_slots_separate k).2.2.2.1 hp,
    chain_side_node_not_inner k i ζ a target _ _ (miniTree_slots_separate k).1 hp⟩

/-- A represented green-side node is separated from every other chain block. -/
theorem chain_green_node_separation (k : MiniTreeCode) (g : RegCpl) (i : RegChain)
    (ζ : ℤˣ) (a target : Fin w × Path)
    (ht : target ∈ coupleNodes g (chainGreenFrame k i ζ a).1 (chainGreenFrame k i ζ a).2) :
    (IncompAddr target (chainRedFrame k i ζ a).1 ∧
      IncompAddr target (chainRedFrame k i ζ a).2) ∧
      IncompAddr target (backRoot a k i k.lone) ∧
      target ∉ chainNodes i (slotSign ζ k.c) (addrExt a [k.c]) := by
  have hp := orientedFrame_node_below g _ _ _ target ht
  exact ⟨(chain_red_green_apart k i ζ a).symm.of_node g target ht,
    chain_side_node_rest k i a target _ _ (miniTree_slots_separate k).2.1
      (miniTree_slots_separate k).2.2.2.2.1 hp,
    chain_side_node_not_inner k i ζ a target _ _ (miniTree_slots_separate k).2.1 hp⟩

end WaveTurbulence.Reg.Skeleton.BContext
