/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.RegStructWork
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Raw
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.BContext.RelocationGeometry
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.BContext.ChainContinuationSeparation


/-! # Transport of side frames when the inner chain changes its terminal address -/

public section
namespace WaveTurbulence.Reg.Skeleton.BContext
open TTree
variable {w : ℕ}

/-- Moving the inner hole moves each lower child by the same source relocation. -/
theorem inner_backRoot_transport (k : MiniTreeCode) (i i' : RegChain)
    (ζ : ℤˣ) (a target : Fin w × Path) (m : MiniTreeCode) (j : Fin 3)
    (ht : target ∈ chainNodes i (slotSign ζ k.c) (addrExt a [k.c]))
    (hh : addrExt (addrExt a [k.c]) i'.lonePath =
      WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone (addrExt (addrExt a [k.c]) i.lonePath)) :
    backRoot a k i' j = WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone (backRoot a k i j) := by
  have hl := relocate_respectsAt_of_not_below target (secondRoot a k i) m.c m.lone
    (chain_inner_not_below_second k i ζ a target ht)
  rw [backRoot_eq,backRoot_eq,hl _,secondRoot_as_hole,secondRoot_as_hole,← hh]

/-- An unchanged side couple follows the moved back root of the inner chain. -/
theorem inner_sidePairs_transport (k : MiniTreeCode) (i i' : RegChain) (Q : RegCpl)
    (ζ ε : ℤˣ) (a target : Fin w × Path) (m : MiniTreeCode) (j l : Fin 3) (hj : j ≠ k.c)
    (ht : target ∈ chainNodes i (slotSign ζ k.c) (addrExt a [k.c]))
    (hh : addrExt (addrExt a [k.c]) i'.lonePath =
      WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone (addrExt (addrExt a [k.c]) i.lonePath)) :
    sidePairs Q ε (addrExt a [j]) (backRoot a k i' l) =
      (sidePairs Q ε (addrExt a [j]) (backRoot a k i l)).map (fun p =>
        (WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone p.1,WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone p.2)) := by
  have hf := chain_inner_front_incomp k i ζ a target j hj ht
  have hlf := relocate_respects_incomparable target (addrExt a [j]) m.c m.lone hf.1 hf.2
  have hlb := relocate_respectsAt_of_not_below target (backRoot a k i l) m.c m.lone
    (chain_inner_not_in_back k i ζ a target l ht)
  have he := inner_backRoot_transport k i i' ζ a target m l ht hh
  by_cases hε : ε = 1
  · simp only [sidePairs,hε,ite_true]
    have hm := couple_pairsAt_map_local Q (WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone)
      (addrExt a [j]) (backRoot a k i l) hlf hlb
    rw [relocate_eq_of_not_below _ _ _ _ hf.1,← he] at hm
    exact hm
  · simp only [sidePairs,hε,ite_false]
    have hm := couple_pairsAt_map_local Q (WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone)
      (backRoot a k i l) (addrExt a [j]) hlb hlf
    rw [relocate_eq_of_not_below _ _ _ _ hf.1,← he] at hm
    exact hm

/-- The whole rest chain follows the moved lower continuation root. -/
theorem inner_rest_pairs_transport (k : MiniTreeCode) (i i' s : RegChain)
    (ζ : ℤˣ) (a target : Fin w × Path) (m : MiniTreeCode)
    (ht : target ∈ chainNodes i (slotSign ζ k.c) (addrExt a [k.c]))
    (hh : addrExt (addrExt a [k.c]) i'.lonePath =
      WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone (addrExt (addrExt a [k.c]) i.lonePath)) :
    s.pairsAt (slotSign (slotSign ζ k.c) k.lone) (backRoot a k i' k.lone) =
      (s.pairsAt (slotSign (slotSign ζ k.c) k.lone) (backRoot a k i k.lone)).map (fun p =>
        (WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone p.1,WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone p.2)) := by
  have hl := relocate_respectsAt_of_not_below target (backRoot a k i k.lone) m.c m.lone
    (chain_inner_not_in_back k i ζ a target k.lone ht)
  rw [inner_backRoot_transport k i i' ζ a target m k.lone ht hh]
  exact chain_pairsAt_map_local s _ _ hl _

/-- Hole transport of an inner-chain replacement implies hole transport of its context. -/
theorem inner_chain_hole_transport (k : MiniTreeCode) (r g : RegCpl) (i i' s : RegChain)
    (ζ : ℤˣ) (a target : Fin w × Path) (m : MiniTreeCode)
    (ht : target ∈ chainNodes i (slotSign ζ k.c) (addrExt a [k.c]))
    (hh : addrExt (addrExt a [k.c]) i'.lonePath =
      WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone (addrExt (addrExt a [k.c]) i.lonePath)) :
    addrExt a (RegChain.pair k r g i' s).lonePath =
      WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone (addrExt a (RegChain.pair k r g i s).lonePath) := by
  have he := inner_backRoot_transport k i i' ζ a target m k.lone ht hh
  have hl := relocate_respectsAt_of_not_below target (backRoot a k i k.lone) m.c m.lone
    (chain_inner_not_in_back k i ζ a target k.lone ht)
  change addrExt a (([k.c] ++ i'.lonePath ++ [k.lone]) ++ s.lonePath) = _
  rw [← addrExt_append]
  change addrExt (backRoot a k i' k.lone) s.lonePath =
    WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone (addrExt a (([k.c] ++ i.lonePath ++ [k.lone]) ++ s.lonePath))
  rw [← addrExt_append,hl _,he]

end WaveTurbulence.Reg.Skeleton.BContext
