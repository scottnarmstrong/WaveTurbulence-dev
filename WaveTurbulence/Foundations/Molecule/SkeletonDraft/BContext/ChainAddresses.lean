/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.BContext.ChainInsertionRoot

/-! # Literal address frames for insertion at a chain pair's lower node -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton.BContext
open TTree
variable {w : ℕ}

/-- The four source pair blocks of a chain pair. -/
theorem chain_pairsAt_blocks {w : ℕ} (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain)
    (ζ : ℤˣ) (a : Fin w × Path) :
    (RegChain.pair k r g i s).pairsAt ζ a =
      sidePairs r (slotSign ζ k.red.1) (addrExt a [k.red.1]) (backRoot a k i k.red.2) ++
      sidePairs g (slotSign ζ k.green.1) (addrExt a [k.green.1]) (backRoot a k i k.green.2) ++
      i.pairsAt (slotSign ζ k.c) (addrExt a [k.c]) ++
      s.pairsAt (slotSign (slotSign ζ k.c) k.lone) (backRoot a k i k.lone) := rfl

theorem backRoot_eq {w : ℕ} (a : Fin w × Path) (k : MiniTreeCode) (i : RegChain) (j : Fin 3) :
    backRoot a k i j = addrExt (secondRoot a k i) [j] := (addrExt_append _ _ _).symm

theorem secondRoot_as_hole {w : ℕ} (a : Fin w × Path) (k : MiniTreeCode) (i : RegChain) :
    secondRoot a k i = addrExt (addrExt a [k.c]) i.lonePath := (addrExt_append _ _ _).symm

/-- The second root is always a proper descendant of the first. -/
theorem secondRoot_ne {w : ℕ} (a : Fin w × Path) (k : MiniTreeCode) (i : RegChain) :
    secondRoot a k i ≠ a :=
  below_child_ne_root a _ k.c i.lonePath ⟨rfl,List.prefix_refl _⟩

/-- Appending a mini-tree to the inner chain moves the old lower node into its lone slot. -/
theorem secondRoot_append {w : ℕ} (a : Fin w × Path) (k m : MiniTreeCode) (i : RegChain) :
    secondRoot a k (appendChain i (miniChain m)) = addrExt (secondRoot a k i) [m.c,m.lone] := by
  simp only [secondRoot,appendChain_lonePath,miniChain_lonePath,addrExt_append,List.append_assoc]

/-- Every old child of the lower node is translated by the same literal relocation. -/
theorem relocate_backRoot (a : Fin w × Path) (k m : MiniTreeCode) (i : RegChain) (j : Fin 3) :
    WaveTurbulence.Reg.Skeleton.relocate (secondRoot a k i) m.c m.lone (backRoot a k i j) =
      backRoot a k (appendChain i (miniChain m)) j := by
  have hlocal : RespectsAt (WaveTurbulence.Reg.Skeleton.relocate (secondRoot a k i) m.c m.lone) (secondRoot a k i) :=
    relocate_respects_desc _ _ _ _ ⟨rfl,List.prefix_refl _⟩
  rw [backRoot_eq,hlocal _,relocate_self,backRoot_eq,secondRoot_append]

/-- A noncontinuation front child is incomparable with the lower node. -/
theorem secondRoot_front_incomp {w : ℕ} (a : Fin w × Path) (k : MiniTreeCode) (i : RegChain)
    (j : Fin 3) (hj : j ≠ k.c) : IncompAddr (secondRoot a k i) (addrExt a [j]) :=
  incomp_distinct_children a k.c j i.lonePath [] hj.symm

/-- Relocation at the lower node fixes every front side root. -/
theorem relocate_frontRoot (a : Fin w × Path) (k m : MiniTreeCode) (i : RegChain)
    (j : Fin 3) (hj : j ≠ k.c) :
    WaveTurbulence.Reg.Skeleton.relocate (secondRoot a k i) m.c m.lone (addrExt a [j]) = addrExt a [j] :=
  relocate_eq_of_not_below _ _ _ _ (secondRoot_front_incomp a k i j hj).1

/-- The full front side subtree is unaffected by lower-node insertion. -/
theorem relocate_respects_front (a : Fin w × Path) (k m : MiniTreeCode) (i : RegChain)
    (j : Fin 3) (hj : j ≠ k.c) :
    RespectsAt (WaveTurbulence.Reg.Skeleton.relocate (secondRoot a k i) m.c m.lone) (addrExt a [j]) :=
  relocate_respects_incomparable _ _ _ _ (secondRoot_front_incomp a k i j hj).1
    (secondRoot_front_incomp a k i j hj).2

/-- Every back side subtree is moved as a whole. -/
theorem relocate_respects_back (a : Fin w × Path) (k m : MiniTreeCode) (i : RegChain) (j : Fin 3) :
    RespectsAt (WaveTurbulence.Reg.Skeleton.relocate (secondRoot a k i) m.c m.lone) (backRoot a k i j) := by
  apply relocate_respects_desc
  rw [backRoot_eq]
  exact below_extend _ _

end WaveTurbulence.Reg.Skeleton.BContext
