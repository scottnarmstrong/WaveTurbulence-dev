/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.PinnedRelocation
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.BContext.InsertionCovariance

/-! # Literal hole transport for insertion within a context or at its terminal node -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

/-- Inserting at a represented context node moves the old hole by literal relocation. -/
theorem insertedChain_hole_of_mem {w : ℕ} (X : RegChain) (σ : Fin w → ℤˣ)
    (ζ : ℤˣ) (a target : Address w) (m : MiniTreeCode)
    (ha : nodeSign σ a = ζ) (ht : target ∈ chainNodes X ζ a) :
    addrExt (pinnedRelocate target m a)
      (normalizeChain (if target = addrExt a X.lonePath then
        appendChain X (miniChain m) else insertMiniChain X ζ a target m)).lonePath =
      relocate target m.c m.lone (addrExt a X.lonePath) := by
  have hn : target ≠ addrExt a X.lonePath := by
    intro he
    apply chainNodes_not_below_lone X ζ a target ht
    rw [he]
    exact ⟨rfl,List.prefix_refl _⟩
  rw [ite_eq_right hn,pinnedRelocate_of_below target a m (chainNodes_below X ζ a target ht)]
  exact BContext.normalizedChain_hole X σ ζ a target m ha ht

/-- Appending at the original core node moves that core to the mini-chain's lone slot. -/
theorem insertedChain_hole_at_core {w : ℕ} (X : RegChain)
    (ζ : ℤˣ) (a : Address w) (m : MiniTreeCode) :
    addrExt (pinnedRelocate (addrExt a X.lonePath) m a)
      (normalizeChain (appendChain X (miniChain m))).lonePath =
      relocate (addrExt a X.lonePath) m.c m.lone (addrExt a X.lonePath) := by
  rw [pinnedRelocate_of_below _ _ _ (below_extend a X.lonePath),normalizeChain_lonePath,
    appendChain_lonePath,miniChain_lonePath]
  rw [BContext.relocate_self]
  exact (addrExt_append a X.lonePath [m.c,m.lone]).symm

/-- Conditional local geometry: an insertion outside the represented context is
 either outside its root or in the subtree filling its terminal hole. -/
theorem insertedChain_hole_of_location {w : ℕ} (X : RegChain) (σ : Fin w → ℤˣ)
    (ζ : ℤˣ) (a target : Address w) (m : MiniTreeCode)
    (ha : nodeSign σ a = ζ)
    (hl : target ∈ chainNodes X ζ a ∨ ¬ Below a target ∨ Below (addrExt a X.lonePath) target) :
    addrExt (pinnedRelocate target m a)
      (normalizeChain (if target = addrExt a X.lonePath then
        appendChain X (miniChain m) else insertMiniChain X ζ a target m)).lonePath =
      relocate target m.c m.lone (addrExt a X.lonePath) := by
  by_cases ht : target = addrExt a X.lonePath
  · subst target
    rw [ite_eq_left rfl]
    exact insertedChain_hole_at_core X ζ a m
  by_cases hm : target ∈ chainNodes X ζ a
  · exact insertedChain_hole_of_mem X σ ζ a target m ha hm
  rw [ite_eq_right ht,insertMiniChain_outside X ζ a target m hm,normalizeChain_lonePath]
  rcases hl with hm' | hn | hb
  · exact (hm hm').elim
  · have he : a ≠ target := by
      intro he
      apply hn
      rw [he]
      exact ⟨rfl,List.prefix_refl _⟩
    rw [pinnedRelocate,ite_eq_right he]
    exact (BContext.relocate_respectsAt_of_not_below target a m.c m.lone hn X.lonePath).symm
  · rw [pinnedRelocate_of_below target a m (below_trans (below_extend a X.lonePath) hb)]
    symm
    apply BContext.relocate_eq_of_not_below
    intro hc
    have he : target = addrExt a X.lonePath := Prod.ext hc.1.symm
      (hc.2.eq_of_length (Nat.le_antisymm hc.2.length_le hb.2.length_le))
    exact ht he

end WaveTurbulence.Reg.Skeleton
