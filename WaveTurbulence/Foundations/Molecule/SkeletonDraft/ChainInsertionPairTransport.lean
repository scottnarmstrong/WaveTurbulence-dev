/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.LocalInsertionHoles

/-! # Pair transport for a chain block with its moved upper attachment -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem normalizedChain_pairs_pinned {w : ℕ} (X : RegChain) (σ : Fin w → ℤˣ)
    (ζ : ℤˣ) (a target : Address w) (m : MiniTreeCode) (ha : nodeSign σ a = ζ)
    (hl : target ∈ chainNodes X ζ a ∨ ¬ Below a target ∨ Below (addrExt a X.lonePath) target) :
    ((normalizeChain (if target = addrExt a X.lonePath then appendChain X (miniChain m)
      else insertMiniChain X ζ a target m)).pairsAt ζ (pinnedRelocate target m a)).toFinset =
      (X.pairsAt ζ a).toFinset.image (fun p =>
        (relocate target m.c m.lone p.1,relocate target m.c m.lone p.2)) ∪
      if target ∈ chainNodes X ζ a ∨ target = addrExt a X.lonePath
        then miniPairs σ target m else ∅ := by
  classical
  by_cases ht : target = addrExt a X.lonePath
  · subst target
    rw [ite_eq_left rfl,ite_eq_left (Or.inr rfl),
      pinnedRelocate_of_below _ _ _ (below_extend a X.lonePath)]
    exact BContext.normalizedAppend_pairs X σ ζ a m ha
  by_cases hm : target ∈ chainNodes X ζ a
  · rw [ite_eq_right ht,ite_eq_left (Or.inl hm),
      pinnedRelocate_of_below _ _ _ (chainNodes_below X ζ a target hm)]
    exact BContext.normalizedChain_pairs X σ ζ a target m ha hm
  rw [ite_eq_right ht,ite_eq_right (not_or.mpr ⟨hm,ht⟩),Finset.union_empty,
    insertMiniChain_outside X ζ a target m hm]
  have he (z : Address w) : ((normalizeChain X).pairsAt ζ z).toFinset =
      (X.pairsAt ζ z).toFinset := by
    ext p
    simp only [List.mem_toFinset,mem_normalizeChain_pairsAt]
  rw [he]
  rcases hl with hm' | hn | hb
  · exact (hm hm').elim
  · rw [pinnedRelocate_eq_relocate target a m hn,
      chain_pairsAt_map_local X (relocate target m.c m.lone) a
        (BContext.relocate_respectsAt_of_not_below target a m.c m.lone hn) ζ,list_map_toFinset]
  · rw [pinnedRelocate_of_below target a m (below_trans (below_extend a X.lonePath) hb)]
    have hf := congrArg List.toFinset (BContext.relocate_pairs_below_chain_hole X ζ a target m.c m.lone hb)
    rw [list_map_toFinset] at hf
    exact hf.symm

end WaveTurbulence.Reg.Skeleton
