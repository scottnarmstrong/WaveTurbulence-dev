/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.BContext.OperationBPairFidelity
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ListPairImages
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.RawChainInsertion

/-! # Arbitrary-width normalized B insertion at an actual represented code node -/

public section
namespace WaveTurbulence.Reg.Skeleton.BContext
open TTree

private theorem perm_finset {α : Type*} [DecidableEq α] {L M : List α}
    (h : L.Perm M) : L.toFinset = M.toFinset := by
  ext z
  simp only [List.mem_toFinset]
  exact h.mem_iff

theorem normalizedCouple_pairs {w : ℕ} (Q : RegCpl) (σ : Fin w → ℤˣ)
    (a b target : Fin w × Path) (m : MiniTreeCode) (hab : IncompAddr a b)
    (ha : nodeSign σ a = 1) (hb : nodeSign σ b = -1) (ht : target ∈ coupleNodes Q a b) :
    ((normalizeCouple (insertMiniCouple Q a b target m)).pairsAt a b).toFinset =
      ((Q.pairsAt a b).toFinset.image (fun p =>
        (relocate target m.c m.lone p.1,relocate target m.c m.lone p.2))) ∪ miniPairs σ target m := by
  classical
  have hn : ((normalizeCouple (insertMiniCouple Q a b target m)).pairsAt a b).toFinset =
      ((insertMiniCouple Q a b target m).pairsAt a b).toFinset := by
    ext z
    simp only [List.mem_toFinset,mem_normalizeCouple_pairsAt]
  rw [hn,perm_finset (insertMiniCouple_pairs Q σ a b target m hab ha hb ht),List.toFinset_append,list_map_toFinset]
  exact congrArg (fun P => _ ∪ P) (miniChain_pairsAt_finset m σ target)

/-- The context pair set moves literally, and the inserted mini-tree supplies its two pairs. -/
theorem normalizedChain_pairs {w : ℕ} (X : RegChain) (σ : Fin w → ℤˣ)
    (ζ : ℤˣ) (a target : Fin w × Path) (m : MiniTreeCode)
    (ha : nodeSign σ a = ζ) (ht : target ∈ chainNodes X ζ a) :
    ((normalizeChain (insertMiniChain X ζ a target m)).pairsAt ζ a).toFinset =
      ((X.pairsAt ζ a).toFinset.image (fun p =>
        (relocate target m.c m.lone p.1,relocate target m.c m.lone p.2))) ∪ miniPairs σ target m := by
  classical
  have hn : ((normalizeChain (insertMiniChain X ζ a target m)).pairsAt ζ a).toFinset =
      ((insertMiniChain X ζ a target m).pairsAt ζ a).toFinset := by
    ext z
    simp only [List.mem_toFinset,mem_normalizeChain_pairsAt]
  rw [hn,perm_finset (insertMiniChain_pairs X σ ζ a target m ha ht).1,
    List.toFinset_append,list_map_toFinset]
  exact congrArg (fun P => _ ∪ P) (miniChain_pairsAt_finset m σ target)

theorem normalizedChain_hole {w : ℕ} (X : RegChain) (σ : Fin w → ℤˣ)
    (ζ : ℤˣ) (a target : Fin w × Path) (m : MiniTreeCode)
    (ha : nodeSign σ a = ζ) (ht : target ∈ chainNodes X ζ a) :
    addrExt a (normalizeChain (insertMiniChain X ζ a target m)).lonePath =
      relocate target m.c m.lone (addrExt a X.lonePath) := by
  rw [normalizeChain_lonePath]
  exact (insertMiniChain_pairs X σ ζ a target m ha ht).2

/-- Insertion at the chain hole appends a mini-chain and retains all prior context pairs. -/
theorem normalizedAppend_pairs {w : ℕ} (X : RegChain) (σ : Fin w → ℤˣ)
    (ζ : ℤˣ) (a : Fin w × Path) (m : MiniTreeCode) (ha : nodeSign σ a = ζ) :
    ((normalizeChain (appendChain X (miniChain m))).pairsAt ζ a).toFinset =
      ((X.pairsAt ζ a).toFinset.image (fun p =>
        (relocate (addrExt a X.lonePath) m.c m.lone p.1,
          relocate (addrExt a X.lonePath) m.c m.lone p.2))) ∪
        miniPairs σ (addrExt a X.lonePath) m := by
  classical
  have hn : ((normalizeChain (appendChain X (miniChain m))).pairsAt ζ a).toFinset =
      ((appendChain X (miniChain m)).pairsAt ζ a).toFinset := by
    ext z
    simp only [List.mem_toFinset,mem_normalizeChain_pairsAt]
  have hs : nodeSign σ (addrExt a X.lonePath) = ζ := by
    rw [nodeSign_addrExt,lonePath_sign,ha]
  have hf := congrArg List.toFinset (relocate_pairs_below_chain_hole X ζ a
    (addrExt a X.lonePath) m.c m.lone ⟨rfl,List.prefix_refl _⟩)
  rw [list_map_toFinset] at hf
  rw [hn,appendChain_pairsAt,List.toFinset_append,hf,← hs]
  rw [miniChain_pairsAt_finset]

end WaveTurbulence.Reg.Skeleton.BContext
