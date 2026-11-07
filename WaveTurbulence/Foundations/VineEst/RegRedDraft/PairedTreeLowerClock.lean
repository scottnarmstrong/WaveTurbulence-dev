/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.EdgeTimeDomain
public import WaveTurbulence.Foundations.WaveB.Lemmas

/-! # The exact lower-boundary clock of a paired-tree kernel -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

theorem leaf_eq_child_of_isParentOf {w : ℕ} {tree : Fin w → TTree}
    (b : GBranch tree) (ℓ : GLeaf tree) (h : b.IsParentOf ℓ) : ∃ i, ℓ.toNode = b.child i := by
  obtain ⟨hj,i,hi⟩ := h
  exact ⟨i,Subtype.ext (Prod.ext hj hi)⟩

/-- Under the source skeleton inequality s < top, KTstar's lone-parent
condition is precisely the incoming clock at its actual distinguished leaf.
The trivial paired tree is included: its incoming clock is the exterior top. -/
theorem pairedTree_lowerClock_iff {G : Garden 1} (hG : IsPairedTree G)
    (ℓ : GLeaf G.tree) (hℓ : G.IsLone ℓ) (top s : ℝ) (hs : s < top)
    (τ : GBranch G.tree → ℝ) :
    (∀ b, G.IsLoneParent b → s < τ b) ↔ s < parentClock top τ ℓ.toNode := by
  constructor
  · intro h
    by_cases hr : ℓ.1.2 = []
    · have he : ℓ.toNode = GNode.root G.tree ℓ.1.1 := Subtype.ext (Prod.ext rfl hr)
      rw [he,parentClock_root]
      exact hs
    · rw [parentClock_nonroot top τ ℓ.toNode hr]
      exact h (ℓ.toNode.parent hr) ⟨ℓ,hℓ,rfl,ℓ.1.2.getLast hr,
        (List.dropLast_append_getLast hr).symm⟩
  · intro h b hb
    obtain ⟨q,hq,hbq⟩ := hb
    have he := hG.eq_of_isLone hq hℓ
    subst q
    obtain ⟨i,hi⟩ := leaf_eq_child_of_isParentOf b ℓ hbq
    rw [hi,parentClock_child] at h
    exact h

end WaveTurbulence.RegRed
