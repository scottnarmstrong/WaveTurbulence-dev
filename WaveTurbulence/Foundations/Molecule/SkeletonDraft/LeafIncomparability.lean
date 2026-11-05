/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.RawPartner

/-! # Distinct actual leaves have incomparable rooted addresses -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem leaves_incomparable {w : ℕ} (tree : Fin w → TTree) (ℓ q : GLeaf tree) (hne : q ≠ ℓ) :
    ℓ.toNode.Incomparable q.toNode := by
  constructor
  · intro h
    change ℓ.1.1 = q.1.1 ∧ ℓ.1.2 <+: q.1.2 at h
    have hq : q.1.2 ∈ (tree ℓ.1.1).nodes := by
      rw [h.1]
      exact TTree.leaves_subset_nodes _ q.2
    have hp := leaf_prefix_node_eq ℓ.2 hq h.2
    apply hne
    exact Subtype.ext (Prod.ext h.1.symm hp.symm)
  · intro h
    change q.1.1 = ℓ.1.1 ∧ q.1.2 <+: ℓ.1.2 at h
    have hl : ℓ.1.2 ∈ (tree q.1.1).nodes := by
      rw [h.1]
      exact TTree.leaves_subset_nodes _ ℓ.2
    have hp := leaf_prefix_node_eq q.2 hl h.2
    apply hne
    exact Subtype.ext (Prod.ext h.1 hp)

end WaveTurbulence.Reg.Skeleton
