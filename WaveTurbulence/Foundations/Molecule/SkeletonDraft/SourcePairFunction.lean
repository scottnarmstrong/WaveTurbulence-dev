/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.PairMembership

/-! # Literal canonical pairs determine the actual ambient partner in either orientation -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem sourcePair_partner {w : ℕ} (G : Garden w) (x y : GLeaf G.tree)
    (h : (x.1,y.1) ∈ sourcePairs G ∨ (y.1,x.1) ∈ sourcePairs G) : G.pair x = y := by
  rcases h with h | h
  · obtain ⟨a,b,ha,hb,hab⟩ := sourcePairs_actual_endpoints G _ h
    have hx : x = a := Subtype.ext ha.symm
    have hy : y = b := Subtype.ext hb.symm
    exact hx ▸ hy ▸ hab
  · obtain ⟨a,b,ha,hb,hab⟩ := sourcePairs_actual_endpoints G _ h
    have hx : x = b := Subtype.ext hb.symm
    have hy : y = a := Subtype.ext ha.symm
    rw [hx,hy,← hab,G.pair_pair]

end WaveTurbulence.Reg.Skeleton
