/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourceMiniClassification
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Carrier

/-! # Canonical pair membership recovers the actual endpoint leaves and partner identity -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem sourcePairs_actual_endpoints {w : ℕ} (G : Garden w) (p : Pair w) (hp : p ∈ sourcePairs G) :
    ∃ ℓ q : GLeaf G.tree, ℓ.1 = p.1 ∧ q.1 = p.2 ∧ G.pair ℓ = q := by
  obtain ⟨ℓ,hℓ,rfl⟩ := Finset.mem_image.mp hp
  exact ⟨ℓ,G.pair ℓ,rfl,rfl,rfl⟩

theorem leafBond_of_orient_mem {w : ℕ} (G : Garden w) (b c : GBranch G.tree)
    (i j : Fin 3) (ζ : ℤˣ)
    (hp : orient (b.child i).1 ζ (c.child j).1 ∈ sourcePairs G) : LeafBond G b c i j := by
  by_cases hζ : ζ = 1
  · rw [orient,ite_eq_left hζ] at hp
    obtain ⟨ℓ,q,hℓ,hq,hp⟩ := sourcePairs_actual_endpoints G _ hp
    exact ⟨ℓ,q,Subtype.ext hℓ,Subtype.ext hq,hp⟩
  · rw [orient,ite_eq_right hζ] at hp
    obtain ⟨q,ℓ,hq,hℓ,hp⟩ := sourcePairs_actual_endpoints G _ hp
    exact ⟨ℓ,q,Subtype.ext hℓ,Subtype.ext hq,by rw [← hp,G.pair_pair]⟩

end WaveTurbulence.Reg.Skeleton
