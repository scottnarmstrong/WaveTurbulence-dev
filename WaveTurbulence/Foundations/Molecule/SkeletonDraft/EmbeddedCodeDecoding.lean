/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourcePairFunction
public import WaveTurbulence.Foundations.RegStruct.FrameAddressMap
public import WaveTurbulence.Foundations.RegStruct.DecodedCouple

/-! # Code decoding from an actual injective pairing embedding into an ambient garden -/

public section
namespace WaveTurbulence.Reg.Skeleton

 theorem decodes_of_actual_embedding {w : ℕ} (C : RegCpl) (H : Garden 2) (G : Garden w)
    (hH : IsCouple H) (ht : H.tree = coupleForest C)
    (a b : Address w) (f : GLeaf H.tree ↪ GLeaf G.tree)
    (hf : ∀ ℓ, (f ℓ).1 = frameAddress a b ℓ.1)
    (hpair : ∀ ℓ, f (H.pair ℓ) = G.pair (f ℓ))
    (hP : ∀ p ∈ C.pairsAt a b, p ∈ sourcePairs G) : C.Decodes H := by
  have htree : H.tree 0 = C.trees.1 ∧ H.tree 1 = C.trees.2 := by
    rw [ht]
    exact ⟨rfl,rfl⟩
  refine ⟨hH,htree.1,htree.2,?_⟩
  intro ℓ
  let x : GLeaf (decodedCouple C).tree := ⟨ℓ.1,by
    change ℓ.1.2 ∈ (coupleForest C ℓ.1.1).leaves
    rw [← ht]
    exact ℓ.2⟩
  let y : GLeaf H.tree := ⟨((decodedCouple C).pair x).1,by
    rw [ht]
    exact ((decodedCouple C).pair x).2⟩
  have hy : (ℓ.1,y.1) ∈ symmPairs C.raw.2 := (decodedCouple_decodes C).2.2.2 x
  have hframe := symmPairs_frameAddress_mem C a b _ hy
  have he : G.pair (f ℓ) = f y := by
    apply sourcePair_partner
    rw [hf,hf]
    rcases (mem_symmPairs_iff _ _).mp hframe with hp | hp
    · exact Or.inl (hP _ hp)
    · exact Or.inr (hP _ hp)
  have hloc : H.pair ℓ = y := f.injective ((hpair ℓ).trans he)
  rw [hloc]
  exact hy

end WaveTurbulence.Reg.Skeleton
