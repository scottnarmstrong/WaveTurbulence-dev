/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.DecodedTree

/-! # The distinguished lone leaf is excluded from all internal chain pair endpoints -/

public section
namespace WaveTurbulence.Reg.Skeleton

 theorem chainLone_not_pairEndpoints (X : RegChain) (ζ : ℤˣ) :
    ((0 : Fin 1),X.lonePath) ∉ pairEndpoints (X.pairsAt ζ (0,[])) := by
  intro h
  let P := X.pairsAt ζ ((0 : Fin 1),[])
  let E := endpointWithLoneEquiv (chainTreeForest X ζ) P
    (decodedTree_pairs_valid X ζ) (chainLoneLeaf X ζ)
    (decodedTree_pairs_cover X ζ) (decodedTree_pair_card X ζ)
  obtain ⟨p,hp,he⟩ := (mem_pairEndpoints_iff P _).mp h
  obtain ⟨i,hi,hei⟩ := List.mem_iff_getElem.mp hp
  rcases he with he | he
  · have hh : E (.inl (⟨i,hi⟩,0)) = E (.inr ()) := by
      apply Subtype.ext
      change P[i].1 = ((0 : Fin 1),X.lonePath)
      exact hei ▸ he.symm
    have hf := E.injective hh
    cases hf
  · have hh : E (.inl (⟨i,hi⟩,1)) = E (.inr ()) := by
      apply Subtype.ext
      change P[i].2 = ((0 : Fin 1),X.lonePath)
      exact hei ▸ he.symm
    have hf := E.injective hh
    cases hf

end WaveTurbulence.Reg.Skeleton
