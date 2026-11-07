/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.RegRedDraft.NativeChainDecorations
public import WaveTurbulence.Foundations.RegStruct.PairFunctionality

/-! # Recovering actual partners from the native paired-tree code list -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

noncomputable def chainEndpointEquiv (X : RegChain) (ζ : ℤˣ) :
    ((Fin (X.pairsAt ζ ((0 : Fin 1),[])).length × Fin 2) ⊕ Unit) ≃
      GLeaf (chainTreeForest X ζ) :=
  endpointWithLoneEquiv (chainTreeForest X ζ) (X.pairsAt ζ (0,[]))
    (decodedTree_pairs_valid X ζ) (chainLoneLeaf X ζ) (decodedTree_pairs_cover X ζ)
    (decodedTree_pair_card X ζ)

theorem chainPair_functional (X : RegChain) (ζ : ℤˣ) {x y z : Address 1}
    (hy : (x,y) ∈ symmPairs (X.pairsAt ζ (0,[])))
    (hz : (x,z) ∈ symmPairs (X.pairsAt ζ (0,[]))) : y = z := by
  obtain ⟨s,hs,hs'⟩ := pair_slot_witness (chainTreeForest X ζ) _ (decodedTree_pairs_valid X ζ) x y hy
  obtain ⟨t,ht,ht'⟩ := pair_slot_witness (chainTreeForest X ζ) _ (decodedTree_pairs_valid X ζ) x z hz
  have he : chainEndpointEquiv X ζ (.inl s) = chainEndpointEquiv X ζ (.inl t) :=
    Subtype.ext (hs.trans ht.symm)
  have hst := Sum.inl.inj ((chainEndpointEquiv X ζ).injective he)
  subst t
  exact hs'.symm.trans ht'

theorem chainPair_first_ne_lone (X : RegChain) (ζ : ℤˣ) {x y : Address 1}
    (h : (x,y) ∈ symmPairs (X.pairsAt ζ (0,[]))) : x.2 ≠ X.lonePath := by
  obtain ⟨s,hs,_⟩ := pair_slot_witness (chainTreeForest X ζ) _ (decodedTree_pairs_valid X ζ) x y h
  intro hx
  have he : chainEndpointEquiv X ζ (.inl s) = chainEndpointEquiv X ζ (.inr ()) :=
    Subtype.ext (hs.trans (Prod.ext (Subsingleton.elim _ _) hx))
  have hbad := (chainEndpointEquiv X ζ).injective he
  cases hbad

/-- The one-direction decoder already recovers every listed actual partner,
including the m=1 code case, by exact endpoint bijectivity. -/
theorem pair_of_decodesTree {X : RegChain} {G : Garden 1} (hd : X.DecodesTree G)
    (p : Pair 1) (hp : p ∈ symmPairs (X.pairsAt (G.sig 0) (0,[])))
    (hv : p.1.2 ∈ (G.tree p.1.1).leaves) : (G.pair ⟨p.1,hv⟩).1 = p.2 :=
  chainPair_functional X (G.sig 0)
    (hd.2.2 ⟨p.1,hv⟩ (chainPair_first_ne_lone X (G.sig 0) hp)) hp

end WaveTurbulence.RegRed
