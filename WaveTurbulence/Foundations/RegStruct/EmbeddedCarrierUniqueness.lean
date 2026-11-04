/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.FrameAddressMap

/-! # Carrier equality from an injective common ambient pairing -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- Two plain couples with identical trees and identical embedded pairings are equal.
The pairing relation is that of the actual decoded ambient code Q. -/
theorem carrier_eq_of_embedded_pairing (Q : RegCpl) (G H : Garden 2)
    (hG : IsCouple G) (hH : IsCouple H) (htree : G.tree = H.tree)
    (f : (Fin 2 × Path) → (Fin 2 × Path)) (hf : Function.Injective f)
    (hg : ∀ ℓ : GLeaf G.tree, (f ℓ.1,f (G.pair ℓ).1) ∈ symmPairs Q.raw.2)
    (hh : ∀ ℓ : GLeaf H.tree, (f ℓ.1,f (H.pair ℓ).1) ∈ symmPairs Q.raw.2) : G = H := by
  obtain ⟨gs,gt,gp,gm,gpp,geq,gsgn⟩ := G
  obtain ⟨hs,ht,hp,hm,hpp,heq,hsgn⟩ := H
  change gt = ht at htree
  subst ht
  have hsig : gs = hs := hG.2.trans hH.2.symm
  subst hs
  have hpair : gp = hp := by
    funext ℓ
    apply Subtype.ext
    exact hf (decodedPair_functional Q (hg ℓ) (hh ℓ))
  have hmark : gm = hm := by
    funext ℓ
    exact (hG.1 ℓ).trans (hH.1 ℓ).symm
  cases hpair
  cases hmark
  rfl

/-- Codes with equal trees and pair blocks in the same injective ambient frame
have the same actual decoded carrier. This is a carrier equality theorem,
not the still-pending code injectivity theorem. -/
theorem decodedCouple_eq_of_common_frame (Q C D : RegCpl) (a b : Fin 2 × Path)
    (hab : IncompAddr a b) (ht : C.trees = D.trees)
    (hC : ∀ p ∈ symmPairs (C.pairsAt a b), p ∈ symmPairs Q.raw.2)
    (hD : ∀ p ∈ symmPairs (D.pairsAt a b), p ∈ symmPairs Q.raw.2) :
    decodedCouple C = decodedCouple D := by
  have hc := decodedCouple_decodes C
  have hd := decodedCouple_decodes D
  have htree : (decodedCouple C).tree = (decodedCouple D).tree := by
    change coupleForest C = coupleForest D
    simp only [coupleForest,ht]
  apply carrier_eq_of_embedded_pairing Q _ _ hc.1 hd.1 htree
    (frameAddress a b) (frameAddress_injective a b hab)
  · intro ℓ
    exact hC _ (symmPairs_frameAddress_mem C a b _ (hc.2.2.2 ℓ))
  · intro ℓ
    exact hD _ (symmPairs_frameAddress_mem D a b _ (hd.2.2.2 ℓ))

end WaveTurbulence.Reg
