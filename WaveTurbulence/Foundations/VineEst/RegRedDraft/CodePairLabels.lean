/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.ChainPairFunctionality
public import WaveTurbulence.Foundations.RegStruct.DecodedPairRecovery

/-! # Actual paired-constant labels on every listed couple and paired-tree edge -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

theorem labels_eq_of_coupleCodePair {Q : RegCpl} {G : Garden 2} (hd : Q.Decodes G)
    {V : Type*} (κ : GNode G.tree → V) (hκ : ∀ ℓ, κ ℓ.toNode = κ (G.pair ℓ).toNode)
    (p : Pair 2) (hp : p ∈ Q.raw.2) (x y : GLeaf G.tree)
    (hx : x.1 = p.1) (hy : y.1 = p.2) : κ x.toNode = κ y.toNode := by
  have hv : p.1.2 ∈ (G.tree p.1.1).leaves := hx ▸ x.2
  have hm := pair_of_decodes hd p ((mem_symmPairs_iff _ _).mpr (Or.inl hp)) hv
  have hx' : x = ⟨p.1,hv⟩ := Subtype.ext hx
  have hpair : G.pair x = y := Subtype.ext ((congrArg (fun ℓ : GLeaf G.tree => ℓ.1)
    (congrArg G.pair hx')).trans (hm.trans hy.symm))
  exact (hκ x).trans (congrArg (fun ℓ : GLeaf G.tree => κ ℓ.toNode) hpair)

theorem labels_eq_of_chainCodePair {X : RegChain} {G : Garden 1} (hd : X.DecodesTree G)
    {V : Type*} (κ : GNode G.tree → V) (hκ : ∀ ℓ, κ ℓ.toNode = κ (G.pair ℓ).toNode)
    (p : Pair 1) (hp : p ∈ X.pairsAt (G.sig 0) (0,[])) (x y : GLeaf G.tree)
    (hx : x.1 = p.1) (hy : y.1 = p.2) : κ x.toNode = κ y.toNode := by
  have hv : p.1.2 ∈ (G.tree p.1.1).leaves := hx ▸ x.2
  have hm := pair_of_decodesTree hd p ((mem_symmPairs_iff _ _).mpr (Or.inl hp)) hv
  have hx' : x = ⟨p.1,hv⟩ := Subtype.ext hx
  have hpair : G.pair x = y := Subtype.ext ((congrArg (fun ℓ : GLeaf G.tree => ℓ.1)
    (congrArg G.pair hx')).trans (hm.trans hy.symm))
  exact (hκ x).trans (congrArg (fun ℓ : GLeaf G.tree => κ ℓ.toNode) hpair)

end WaveTurbulence.RegRed
