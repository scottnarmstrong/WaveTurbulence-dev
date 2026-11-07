/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeSigns
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.RelativeDecorations

/-! # Exact coupling powers and sign prefactors in the native kernel reduction -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

theorem nativeCouple_order {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (p : SourcePair S) : (nativeCoupleGarden D hS p).order = (D.couple p).size :=
  decodedCouple_order _

theorem nativeChain_order {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (b : GBranch S.tree) : (decodedTree (D.tree b) (nodeSign S.sig b.1)).order = (D.tree b).size :=
  decodedTree_order _ _

/-- TARGET redkg: the full coupling power and zeta factor are exactly the
original core prefactor times all actual native kernel prefactors. -/
theorem kernelPrefactor_reconstruction {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (c : ℂ) :
    c^(D.garden hS).order * (D.garden hS).zeta = c^S.order * S.zeta *
      (∏ p : SourcePair S, c^(nativeCoupleLayered D hS layer hLayer p).garden.order *
        (nativeCoupleLayered D hS layer hLayer p).garden.zeta) *
      (∏ b : GBranch S.tree, c^(nativeChainLayered D hS layer hLayer b).garden.order *
        (nativeChainLayered D hS layer hLayer b).garden.zeta) := by
  have hq : (∏ p : SourcePair S, c^(nativeCoupleLayered D hS layer hLayer p).garden.order) =
      c^(∑ p : SourcePair S, (D.couple p).size) := by
    have he (p : SourcePair S) : (nativeCoupleLayered D hS layer hLayer p).garden.order =
        (D.couple p).size := nativeCouple_order D hS p
    simp only [he]
    exact Finset.prod_pow_eq_pow_sum _ _ _
  have ht : (∏ b : GBranch S.tree, c^(nativeChainLayered D hS layer hLayer b).garden.order) =
      c^(∑ b : GBranch S.tree, (D.tree b).size) := by
    simp only [nativeChainLayered,nativeChain_order]
    exact Finset.prod_pow_eq_pow_sum _ _ _
  have ho : (D.garden hS).order = S.order + D.size := D.forest_order hS
  rw [ho,zeta_reconstruction D hS layer hLayer,Finset.prod_mul_distrib,Finset.prod_mul_distrib,hq,ht]
  unfold ReconstructionData.size
  rw [pow_add,pow_add]
  ring

end WaveTurbulence.RegRed
