/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Statement
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Canon
public import WaveTurbulence.Foundations.XChain.SNormOperations

/-! # `VineEstCanonLayer`: TARGET Prop `vineest` for an arbitrary layer-indexed input family (R45, step 5)

`VineEstCanon` with `inputsF P Rin` (and `InputRemainder`) replaced by an arbitrary layer-indexed family
`h : ℕ → Mom d → ℝ` with `SNormR (40d) (40d) (h r) ≤ Bh r` for `r ≤ p`, and the right-hand side multiplied by the
region-restricted leaf-size product `regionLeafSize`: the product of `Bh (layer ℓ)` over the input leaves of the native
couples and trees of the rows of the region `U` (the only leaves `K^U` sees). -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton
  WaveTurbulence.VineEstS4 VineParamContract TTree
open scoped ENNReal

/-- The leaf-size product of the rows of the region `U`: over the input leaves of the native couple of every regional
pair and of the native tree of every interior branch, the size `Bh (layer ℓ)` of the layer input at the leaf. -/
noncomputable def regionLeafSize {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (RD : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (Bh : ℕ → ℝ) : ℝ :=
  (∏ p ∈ clRegionalPairs hG U, ∏ ℓ ∈ inputLeaves (nativeCoupleLayered RD hG layer hLayer p).garden,
      Bh ((nativeCoupleLayered RD hG layer hLayer p).layer ℓ.toNode)) *
    ∏ v ∈ clInteriorBranches R, ∏ ℓ ∈ inputLeaves (nativeChainLayered RD hG layer hLayer v).garden,
      Bh ((nativeChainLayered RD hG layer hLayer v).layer ℓ.toNode)

end WaveTurbulence.VineEstS5C
