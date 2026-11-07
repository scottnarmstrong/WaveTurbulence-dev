/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RowMatch
public import WaveTurbulence.Foundations.VineEst.VineEstS5B.StateInt2
public import WaveTurbulence.Foundations.VineEst.VineEstS5B.Frame

/-! # V5W-B (ruling F2): under `RowSel.plain` every selected body is main's original body, by `rfl`

For each row-carrying definition changed by the in-place `RowSel` generalization, the plain specialization is
definitionally main's original body (copied verbatim from main 796c0f5f on the right-hand sides):

* `clLocalStarProduct_plain` (`RegRedDraft/CLLocalFactors`), `starProd_plain` (`VineEstS4/SplitSummand`);
* `assemblyClockedS_plain` (`VineEstS3/AssemblyClocked`: the selected rows are `assemblyClocked`);
* `qRow_plain`, `tRow_plain` (`VineEstS5B/Frame`), `rowQ_plain`, `rowT_plain` (`VineEstS5B/StateInt2`);
* `natCR3_W_plain` (`VineEstS5C/P4/W2/RowMatch`);
* `assemblyWK_plain`, `assemblyWL_plain` (`VineEstS2/CLStep2Weights`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEst
open WaveTurbulence WaveTurbulence.VineParamContract WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5C.P4.W2 WaveTurbulence.LFTwist TTree Reg Reg.Skeleton
  RegRed

section Region
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem clLocalStarProduct_plain (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (κ : GNode G.tree → (Fin d → ℤ))
    (t : Fin 3 → ℝ) (τ : CLInternalTime R) :
    clLocalStarProduct (rowSel := RowSel.plain) D hG R L γ δ F layer hLayer base κ t τ =
      (let u := clLocalClock R t τ
      (∏ p ∈ clRegionalPairs hG U, KQstar L γ δ F (nativeCoupleLayered D hG layer hLayer p)
        (parentClock (t 0) u (p.firstLeaf hG).toNode) (parentClock (t 0) u (p.secondLeaf hG).toNode)
        (cosetDecoration G L base κ (p.firstLeaf hG).toNode)) *
      (∏ v ∈ clInteriorBranches R, KTstar L γ δ F (nativeChainLayered D hG layer hLayer v)
        (parentClock (t 0) u v.toNode) (u v) (cosetDecoration G L base κ v.toNode))) := rfl

theorem starProd_plain (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
    (V : Finset (GBranch G.tree)) (a : GBranch G.tree) (top : ℝ)
    (x : GNode G.tree → (Fin d → ℤ)) (u : GBranch G.tree → ℝ) :
    starProd (rowSel := RowSel.plain) D hG L γ δ F layer hLayer base V a top x u =
      (∏ p ∈ clRegionalPairs hG V, KQstar L γ δ F (nativeCoupleLayered D hG layer hLayer p)
        (parentClock top u (p.firstLeaf hG).toNode) (parentClock top u (p.secondLeaf hG).toNode)
        (cosetDecoration G L base x (p.firstLeaf hG).toNode)) *
      (∏ v ∈ V.erase a, KTstar L γ δ F (nativeChainLayered D hG layer hLayer v)
        (parentClock top u v.toNode) (u v) (cosetDecoration G L base x v.toNode)) := rfl

theorem qRow_plain (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
    (top : ℝ) (x : GNode G.tree → (Fin d → ℤ)) (u : GBranch G.tree → ℝ) (p : SourcePair G) :
    qRow (rowSel := RowSel.plain) D hG L γ δ F layer hLayer base top x u p =
      KQstar L γ δ F (nativeCoupleLayered D hG layer hLayer p)
        (parentClock top u (p.firstLeaf hG).toNode) (parentClock top u (p.secondLeaf hG).toNode)
        (cosetDecoration G L base x (p.firstLeaf hG).toNode) := rfl

theorem tRow_plain (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
    (top : ℝ) (x : GNode G.tree → (Fin d → ℤ)) (u : GBranch G.tree → ℝ) (v : GBranch G.tree) :
    tRow (rowSel := RowSel.plain) D hG L γ δ F layer hLayer base top x u v =
      KTstar L γ δ F (nativeChainLayered D hG layer hLayer v)
        (parentClock top u v.toNode) (u v) (cosetDecoration G L base x v.toNode) := rfl

variable {R : CLRegionData G U a b} {n : ℕ}

theorem assemblyClockedS_plain (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) (W : SumintWeightClockData (assemblyShape hM9 B) d) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) :
    assemblyClockedS (rowSel := RowSel.plain) hM9 B RD hG W L γ δ F layer hLayer =
      assemblyClocked hM9 B RD hG W L γ δ F layer hLayer := rfl

theorem assemblyWK_plain (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (D : ReconstructionData G)
    (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (t : Fin 3 → ℝ) (τ : CLInternalTime R)
    (v : (assemblyShape hM9 B).VIdx) (k : Mom d) :
    assemblyWK (rowSel := RowSel.plain) hM9 B D hG L γ δ F layer hLayer t τ v k =
      KQstar L γ δ F (nativeCoupleLayered D hG layer hLayer (assemblyPairOf hM9 B hG v).1)
        (parentClock (t 0) (clLocalClock R t τ) ((assemblyPairOf hM9 B hG v).1.firstLeaf hG).toNode)
        (parentClock (t 0) (clLocalClock R t τ) ((assemblyPairOf hM9 B hG v).1.secondLeaf hG).toNode) k := rfl

theorem assemblyWL_plain (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (D : ReconstructionData G)
    (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (t : Fin 3 → ℝ) (τ : CLInternalTime R)
    (v : (assemblyShape hM9 B).VIdx) (k : Mom d) :
    assemblyWL (rowSel := RowSel.plain) hM9 B D hG L γ δ F layer hLayer t τ v k =
      KTstar L γ δ F (nativeChainLayered D hG layer hLayer (assemblyBranchOf hM9 B v).1)
        (parentClock (t 0) (clLocalClock R t τ) (assemblyBranchOf hM9 B v).1.toNode)
        (clLocalClock R t τ (assemblyBranchOf hM9 B v).1) k := rfl

theorem natCR3_W_plain (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) d) (wN wDec : ℕ) (bk : Fin (assemblyShape hM9 B).I → Fin 4)
    (cons : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) (g g' : (assemblyShape hM9 B).VIdx → ℕ)
    (RD : ReconstructionData G) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer) :
    (natCR3 (rowSel := RowSel.plain) hM9 B hG W wN wDec bk cons g g' RD L γ δ F layer hLayer).W =
      fun ρ c _ k => match ρ with
        | Sum.inl v => KQstar L γ δ F (nativeCoupleLayered RD hG layer hLayer (assemblyPairOf hM9 B hG v).1) (c 0) (c 1) k
        | Sum.inr v => KTstar L γ δ F (nativeChainLayered RD hG layer hLayer (assemblyBranchOf hM9 B v).1) (c 0) (c 1) k :=
  rfl

end Region

section State
variable {w : ℕ} {ι : Type*} {d : ℕ}

theorem rowQ_plain (κ : KPar d) (G : FamilyReconstruction w ι) (i : ι) :
    rowQ (rowSel := RowSel.plain) κ G i = KQstar κ.L κ.γ κ.δ κ.F (sigStar G i).2.1 := rfl

theorem rowT_plain (κ : KPar d) (G : FamilyReconstruction w ι) (i : ι) :
    rowT (rowSel := RowSel.plain) κ G i = KTstar κ.L κ.γ κ.δ κ.F (sigStar G i).2.2 := rfl

end State

end WaveTurbulence.VineEst
