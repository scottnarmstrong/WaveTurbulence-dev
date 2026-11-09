/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecMom2
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecBotMom
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecMom2
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecBotMom` (sha256 a66c6567525909f9…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4-W2 (session 16, step 1): momenta of a bottom-case record

At a bottom operative member the lower joint of the placement is the bottom `b` of the region (`c.b = lower`), so there is no split: the gap
`σ_b (k_b - k_{kept}) = k_{b⁺} - k_{b⁻}` is the local conservation at `b` (`bot_gap_lattice`).  `bot_low_ret_eps'` is `low = ret + ε₀ r`, `bot_moms'` the pair/branch row momenta (same shape as `rec_moms'`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W2 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
variable {γF : ℝ}
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A WaveTurbulence.GammaLow.Famb.VineEstS2
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS5B2 WaveTurbulence.Links
  WaveTurbulence.VineEstS5C.P1 WaveTurbulence.Mole WaveTurbulence.Molecpl WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P2 WaveTurbulence.GammaLow.Famb.VineEstS5C.P3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS4

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem bot_moms'Γ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) (wN wDec : ℕ) (bk : Fin (assemblyShapeΓ hM9 B).I → Fin 4)
    (cons : Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar)) (g g' : (assemblyShapeΓ hM9 B).VIdx → ℕ)
    {ι : Type*} {F : CoreFamily G ι} {pstar : ι}
    (hbU : b ∈ U) (hlow : (F.placement pstar).lower = b) (hkeep : R.kept = (F.placement pstar).keep)
    {L : ℝ} (hL : L ≠ 0) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (x : (assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ))
    (p0 : SourcePair G) (hp : p0 ∈ clRegionalPairs hG U) (hp0 : p0 = pairOfLeaf G hG (F.placement pstar).retained)
    (bj : GBranch G.tree) (hbj : bj ∈ clInteriorBranches R) (hbj' : bj = (F.placement pstar).lower) :
      rowMom (engDatumΓ hM9 B hG W wN wDec bk cons g g') L x
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)))
          (Sum.inl (assemblyPairBijΓ hG B hM9 ⟨p0, hp⟩)) =
        base + latticePoint L (clExtendIndices R ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1
          (F.placement pstar).retained.toNode) ∧
      rowMom (engDatumΓ hM9 B hG W wN wDec bk cons g g') L x
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)))
          (Sum.inr (assemblyBranchBijΓ hM9 B ⟨bj, hbj⟩)) =
        base + latticePoint L (clExtendIndices R ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1
          (F.placement pstar).lower.toNode) ∧
      base + latticePoint L (clExtendIndices R ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1
          (F.placement pstar).lower.toNode) =
        (base + latticePoint L (clExtendIndices R ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1
          (F.placement pstar).retained.toNode)) +
          lowEps (F.placement pstar).lower •
            (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
              sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) := by
  classical
  refine ⟨?_, ?_, bot_low_ret_eps' R hbU hlow hkeep L base β hβ ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x)⟩
  · rw [pairMom_eqΓ hM9 B hG W wN wDec bk cons g g' hL base β hβ x, assemblyPairOf_bijΓ]
    show base + latticePoint L (clExtendIndices R ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1
      ((p0.firstLeaf hG).toNode)) = _
    rw [firstLeaf_deco_eq' hG R ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x) _ p0 hp0 hp]
  · rw [branchMom_eqΓ hM9 B hG W wN wDec bk cons g g' hL base β hβ x, assemblyBranchOf_bijΓ]
    show base + latticePoint L (clExtendIndices R ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1 bj.toNode) = _
    rw [hbj']

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
