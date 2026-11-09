/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecMom
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecMom2
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecMom
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecMom2` (sha256 1b0094f5f2f1c86d…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4-W2 (session 15, step 2a): `rec_moms` with the explicit sign `ε₀ = -σ(lower)`

`rec_moms` (session 14) hides `ε` in an existential, which may a priori depend on the decoration; the representation `PieceRepU` needs ONE `ε`.  Here the sign is
explicit: `ε₀ = -(sign of the lower joint)`, the proof of `exc_low_ret_eps` read with `ε` unfolded.
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

theorem rec_moms'Γ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) (wN wDec : ℕ) (bk : Fin (assemblyShapeΓ hM9 B).I → Fin 4)
    (cons : Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar)) (g g' : (assemblyShapeΓ hM9 B).VIdx → ℕ)
    {ι : Type*} {F : CoreFamily G ι} {pstar : ι} {J : Set ι} (sp : SplitAt G F pstar J)
    (hb : sp.tb.b = b) (hsub : sp.tb.U ⊆ U) {L : ℝ} (hL : L ≠ 0) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
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
  obtain ⟨-, -, h1, h2, -⟩ := rec_momsΓ hM9 B hG W wN wDec bk cons g g' sp hb hsub hL base β hβ x p0 hp hp0 bj hbj hbj'
  exact ⟨h1, h2, exc_low_ret_eps' sp R hb hsub L base β hβ ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x)⟩

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
