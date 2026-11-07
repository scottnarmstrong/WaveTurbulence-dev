/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecProd
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcGeo
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcPair

/-! # P4-W2 (session 14, step 1a): the momenta of the two rows of a record

For a record with pair `p₀ = pairOfLeaf (retained)` and branch `b_j = lower` of a placement of a split of a chain (`SplitAt`) whose lower block
`tb` has bottom `b` and lies in `U`, at the engine decoration `x`: the `𝒦` row of the pair carries the momentum `base + L·ξ(retained)`, the `ℒ` row of
the branch carries `base + L·ξ(lower)`, and `lower = retained + ε (E₀ - E₁)` with `|ε| = 1` (`rec_moms`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS5B2 WaveTurbulence.Links
  WaveTurbulence.VineEstS5C.P1 WaveTurbulence.Mole WaveTurbulence.Molecpl

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem rec_moms (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) d) (wN wDec : ℕ) (bk : Fin (assemblyShape hM9 B).I → Fin 4)
    (cons : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) (g g' : (assemblyShape hM9 B).VIdx → ℕ)
    {ι : Type*} {F : CoreFamily G ι} {pstar : ι} {J : Set ι} (sp : SplitAt G F pstar J)
    (hb : sp.tb.b = b) (hsub : sp.tb.U ⊆ U) {L : ℝ} (hL : L ≠ 0) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ))
    (p0 : SourcePair G) (hp : p0 ∈ clRegionalPairs hG U) (hp0 : p0 = pairOfLeaf G hG (F.placement pstar).retained)
    (bj : GBranch G.tree) (hbj : bj ∈ clInteriorBranches R) (hbj' : bj = (F.placement pstar).lower) :
    ∃ ε : ℝ, |ε| = 1 ∧
      rowMom (engDatum hM9 B hG W wN wDec bk cons g g') L x
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)))
          (Sum.inl (assemblyPairBij hG B hM9 ⟨p0, hp⟩)) =
        base + latticePoint L (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1
          (F.placement pstar).retained.toNode) ∧
      rowMom (engDatum hM9 B hG W wN wDec bk cons g g') L x
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)))
          (Sum.inr (assemblyBranchBij hM9 B ⟨bj, hbj⟩)) =
        base + latticePoint L (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1
          (F.placement pstar).lower.toNode) ∧
      base + latticePoint L (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1
          (F.placement pstar).lower.toNode) =
        (base + latticePoint L (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1
          (F.placement pstar).retained.toNode)) +
          ε • (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
            sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) := by
  classical
  obtain ⟨ε, hε, hlow⟩ := exc_low_ret_eps sp R hb hsub L base β hβ ((clNormalizedChainEquiv hL B base β hβ hM9).symm x)
  refine ⟨ε, hε, ?_, ?_, hlow⟩
  · rw [pairMom_eq hM9 B hG W wN wDec bk cons g g' hL base β hβ x, assemblyPairOf_bij]
    show base + latticePoint L (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1
      ((p0.firstLeaf hG).toNode)) = _
    rw [firstLeaf_deco_eq' hG R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x) _ p0 hp0 hp]
  · rw [branchMom_eq hM9 B hG W wN wDec bk cons g g' hL base β hβ x, assemblyBranchOf_bij]
    show base + latticePoint L (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1 bj.toNode) = _
    rw [hbj']

end WaveTurbulence.VineEstS5C.P4.W2
