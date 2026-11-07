/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecMom

/-! # P4-W2 (session 15, step 2a): `rec_moms` with the explicit sign `ε₀ = -σ(lower)`

`rec_moms` (session 14) hides `ε` in an existential, which may a priori depend on the decoration; the representation `PieceRepU` needs ONE `ε`.  Here the sign is
explicit: `ε₀ = -(sign of the lower joint)`, the proof of `exc_low_ret_eps` read with `ε` unfolded.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS5B2 WaveTurbulence.Links
  WaveTurbulence.VineEstS5C.P1 WaveTurbulence.Mole WaveTurbulence.Molecpl

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The sign `ε₀ = -σ(lower)` of a placement. -/
noncomputable def lowEps {S : Garden w} (v : GBranch S.tree) : ℝ := -(((S.sign v.toNode : ℤ) : ℝ))

theorem abs_lowEps {S : Garden w} (v : GBranch S.tree) : |lowEps v| = 1 := by
  unfold lowEps
  rcases Int.units_eq_one_or (S.sign v.toNode) with h1 | h1 <;> simp [h1]

theorem exc_low_ret_eps' {S : Garden w} {ι : Type*} {F : CoreFamily S ι} {pstar : ι} {J : Set ι}
    (sp : SplitAt S F pstar J) {U : Finset (GBranch S.tree)} {a b : GBranch S.tree} (R : CLRegionData S U a b)
    (hb : sp.tb.b = b) (hsub : sp.tb.U ⊆ U) (L : ℝ) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((S.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3)
    (κ : CLLocalDecoration R L base (fun j => base + latticePoint L (β j))) :
    base + latticePoint L (clExtendIndices R κ.1 (F.placement pstar).lower.toNode) =
        (base + latticePoint L (clExtendIndices R κ.1 (F.placement pstar).retained.toNode)) +
          lowEps (F.placement pstar).lower • (sumintBoundary (S.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
            sumintBoundary (S.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) := by
  have h := exc_gap sp R hb hsub L base _ κ
  have hg := sumintBoundary_gap_physical (L := L) (S.sign a.toNode) base β hβ
  rw [hg]
  unfold lowEps
  set σ : ℝ := ((S.sign (F.placement pstar).lower.toNode : ℤ) : ℝ) with hσ
  have hσ1 : σ = 1 ∨ σ = -1 := by
    rcases Int.units_eq_one_or (S.sign (F.placement pstar).lower.toNode) with h1 | h1 <;> simp [hσ, h1]
  have h' : latticePoint L (clExtendIndices R κ.1 (F.placement pstar).lower.toNode) -
      latticePoint L (clExtendIndices R κ.1 (F.placement pstar).retained.toNode) =
      σ • ((base + latticePoint L (β 2)) - (base + latticePoint L (β 3))) := by
    have := congrArg (fun z => σ • z) h
    simp only [smul_smul] at this
    rcases hσ1 with h1 | h1 <;> rw [h1] at this ⊢ <;> simpa using this
  have hl : latticePoint L (β 2 - β 3) = latticePoint L (β 2) - latticePoint L (β 3) :=
    map_sub (latticePointAddHom (d := d) L) (β 2) (β 3)
  rw [hl, neg_smul, smul_neg, neg_neg]
  have h3 : latticePoint L (clExtendIndices R κ.1 (F.placement pstar).lower.toNode) =
      latticePoint L (clExtendIndices R κ.1 (F.placement pstar).retained.toNode) +
        σ • (latticePoint L (β 2) - latticePoint L (β 3)) := by
    have e : (base + latticePoint L (β 2)) - (base + latticePoint L (β 3)) =
        latticePoint L (β 2) - latticePoint L (β 3) := by abel
    rw [e] at h'
    rw [← h']; abel
  rw [h3]; abel

theorem rec_moms' (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) d) (wN wDec : ℕ) (bk : Fin (assemblyShape hM9 B).I → Fin 4)
    (cons : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) (g g' : (assemblyShape hM9 B).VIdx → ℕ)
    {ι : Type*} {F : CoreFamily G ι} {pstar : ι} {J : Set ι} (sp : SplitAt G F pstar J)
    (hb : sp.tb.b = b) (hsub : sp.tb.U ⊆ U) {L : ℝ} (hL : L ≠ 0) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ))
    (p0 : SourcePair G) (hp : p0 ∈ clRegionalPairs hG U) (hp0 : p0 = pairOfLeaf G hG (F.placement pstar).retained)
    (bj : GBranch G.tree) (hbj : bj ∈ clInteriorBranches R) (hbj' : bj = (F.placement pstar).lower) :
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
          lowEps (F.placement pstar).lower •
            (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
              sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) := by
  classical
  obtain ⟨-, -, h1, h2, -⟩ := rec_moms hM9 B hG W wN wDec bk cons g g' sp hb hsub hL base β hβ x p0 hp hp0 bj hbj hbj'
  exact ⟨h1, h2, exc_low_ret_eps' sp R hb hsub L base β hβ ((clNormalizedChainEquiv hL B base β hβ hM9).symm x)⟩

end WaveTurbulence.VineEstS5C.P4.W2
