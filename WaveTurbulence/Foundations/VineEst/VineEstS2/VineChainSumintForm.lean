/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLStep2Time

/-! # TARGET vineest Step 2: the vine-chain contribution in `sumint` input form

`vineChain_eq_sumintForm` identifies the actual recentered regional kernel of a vine chain
(the expression `\widetilde K` of TARGET (tildeK2)) with

`coupling^{n₁} ζ ∑ₓ ε(x) ∫_{timeDom(q,constraints)} signedPhase(D)(x,r,t,τ) ∏ᵥ 𝒦ᵥ(kᵥ) ℒᵥ(ℓᵥ)`,

where `D = sourceSumintDatum` is the frozen `sumint` datum of the chain, `kᵥ = D.kVec`,
`ℓᵥ = D.ℓVec` are evaluated at the boundary vector `sumintBoundary ζ (base + β)`, `timeDom` is
the frozen `sumint` time domain with `q` the source layers and the constraints the parent order,
and `𝒦ᵥ, ℒᵥ` are the actual starred kernels `K_Q^*, K_T^*` of the garden (time dependent; their
expansion into time-independent weights is TARGET Step 3). -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- In the physical lattice the frozen boundary vectors satisfy `e - f = -(g - h)`. -/
theorem sumintBoundary_gap_physical {L : ℝ} (ζ : ℤˣ) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : (ζ : ℤ) • (β 0 - β 1) = β 2 - β 3) :
    sumintBoundary ζ (fun j => base + latticePoint L (β j)) 0 -
        sumintBoundary ζ (fun j => base + latticePoint L (β j)) 1 =
      -(latticePoint L (β 2 - β 3)) := by
  have h1 := congrArg (latticePointAddHom (d := d) L) hβ
  rw [map_zsmul] at h1
  simp only [map_sub] at h1
  have hp : (ζ : ℤ) • ((base + latticePoint L (β 0)) - (base + latticePoint L (β 1))) =
      (base + latticePoint L (β 2)) - (base + latticePoint L (β 3)) := by
    rw [add_sub_add_left_eq_sub, add_sub_add_left_eq_sub]
    exact h1
  rw [sumintBoundary_gap ζ (fun j => base + latticePoint L (β j)) hp, add_sub_add_left_eq_sub,
    latticePoint_sub]

/-- One summand of the recentered regional kernel in `sumint` form. -/
theorem clLocalRecenteredSummand_sumint (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (D : ReconstructionData G) (hG : G.IsPlain) (W : SumintWeightClockData (assemblyShape hM9 B) d)
    (hpar : ∀ v, W.param v = 0) (hbad : ∀ i, W.badKind i ≠ 2)
    {L : ℝ} (hL : L ≠ 0) (γ δ η : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3)
    (x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ)) (t : Fin 3 → ℝ)
    (τ : (assemblyShape hM9 B).TVar → ℝ) :
    clLocalRecenteredSummand D hG R L γ δ F layer hLayer base (fun j => base+latticePoint L (β j)) t
        ((clNormalizedChainEquiv hL B base β hβ hM9).symm x) (assemblyClockEquiv hM9 B τ) =
      (clRegionalEpsilon G U (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) : ℂ) *
        ((assemblyClockEquiv hM9 B ⁻¹' clLocalTimeDomain R
            (fun v => layer (D.coreBranch hG v).toNode) t).indicator
          (fun τ => signedPhase (sourceSumintDatum hM9 B hG W)
              (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) L γ (2*δ) η x
              (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
                sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) (t 0) τ *
            ∏ v, (assemblyWK hM9 B D hG L γ δ F layer hLayer t (assemblyClockEquiv hM9 B τ) v
                ((sourceSumintDatum hM9 B hG W).kVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v) *
              assemblyWL hM9 B D hG L γ δ F layer hLayer t (assemblyClockEquiv hM9 B τ) v
                ((sourceSumintDatum hM9 B hG W).ℓVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v))) τ) := by
  unfold clLocalRecenteredSummand
  congr 1
  by_cases h : assemblyClockEquiv hM9 B τ ∈ clLocalTimeDomain R
      (fun v => layer (D.coreBranch hG v).toNode) t
  · have h' : τ ∈ assemblyClockEquiv hM9 B ⁻¹' clLocalTimeDomain R
        (fun v => layer (D.coreBranch hG v).toNode) t := h
    rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
    rw [sumintBoundary_gap_physical (L := L) (G.sign a.toNode) base β hβ,
      ← assembly_regionalPhase_eq_signedPhase hM9 B hG W hpar hbad hL base β hβ γ δ η x t τ,
      clLocalStarProduct_eq_weights hM9 B D hG L γ δ F layer hLayer base]
    refine congrArg (HMul.hMul _) (Finset.prod_congr rfl (fun v _ => ?_))
    rw [← assembly_pair_momentum hM9 B hG W hL base β hβ x v,
      ← assembly_branch_momentum hM9 B hG W hL base β hβ x v]
  · have h' : τ ∉ assemblyClockEquiv hM9 B ⁻¹' clLocalTimeDomain R
        (fun v => layer (D.coreBranch hG v).toNode) t := h
    rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']

end WaveTurbulence.VineEstS2
