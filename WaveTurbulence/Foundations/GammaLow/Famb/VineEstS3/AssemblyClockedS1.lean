/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.ClockSlots
public import WaveTurbulence.Foundations.VineEst.VineEstS3.ClockedExpr
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS3.AssemblyClocked
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.AssemblyClocked
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLStep2TimeS1
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS3.AssemblyClocked` (sha256 fe00cf1d6dbcd7dc…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # B4: the clock-dependent rows of the vine-chain assembly (V5)

`assemblyClocked` is the `ClockedRows` of `sourceSumintDatum hM9 B hG W` whose weights are the starred kernels
`K_Q^*` (rows `inl v`) and `K_T^*` (rows `inr v`) of V4, as functions of the clock pair
`(parentClock of the first leaf, parentClock of the second leaf)` resp. `(parentClock of the branch, its clock)`.
The slots come from `node_parent_slot` and `branch_clock_slot`.  `clockedIntegrand_assembly` identifies the
integrand of `clockedExpr` with the integrand of V4's endpoint `vineChain_eq_sumintForm`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS3
open WaveTurbulence.VineEstS3
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3.Eng VineParamContract TTree Reg WaveTurbulence.GammaLow.Famb.VineEstS2
  Reg.Skeleton RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The integrand of `clockedExpr` for `assemblyClockedS` is the integrand of V4's endpoint. -/
theorem clockedIntegrand_assemblyΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
    (cfs cs : Fin (assemblyShapeΓ hM9 B).I → ℤˣ) (γ' δ' η : ℝ) (x : (assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ))
    (E : Fin 4 → Mom d) (t : Fin 3 → ℝ) (τ : (assemblyShapeΓ hM9 B).TVar → ℝ) :
    clockedIntegrand (assemblyClockedSΓ hM9 B RD hG W L γ δ F layer hLayer) cfs cs L γ' δ' η x E t τ =
      signedPhase (sourceSumintDatumΓ hM9 B hG W) cfs cs L γ' δ' η x (E 0 - E 1) (t 0) τ *
        ∏ v, (assemblyWKΓ hM9 B RD hG L γ δ F layer hLayer t (assemblyClockEquivΓ hM9 B τ) v
            ((sourceSumintDatumΓ hM9 B hG W).kVec L x E v) *
          assemblyWLΓ hM9 B RD hG L γ δ F layer hLayer t (assemblyClockEquivΓ hM9 B τ) v
            ((sourceSumintDatumΓ hM9 B hG W).ℓVec L x E v)) := by
  unfold clockedIntegrand
  congr 1
  rw [Fintype.prod_sum_type, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hp := pairLeaf_ne (a := a) hG (assemblyPairOfΓ hM9 B hG v)
  have h1 := nodeSlot_specΓ hM9 B _ (clRegionalPair_realization hG _ (assemblyPairOfΓ hM9 B hG v).2).1 hp.1 t τ
  have h2 := nodeSlot_specΓ hM9 B _ (clRegionalPair_realization hG _ (assemblyPairOfΓ hM9 B hG v).2).2 hp.2 t τ
  have hbr := (branch_mem_clRealizationNodes (assemblyBranchOfΓ hM9 B v).1).mpr
    (Finset.mem_erase.mp (assemblyBranchOfΓ hM9 B v).2).2
  have h3 := nodeSlot_specΓ hM9 B _ hbr (interior_ne (assemblyBranchOfΓ hM9 B v)) t τ
  have h4 := branchSlot_specΓ hM9 B (assemblyBranchOfΓ hM9 B v) t τ
  simp only [ClockedRows.clock, assemblyClockedSΓ, rowMom, Sum.elim_inl, Sum.elim_inr, slotVal]
  unfold assemblyWKΓ assemblyWLΓ
  simp only [h1, h2, h3, h4, if_true, Fin.isValue]
  rfl

end WaveTurbulence.GammaLow.Famb.VineEstS3
