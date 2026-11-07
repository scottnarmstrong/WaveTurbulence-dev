/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLGlobalPhase

/-! # TARGET Step 2: the actual regional kernel in sumint coordinates

The regional kernel equals `coupling^{n₁} ζ ∑ₓ ∫_τ` of the source sign factor `ε` times the
indicator of the source clock domain times `signedPhase` of the source sumint datum (vanishing
weight parameters) times the native starred-kernel product, all in the exact frozen sumint
lattice and clock coordinates. Weight extraction and the bad-case alternatives are Step 3. -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- Typing data with vanishing parameters and no bad kind: the exact phase-bearing fields
of `SumintDatum` that enter `signedPhase` are then fixed by the source. -/
noncomputable def phaseOnlyWeightData (S : SumintShape) (d : ℕ) : SumintWeightClockData S d where
  wK := fun _ _ => 1
  wL := fun _ _ => 1
  g := fun _ => 0
  g' := fun _ => 0
  param := fun _ => 0
  q := fun _ => 0
  constraints := ∅
  badKind := fun _ => 0
  qOut := fun _ => 0
  centre := fun _ => 0
  wBar := 0

theorem clLocalRecenteredSummand_signed (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (D : ReconstructionData G) (hG : G.IsPlain) {L : ℝ} (hL : L ≠ 0) (γ δ η : ℝ)
    (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3)
    (x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ)) (t : Fin 3 → ℝ)
    (τ : (assemblyShape hM9 B).TVar → ℝ) :
    clLocalRecenteredSummand D hG R L γ δ F layer hLayer base (fun j => base+latticePoint L (β j)) t
        ((clNormalizedChainEquiv hL B base β hβ hM9).symm x) (assemblyClockEquiv hM9 B τ) =
      (clRegionalEpsilon G U (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) : ℂ) *
        ((assemblyClockEquiv hM9 B ⁻¹' clLocalTimeDomain R
            (fun v => layer (D.coreBranch hG v).toNode) t).indicator
          (fun τ => signedPhase (sourceSumintDatum hM9 B hG (phaseOnlyWeightData (assemblyShape hM9 B) d))
              (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) L γ (2*δ) η x
              (-(latticePoint L (β 2-β 3))) (t 0) τ *
            clLocalStarProduct D hG R L γ δ F layer hLayer base
              (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) t
              (assemblyClockEquiv hM9 B τ)) τ) := by
  unfold clLocalRecenteredSummand
  congr 1
  by_cases h : assemblyClockEquiv hM9 B τ ∈ clLocalTimeDomain R
      (fun v => layer (D.coreBranch hG v).toNode) t
  · have h' : τ ∈ assemblyClockEquiv hM9 B ⁻¹' clLocalTimeDomain R
        (fun v => layer (D.coreBranch hG v).toNode) t := h
    rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
    rw [← assembly_regionalPhase_eq_signedPhase hM9 B hG (phaseOnlyWeightData (assemblyShape hM9 B) d)
      (fun _ => rfl) (fun _ => by simp [phaseOnlyWeightData]) hL base β hβ γ δ η x t τ]
  · have h' : τ ∉ assemblyClockEquiv hM9 B ⁻¹' clLocalTimeDomain R
        (fun v => layer (D.coreBranch hG v).toNode) t := h
    rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']

/-- TARGET vineest Step 2: the actual recentered regional kernel as a sum over the frozen
sumint lattice and an integral over the frozen sumint clocks of the source sign factor times
the source clock-domain indicator times `signedPhase` times the native starred-kernel product. -/
theorem clLocalKernel_step2 {L : ℝ} (hL : L ≠ 0)
    (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (D : ReconstructionData G) (hG : G.IsPlain)
    (γ δ η : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3) (t : Fin 3 → ℝ) :
    clRecenteredLocalKernel D hG R L γ δ F layer hLayer base (t 0) (t 1) (t 2)
      (base+latticePoint L (β 0)) (base+latticePoint L (β 1))
      (base+latticePoint L (β 2)) (base+latticePoint L (β 3)) =
    (coupling d L γ δ : ℂ)^clLocalOrder1 R * clLocalZeta R *
      ∑' x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ), ∫ τ : (assemblyShape hM9 B).TVar → ℝ,
        (clRegionalEpsilon G U (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) : ℂ) *
        ((assemblyClockEquiv hM9 B ⁻¹' clLocalTimeDomain R
            (fun v => layer (D.coreBranch hG v).toNode) t).indicator
          (fun τ => signedPhase (sourceSumintDatum hM9 B hG (phaseOnlyWeightData (assemblyShape hM9 B) d))
              (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) L γ (2*δ) η x
              (-(latticePoint L (β 2-β 3))) (t 0) τ *
            clLocalStarProduct D hG R L γ δ F layer hLayer base
              (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) t
              (assemblyClockEquiv hM9 B τ)) τ) := by
  rw [clLocalKernel_reindexed hL hM9 B D hG γ δ F layer hLayer base β hβ t]
  congr 1
  refine tsum_congr (fun x => ?_)
  exact integral_congr_ae (Filter.Eventually.of_forall (fun τ =>
    clLocalRecenteredSummand_signed hM9 B D hG hL γ δ η F layer hLayer base β hβ x t τ))

end WaveTurbulence.VineEstS2
