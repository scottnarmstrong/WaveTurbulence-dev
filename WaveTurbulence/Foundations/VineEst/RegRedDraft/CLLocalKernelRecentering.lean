/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLLocalKernel
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLBoundaryLocal

/-! # TARGET defKtilde: the actual recentered seven-argument CL-local kernel -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton MeasureTheory

noncomputable def clLocalRecenteredSummand {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (boundary : Fin 4 → Mom d)
    (t : Fin 3 → ℝ) (κ : CLLocalDecoration R L base boundary) (τ : CLInternalTime R) : ℂ :=
  (clRegionalEpsilon G U (clExtendIndices R κ.1) : ℂ) *
    (clLocalTimeDomain R (fun v => layer (D.coreBranch hG v).toNode) t).indicator
      (fun τ => clRegionalPhase G U L γ δ (cosetDecoration G L base (clExtendIndices R κ.1))
          (fun v => clLocalClock R t τ v-t 0) *
        clLocalStarProduct D hG R L γ δ F layer hLayer base (clExtendIndices R κ.1) t τ) τ

theorem clLocalSummand_recenter {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (hU : G.molecule.IsBlock U a b)
    (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (boundary : Fin 4 → Mom d)
    (t : Fin 3 → ℝ) (κ : CLLocalDecoration R L base boundary) (τ : CLInternalTime R) :
    Complex.exp (((-(Real.pi*δ*L^(2*γ))*t 0*
      boundaryEnergyFromMomenta (G.sign a.toNode) (boundary 0) (boundary 1) (boundary 2) (boundary 3) : ℝ) : ℂ)*Complex.I) *
        clLocalSummand D hG R L γ δ F layer hLayer base boundary t κ τ =
      clLocalRecenteredSummand D hG R L γ δ F layer hLayer base boundary t κ τ := by
  let A := clLocalTimeDomain R (fun v => layer (D.coreBranch hG v).toNode) t
  by_cases hτ : τ ∈ A
  · have hp := clLocalDecoration_phase_recenter hU R L γ δ base boundary κ (clLocalClock R t τ) (t 0)
    unfold clLocalSummand clLocalRecenteredSummand
    rw [Set.indicator_of_mem hτ,Set.indicator_of_mem hτ]
    apply Eq.trans (b := (clRegionalEpsilon G U (clExtendIndices R κ.1) : ℂ) *
      ((Complex.exp (((-(Real.pi*δ*L^(2*γ))*t 0*
        boundaryEnergyFromMomenta (G.sign a.toNode) (boundary 0) (boundary 1) (boundary 2) (boundary 3) : ℝ) : ℂ)*Complex.I) *
          clRegionalPhase G U L γ δ (cosetDecoration G L base (clExtendIndices R κ.1)) (clLocalClock R t τ)) *
        clLocalStarProduct D hG R L γ δ F layer hLayer base (clExtendIndices R κ.1) t τ))
    · ring
    · exact congrArg (fun z => (clRegionalEpsilon G U (clExtendIndices R κ.1) : ℂ) *
        (z * clLocalStarProduct D hG R L γ δ F layer hLayer base (clExtendIndices R κ.1) t τ)) hp
  · unfold clLocalSummand clLocalRecenteredSummand
    rw [Set.indicator_of_notMem hτ,Set.indicator_of_notMem hτ]
    simp only [mul_zero]

/-- TARGET vineest Step 1, defKtilde: an equality of the actual local kernel
with its recentered phase formula. The boundary-energy identity and all local
matching cancellations are proved for every summand, without an extra premise. -/
theorem clLocalKernel_recentered_formula {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (hU : G.molecule.IsBlock U a b)
    (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
    (tUpper tPositive tNegative : ℝ) (e f g h : Mom d) :
    clRecenteredLocalKernel D hG R L γ δ F layer hLayer base tUpper tPositive tNegative e f g h =
      (coupling d L γ δ : ℂ)^clLocalOrder1 R * clLocalZeta R *
        ∑' κ : CLLocalDecoration R L base ![e,f,g,h], ∫ τ : CLInternalTime R,
          clLocalRecenteredSummand D hG R L γ δ F layer hLayer base ![e,f,g,h]
            ![tUpper,tPositive,tNegative] κ τ := by
  let C := (coupling d L γ δ : ℂ)^clLocalOrder1 R * clLocalZeta R
  let E := Complex.exp (((-(Real.pi*δ*L^(2*γ))*tUpper*
    boundaryEnergyFromMomenta (G.sign a.toNode) e f g h : ℝ) : ℂ)*Complex.I)
  unfold clRecenteredLocalKernel clLocalKernel
  rw [mul_left_comm E C]
  apply congrArg (fun z => C*z)
  rw [← tsum_mul_left]
  apply tsum_congr
  intro κ
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun τ =>
    clLocalSummand_recenter hU D hG R L γ δ F layer hLayer base ![e,f,g,h]
      ![tUpper,tPositive,tNegative] κ τ))

end WaveTurbulence.RegRed
