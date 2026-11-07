/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLLocalFactors
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLPhaseRecentering

/-! # TARGET regred: the actual seven-argument CL-local kernel construction -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton MeasureTheory

/-- The literal source local summand: upper joint included in epsilon and
phase, excluded from order, zeta, integrated clocks and regular-tree products. -/
noncomputable def clLocalSummand {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (boundary : Fin 4 → Mom d)
    (t : Fin 3 → ℝ) (κ : CLLocalDecoration R L base boundary) (τ : CLInternalTime R) : ℂ :=
  (clRegionalEpsilon G U (clExtendIndices R κ.1) : ℂ) *
    (clLocalTimeDomain R (fun v => layer (D.coreBranch hG v).toNode) t).indicator
      (fun τ => clRegionalPhase G U L γ δ (cosetDecoration G L base (clExtendIndices R κ.1))
          (clLocalClock R t τ) *
        clLocalStarProduct D hG R L γ δ F layer hLayer base (clExtendIndices R κ.1) t τ) τ

/-- TARGET regred L1733–1740: K^U_(G), with exactly three exterior clocks and
four exterior momenta. The lattice coset base is fixed standing data. If a lower
boundary child is a leaf, its unused clock is a dummy argument; only actual tree
edge inequalities are imposed. This construction covers all current CL blocks,
including the F72 m=1 vine-II shape, without a width cutoff. -/
noncomputable def clLocalKernel {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
    (tUpper tPositive tNegative : ℝ) (e f g h : Mom d) : ℂ :=
  (coupling d L γ δ : ℂ)^clLocalOrder1 R * clLocalZeta R *
    ∑' κ : CLLocalDecoration R L base ![e,f,g,h],
      ∫ τ : CLInternalTime R,
        clLocalSummand D hG R L γ δ F layer hLayer base ![e,f,g,h] ![tUpper,tPositive,tNegative] κ τ

/-- The single-garden recentered expression at the beginning of vineest Step 1.
The LF-twist family itself is the separate M7 construction. -/
noncomputable def clRecenteredLocalKernel {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
    (tUpper tPositive tNegative : ℝ) (e f g h : Mom d) : ℂ :=
  Complex.exp (((-(Real.pi*δ*L^(2*γ))*tUpper*boundaryEnergyFromMomenta (G.sign a.toNode) e f g h : ℝ) : ℂ)*Complex.I) *
    clLocalKernel D hG R L γ δ F layer hLayer base tUpper tPositive tNegative e f g h

end WaveTurbulence.RegRed
