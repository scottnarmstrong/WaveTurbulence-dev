/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.Cont.ModKernel
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Tw11Data
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Tw7Summand

/-! # FLAT-MOD (R60), kernel level 1: twist invariance of the modulated kernel

The modulation `e^{πiλτ_b}` (`Cont.lowModC`) reads only the clock of the lower joint `b`, which every twist fixes
(`clock_corr`), and does not see the data of the reconstruction.  So `K^{T,λ}` (`Cont.clLocalKernelModC`) is twist invariant
(`clLocalKernelModC_twist`, exchange of the first two boundary momenta) and depends on the data only through the native rows
(`clLocalKernelModC_congr_data`), exactly as `clLocalKernel_twist` / `clLocalKernel_congr_data` (VineEstS4).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C.FlatMod
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.Reg
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C.Cont TTree MeasureTheory

variable {w : ℕ} {G : Garden w} (P : CorePlacement G) {T : Finset (GBranch G.tree)} {z : GBranch G.tree}

theorem lowModC_twist (hB : G.molecule.IsBlock T P.lower z)
    (R : CLRegionData G T P.lower z) (R' : TwRegion P T z) (lam : ℝ) (t : Fin 3 → ℝ) (τ : CLInternalTime R) :
    lowModC R' lam t (tEquiv P R R' τ) = lowModC R lam t τ := by
  unfold lowModC
  rw [clock_corr P R R' t τ hB.2.2.1]

variable (hB : G.molecule.IsBlock T P.lower z) (hCL : Mole.CLParentPattern G T P.lower z)
  (R : CLRegionData G T P.lower z) (R' : TwRegion P T z)
variable {d : ℕ} (hG : G.IsPlain) (D : ReconstructionData G) (D' : ReconstructionData (unitTwistGarden G P))
  (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer)
  (layer' : GNode (D'.forest (unitTwistGarden_plain G P hG)) → ℕ)
  (hLayer' : IsLayering (D'.garden (unitTwistGarden_plain G P hG)) layer') (base : Mom d) (lam : ℝ) (t0 t1 t2 : ℝ)
  (e f g h : Mom d)
  (hC : ∀ p ∈ clRegionalPairs hG T, nativeCoupleLayered D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) =
      nativeCoupleLayered D hG layer hLayer p)
  (hT : ∀ v ∈ clInteriorBranches R, nativeChainLayered D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
      nativeChainLayered D hG layer hLayer v)
  (hl : ∀ v ∈ T, layer' (D'.coreBranch (unitTwistGarden_plain G P hG) (eB P v)).toNode =
      layer (D.coreBranch hG v).toNode)
  (hCi : ∀ p ∈ clRegionalPairs hG T, Flower.V5W.coupleIncoh D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) =
      Flower.V5W.coupleIncoh D hG layer hLayer p)
  (hTi : ∀ v ∈ clInteriorBranches R, Flower.V5W.treeIncoh D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
      Flower.V5W.treeIncoh D hG layer hLayer v)

include hB hCL hC hT hl hCi hTi in
/-- **K^{T,λ} twist invariance** (modulated `clLocalKernel_twist`). -/
theorem clLocalKernelModC_twist :
    clLocalKernelModC D' (unitTwistGarden_plain G P hG) R' L γ δ F layer' hLayer' base lam t0 t1 t2 e f g h =
      clLocalKernelModC D hG R L γ δ F layer hLayer base lam t0 t1 t2 f e g h := by
  unfold clLocalKernelModC
  rw [order1_twist P R R', zeta_twist P R R']
  congr 1
  have hint : ∀ κ' : CLLocalDecoration R' L base ![e, f, g, h],
      ∫ τ' : CLInternalTime R', lowModC R' lam ![t0, t1, t2] τ' *
          clLocalSummand D' (unitTwistGarden_plain G P hG) R' L γ δ F layer' hLayer' base
          ![e, f, g, h] ![t0, t1, t2] κ' τ' =
        ∫ τ : CLInternalTime R, lowModC R lam ![t0, t1, t2] τ *
          clLocalSummand D hG R L γ δ F layer hLayer base ![f, e, g, h] ![t0, t1, t2]
          (decEquiv P hB hCL R R' L base e f g h κ') τ := by
    intro κ'
    rw [← (tEquiv_measurePreserving P R R').integral_comp' (g := fun τ' => lowModC R' lam ![t0, t1, t2] τ' *
      clLocalSummand D' _ R' L γ δ F layer' hLayer' base ![e, f, g, h] ![t0, t1, t2] κ' τ')]
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    beta_reduce
    rw [lowModC_twist P hB R R' lam _ τ]
    exact congrArg (fun y => lowModC R lam ![t0, t1, t2] τ * y)
      (summand_twist P hB hCL R R' hG D D' L γ δ F layer hLayer layer' hLayer' base e f g h hC hT hl hCi hTi _ κ' τ)
  rw [tsum_congr hint]
  exact (decEquiv P hB hCL R R' L base e f g h).tsum_eq
    (fun κ => ∫ τ : CLInternalTime R, lowModC R lam ![t0, t1, t2] τ *
      clLocalSummand D hG R L γ δ F layer hLayer base ![f, e, g, h] ![t0, t1, t2] κ τ)

end WaveTurbulence.VineEstS5C.FlatMod
