/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5W2L.Defs
public import WaveTurbulence.Foundations.Flower.V5WT.FlatT

/-! # V5W-2L: the class identity with a product of top filters

`twistedRecenteredFWL_eq`: the pinned class kernel with the product filter `topFilterWeightL S` is the selector class
`twistedRecenteredModCX` at `selW p g cψ` with every member's top-weighted weight
`V5WT.bWT (wdOf p g cψ) (topFilterWeightL S)`.

V5W-T's class identity (`V5WT.classSumBT_eq_flat`, `V5WT.twistedRecenteredModCX_bondT_eq_flatFn`) already takes an
arbitrary top weight `W` with `‖W‖ ≤ CW`; only its entry bridge (`V5WT.twistedRecenteredFW_eq`, stated at
`topFilterWeight S`) is re-proved here at `topFilterWeightL S`.  Copied by source from V5W-T `Flower/V5WT/FlatT.lean`
section `BridgeT` (sha256 in `COPIED-SHA256SUMS`), with `S : List ℝ` and the `…L` kernels.
-/

@[expose] public section
noncomputable section
namespace WaveTurbulence.Flower.V5W2L
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.Flower.V5WT (bWT)

section BridgeL
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS4 Links
open WaveTurbulence.VineSpaceK (ClassMember nodeWeight)
open WaveTurbulence.Flower.V5W (nodeRowIncoh regionWeightFW stateCoreLayer topFilterWeight clLocalKernelFW
  clLocalSummandFW clLocalStarProductFW)
variable {w d : ℕ} {ι : Type*}

/-- The region multiplier with a product of top filters is V5W-0's at `S = none` times the product filter at the
top. -/
theorem regionWeightFWL_eq_none_mul (p : ℕ) (g : Mom d → ℂ) (S : List ℝ) (L : ℝ) (base : Mom d)
    (X : FamilyReconstruction w ι) (U : Finset (GBranch X.skeleton.tree)) (a : GBranch X.skeleton.tree)
    (x : GNode X.skeleton.tree → Fin d → ℤ) :
    regionWeightFWL p g S L base X U a x =
      regionWeightFW p g none L base X U a x * nodeWeight (topFilterWeightL S) L base a x := by
  have h1 : nodeWeight (topFilterWeight (none : Option ℝ)) L base a x = 1 := by
    simp [nodeWeight, topFilterWeight]
  unfold regionWeightFWL regionWeightFW
  rw [h1, mul_one]

/-- **The top-weighted masked, normalized bond weight is the multiplier at `S` times the row normalization.** -/
theorem bWT_eq_regionWeightFWL (p : ℕ) (g : Mom d → ℂ) {cψ : ℝ} (hc : 0 ≤ cψ) (S : List ℝ) (κ : KPar d)
    (X : FamilyReconstruction w ι) (c : ChainAt X.skeleton X.family) (x : GNode X.skeleton.tree → Fin d → ℤ) :
    bWT (wdOf p g cψ) (topFilterWeightL S) κ X c.U c.a x =
      regionWeightFWL p g S κ.L κ.base X c.U c.a x *
        (rowNorm cψ X.data X.plain (clRegionData X.skeleton c.block c.cl) (stateLayer X)
          (stateLayer_isLayering X) : ℂ) := by
  unfold bWT
  rw [bWN_eq_regionWeightFW p g hc κ X c x, regionWeightFWL_eq_none_mul p g S κ.L κ.base X c.U c.a x]
  ring

variable {rowSelU : Unit} [rowSel : VineEst.RowSel rowSelU]

/-- **The member kernel**: the member kernel with a product of top filters is the selector member kernel with
`bWT`. -/
theorem twistedLocalKernelFWL_eq (p : ℕ) (g : Mom d → ℂ) (cψ : ℝ) (h1 : 1 ≤ cψ) (hg : ∀ x, ‖g x‖ ≤ cψ)
    (hr : ∀ x, (g x).im = 0) (S : List ℝ) (X : FamilyReconstruction w ι) (c : ChainAt X.skeleton X.family)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (lam t0 t1 t2 : ℝ) (e f g' h : Mom d) :
    twistedLocalKernelFWL p g S X c L γ δ F base (VineC.modW lam) t0 t1 t2 e f g' h =
      memberMX (rowSel := selW p g cψ h1 hg hr) X.data X.plain (clRegionData X.skeleton c.block c.cl) L γ δ F
        (stateLayer X) (stateLayer_isLayering X) base lam
        (bWT (wdOf p g cψ) (topFilterWeightL S) (VineEstS5C.P4.kparOf L γ δ F base) X c.U c.a)
        t0 t1 t2 e f g' h := by
  have hc : 0 ≤ cψ := by linarith
  unfold twistedLocalKernelFWL clLocalKernelFW memberMX
  refine congrArg (HMul.hMul _) (tsum_congr fun κ => MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun τ => ?_))
  beta_reduce
  rw [bWT_eq_regionWeightFWL p g hc S, clLocalSummandFW_eq p g cψ h1 hg hr]
  unfold VineEstS5C.Cont.lowModC VineC.modW
  have hk1 : (VineEstS5C.P4.kparOf L γ δ F base).L = L := rfl
  have hk2 : (VineEstS5C.P4.kparOf L γ δ F base).base = base := rfl
  rw [hk1, hk2]
  ring

/-- **The class kernel**: the pinned class kernel with a product of top filters is the selector class
`twistedRecenteredModCX` at `selW` with every member's top-weighted weight `bWT … (topFilterWeightL S)`. -/
theorem twistedRecenteredFWL_eq (p : ℕ) (g : Mom d → ℂ) (cψ : ℝ) (h1 : 1 ≤ cψ) (hg : ∀ x, ‖g x‖ ≤ cψ)
    (hr : ∀ x, (g x).im = 0) (S : List ℝ) (G : Garden w) (a : GBranch G.tree) (Z : Finset (ClassMember w ι))
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (lam t0 t1 t2 : ℝ) (e f g' h : Mom d) :
    twistedRecenteredFWL p g S G a Z L γ δ F base (VineC.modW lam) t0 t1 t2 e f g' h =
      twistedRecenteredModCX (rowSel := selW p g cψ h1 hg hr) G a Z
        (fun z => bWT (wdOf p g cψ) (topFilterWeightL S) (VineEstS5C.P4.kparOf L γ δ F base) z.1 z.2.U z.2.a)
        L γ δ F base lam t0 t1 t2 e f g' h := by
  unfold twistedRecenteredFWL twistedRecenteredModCX VineC.recPhase
  refine congrArg (HMul.hMul _) ?_
  exact Finset.sum_congr rfl fun z _ => twistedLocalKernelFWL_eq p g cψ h1 hg hr S z.1 z.2 L γ δ F base lam
    t0 t1 t2 e f g' h

end BridgeL

end WaveTurbulence.Flower.V5W2L
