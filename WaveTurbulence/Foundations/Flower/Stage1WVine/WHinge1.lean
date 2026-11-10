/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WVine.WAlign1
public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.Core1
public import WaveTurbulence.Foundations.Flower.V5W.ContClass
public import WaveTurbulence.Foundations.Flower.V5W.Foreign
public import WaveTurbulence.Foundations.Stage1.Represents.RepVD15

/-! # STAGE1W-VINE (T6, part 1): the weighted unit class kernels and their hinge data

* `unitHkFW`: the weighted class kernel of a unit, `twistedRecenteredFW p (g j₁) none … (modW λ)` (S-V5W §1, `S = none`),
  the weighted analogue of main's `unitHk`.
* `unitHkFW_hind`: it does not depend on the clocks of lower children that are leaves in every member (main's
  `unitHk_hind`).
* `unit_vineest_boundW`: the staged **`V5FrontierClassBoundAt`** gives the X-norm bound of a unit with the weighted mass
  `unitMassFW = cψ^(9|U| + 4n₂) · topFilterMass · unitMass` (main's `unit_vineest_bound`).
* `unit_hcontW`: T5 `weightedClassContinuity` (with INC-TOP's `TopIncoherentDecayAtR`) gives `hcont` (main's
  `unit_hcont`).
* `hinge_units_constW`: main's `hinge_units_const` for the weighted kernels; the constant depends only on `(d, η)`.

Adapted from main's `Represents/{RepVN11, RepVN12, RepKC1, RepUG8, RepVC1}.lean` (see `COPIED-SHA256SUMS`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.Stage1WVine
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RepAnalytic
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed WaveTurbulence.Represents
  WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C VineParamContract WaveTurbulence.Flower.Stage1W
  WaveTurbulence.Flower.V5W
open scoped ENNReal

theorem topFilterMass_nonneg : 0 ≤ topFilterMass :=
  MeasureTheory.integral_nonneg fun _ => norm_nonneg _

/-! ## Leaf independence -/

section Congr
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem clLocalKernelFW_congr_t (pw : ℕ) (g : Mom d → ℂ) (D : ReconstructionData G) (hG : G.IsPlain)
    (R : CLRegionData G U a b) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (m : (GNode G.tree → Fin d → ℤ) → ℂ) (W : ℝ → ℂ)
    (tU tP tN tP' tN' : ℝ) (e f g' h : Mom d)
    (hp : (b.child R.positive).1.2 ∉ (G.tree (b.child R.positive).1.1).branching ∨ tP = tP')
    (hn : (b.child R.negative).1.2 ∉ (G.tree (b.child R.negative).1.1).branching ∨ tN = tN') :
    clLocalKernelFW pw g D hG R L γ δ F layer hLayer base m W tU tP tN e f g' h =
      clLocalKernelFW pw g D hG R L γ δ F layer hLayer base m W tU tP' tN' e f g' h := by
  unfold clLocalKernelFW
  congr 1
  refine tsum_congr fun κ => MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  have h0 : ![tU, tP, tN] 0 = ![tU, tP', tN'] 0 := rfl
  have e1 := clLocalClock_congr R ![tU, tP, tN] ![tU, tP', tN'] h0 hp hn τ
  have e2 := clLocalSummandFW_congr pw g D hG R L γ δ F layer hLayer base ![e, f, g', h] ![tU, tP, tN]
    ![tU, tP', tN'] rfl hp hn κ τ
  simp only [e1, e2]

end Congr

section Hind
variable {w : ℕ} {ι : Type*} [Fintype ι]

end Hind

/-! ## The unit bound from the staged `V5FrontierClassBoundAt`, and continuity from T5 -/

end WaveTurbulence.Flower.Stage1WVine
