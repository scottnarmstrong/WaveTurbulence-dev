/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.VineEst.VineSpaceK.StatementDefs
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ModStatement
public import WaveTurbulence.Foundations.Cut2A.SpatialMeasure
/-! Literal V5 member and class kernels with a spatial multiplier inside each lattice sum. -/
@[expose] public section
noncomputable section
namespace WaveTurbulence.VineSpaceK
open MeasureTheory VineEstS5C VineEstS5C.Cont VineEstS4 LFTwist RegRed Reg.Skeleton
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem memberMX_one (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (lam t0 t1 t2 : ℝ) (e f g h : Mom d) :
    memberMX D hG R L γ δ F layer hLayer base lam (fun _ => 1) t0 t1 t2 e f g h =
      clLocalKernelModC D hG R L γ δ F layer hLayer base lam t0 t1 t2 e f g h := by
  simp only [memberMX, one_mul, clLocalKernelModC]

theorem twistedRecenteredModCX_one {ι : Type*} (G : Garden w) (a : GBranch G.tree)
    (Z : Finset (ClassMember w ι)) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d)
    (lam t0 t1 t2 : ℝ) (e f g h : Mom d) :
    twistedRecenteredModCX G a Z (fun _ _ => 1) L γ δ F base lam t0 t1 t2 e f g h =
      twistedRecenteredModC G a Z L γ δ F base lam t0 t1 t2 e f g h := by
  simp only [twistedRecenteredModCX, memberMX_one, twistedRecenteredModC]
end WaveTurbulence.VineSpaceK
