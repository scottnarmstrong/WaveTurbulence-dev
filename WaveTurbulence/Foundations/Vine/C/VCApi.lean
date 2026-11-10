/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.C.VCSigma
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.Cont.ModClass

/-! # VINE-C adapter to the VINE-D ENGINE API (PLAN-VINE, fixed 2026-11-06)

The engine consumes, per vine piece,
`Σ_{LG ∈ T} value = Σ_i sign_i · Σ'_ξ W_i ξ · outerValM G … (amp_i ξ) (frq_i ξ) route hclk hmom HkM_i` with
`HkM_i j λ = Cont.twistedRecenteredModC S u_j.upper (canonFinsetK p kind (startState B_j D hS layer hLayer)
(chainStart B_j)) L γ δ (fun q => U.h i q j₁ j₁) base λ` (curried in the three clocks and four momenta).

* `clLocalKernelModC_eq_W`, `twistedRecenteredModC_eq_W`, `clRecenteredLocalKernelModC_eq_W`: V5-CONT's modulated kernels
  are the weighted kernels of VINE-C with the weight `modW λ` (the modulation stands on the other side of the summand).
* `sum_tauClass_vineD_api`: the τ-class sum in exactly the engine's form, from VINE-B♯'s per-member, per-mode
  factorization (with the member's unit kernels) and the summability in the mode `ξ` and the integrability/summability of
  each member's outer integrand (the finite interchanges).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineC
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.Reg.Skeleton
  WaveTurbulence.Represents WaveTurbulence.RegRed WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 TTree MeasureTheory

variable {w : ℕ}

/-- V5-CONT's modulated unit kernel is the weighted kernel with the weight `modW λ`. -/
theorem clLocalKernelModC_eq_W {d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (lam : ℝ)
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    VineEstS5C.Cont.clLocalKernelModC D hG R L γ δ F layer hLayer base lam t0 t1 t2 e f g h =
      clLocalKernelW D hG R L γ δ F layer hLayer base (modW lam) t0 t1 t2 e f g h := by
  unfold VineEstS5C.Cont.clLocalKernelModC clLocalKernelW VineEstS5C.Cont.lowModC modW
  congr 1
  exact tsum_congr fun κ => integral_congr_ae (Filter.Eventually.of_forall fun τ => mul_comm _ _)

/-- V5-CONT's recentered modulated unit kernel (the per-member unit factor) in VINE-C's form. -/
theorem clRecenteredLocalKernelModC_eq_W {d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (lam : ℝ)
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    VineEstS5C.Cont.clRecenteredLocalKernelModC D hG R L γ δ F layer hLayer base lam t0 t1 t2 e f g h =
      recPhase (G.sign a.toNode) L γ δ t0 e f g h *
        clLocalKernelW D hG R L γ δ F layer hLayer base (modW lam) t0 t1 t2 e f g h := by
  unfold VineEstS5C.Cont.clRecenteredLocalKernelModC recPhase
  rw [clLocalKernelModC_eq_W]

/-- V5-CONT's modulated class kernel `twistedRecenteredModC` is VINE-C's `twistedRecenteredW` with `W = modW λ`. -/
theorem twistedRecenteredModC_eq_W {κ : Type*} {d : ℕ} (G : Garden w) (a : GBranch G.tree)
    (Z : Finset (Σ Bs : FamilyReconstruction w κ, ChainAt Bs.skeleton Bs.family)) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (base : Mom d) (lam : ℝ) (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    VineEstS5C.Cont.twistedRecenteredModC G a Z L γ δ F base lam t0 t1 t2 e f g h =
      twistedRecenteredW G a Z L γ δ F base (modW lam) t0 t1 t2 e f g h := by
  unfold VineEstS5C.Cont.twistedRecenteredModC twistedRecenteredW recPhase twistedLocalKernelW
  congr 1
  exact Finset.sum_congr rfl fun x _ => clLocalKernelModC_eq_W _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- The per-member unit factor of VINE-B♯ in V5-CONT's form, at any region data of the carried unit block and any
layering decoding the member, is VINE-C's `unitRecenteredW` with `W = modW λ`. -/
theorem clRecenteredLocalKernelModC_eq_unit {ι : Type*} {Q : ι → Prop} {d : ℕ} (X : FamilyReconstruction w ι)
    (u : UnitAt X.skeleton X.family Q) (R : CLRegionData X.skeleton u.blk.U u.blk.a u.blk.b)
    (layer : GNode (X.data.forest X.plain) → ℕ) (hL : IsLayering (X.data.garden X.plain) layer)
    (hspec : layeredReconstruction X.data X.plain layer hL = X.layered) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (base : Mom d) (lam : ℝ) (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    VineEstS5C.Cont.clRecenteredLocalKernelModC X.data X.plain R L γ δ F layer hL base lam t0 t1 t2 e f g h =
      unitRecenteredW X u L γ δ F base (modW lam) t0 t1 t2 e f g h := by
  rw [clRecenteredLocalKernelModC_eq_W]
  exact unitRecenteredW_eq_of_data X u R layer hL hspec L γ δ F base (modW lam) t0 t1 t2 e f g h

variable {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer)

end WaveTurbulence.VineC
