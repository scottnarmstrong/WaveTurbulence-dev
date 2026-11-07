/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp11Lin

/-! # `SOK` for the lower kernel (V5 Step 4b, step 4, WP-E, part 2)

`sok_KT`: for a split `S ∪ T` with absolutely summable inputs (`HF`), the integrand of the S-side with the lower factor `K^T`
is integrable in the times of `S` for each `xS`, and its `L¹` norms are summable in `xS` (from `absConv_of_inputs`, `fubini_one`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w d : ℕ} {G : Garden w} {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}

section Sok
variable (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c) (hi : S ∩ T = {b})
  (hU : G.molecule.IsBlock (S ∪ T) a c) (RU : CLRegionData G (S ∪ T) a c) (RS : CLRegionData G S a b)
  (RT : CLRegionData G T b c) (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
  (t0 t1 t2 : ℝ) (e f g h : Mom d)

include hS hT hi hU RU in
theorem sok_KT (hL : L ≠ 0) (hF : HF D hG L F layer base) :
    SOK RS D hG L γ δ F layer hLayer base t0 t1 t2 e f (clBoundaryNodes RT 0) (clBoundaryNodes RT 1)
      (fun t E F' => clLocalKernel D hG RT L γ δ F layer hLayer base t t1 t2 E F' g h) := by
  obtain ⟨hint, hsum⟩ := absConv_of_inputs hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h hL hF
  have hone := fun p => fubini_one hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h p (hint p)
  have hsP : Summable (fun p => ∫ σ, ‖PhiS RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h p σ‖) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) (fun p => (hone p).2.2) hsum
  set CT : ℂ := (coupling d L γ δ : ℂ) ^ clLocalOrder1 RT * clLocalZeta RT with hCT
  have hK : ∀ (xS : ExtS RS L base e f) (σ : CLInternalTime RS),
      sInt RS D hG L γ δ F layer hLayer base t0 t1 t2 e f (clBoundaryNodes RT 0) (clBoundaryNodes RT 1)
        (fun t E F' => clLocalKernel D hG RT L γ δ F layer hLayer base t t1 t2 E F' g h) xS σ =
      CT * ∑' κ : CLLocalDecoration RT L base (bdT RT L base xS.1 g h),
        PhiS RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h ⟨xS, κ⟩ σ := by
    intro xS σ
    unfold sInt
    beta_reduce
    rw [clLocalKernel_eq_vec]
    unfold clLocalKernelVec
    simp only [PhiS, JT, bdT]
    rw [tsum_mul_left, hCT]
    ring
  refine ⟨fun xS => ?_, ?_⟩
  · have : sInt RS D hG L γ δ F layer hLayer base t0 t1 t2 e f (clBoundaryNodes RT 0) (clBoundaryNodes RT 1)
        (fun t E F' => clLocalKernel D hG RT L γ δ F layer hLayer base t t1 t2 E F' g h) xS =
        fun σ => CT * ∑' κ : CLLocalDecoration RT L base (bdT RT L base xS.1 g h),
          PhiS RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h ⟨xS, κ⟩ σ := funext (hK xS)
    rw [this]
    exact (integrable_tsum_of_summable_integral_norm (fun κ => (hone ⟨xS, κ⟩).1) (hsP.sigma_factor xS)).const_mul CT
  · have hb : ∀ xS : ExtS RS L base e f,
        ∫ σ, ‖sInt RS D hG L γ δ F layer hLayer base t0 t1 t2 e f (clBoundaryNodes RT 0) (clBoundaryNodes RT 1)
          (fun t E F' => clLocalKernel D hG RT L γ δ F layer hLayer base t t1 t2 E F' g h) xS σ‖ ≤
          ‖CT‖ * ∑' κ : CLLocalDecoration RT L base (bdT RT L base xS.1 g h),
            ∫ σ, ‖PhiS RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h ⟨xS, κ⟩ σ‖ := by
      intro xS
      have h1 : ∀ σ, ‖sInt RS D hG L γ δ F layer hLayer base t0 t1 t2 e f (clBoundaryNodes RT 0) (clBoundaryNodes RT 1)
          (fun t E F' => clLocalKernel D hG RT L γ δ F layer hLayer base t t1 t2 E F' g h) xS σ‖ =
          ‖CT‖ * ‖∑' κ : CLLocalDecoration RT L base (bdT RT L base xS.1 g h),
            PhiS RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h ⟨xS, κ⟩ σ‖ := by
        intro σ; rw [hK xS σ, norm_mul]
      simp_rw [h1]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (integral_norm_tsum_le (fun κ => (hone ⟨xS, κ⟩).1) (hsP.sigma_factor xS))
        (norm_nonneg _)
    exact Summable.of_nonneg_of_le (fun xS => integral_nonneg (fun _ => norm_nonneg _)) hb (hsP.sigma.mul_left ‖CT‖)

end Sok

end WaveTurbulence.VineEstS4
