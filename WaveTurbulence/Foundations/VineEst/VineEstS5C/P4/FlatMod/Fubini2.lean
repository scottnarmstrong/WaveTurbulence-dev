/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.Fubini

/-! # FLAT-MOD (R60), kernel level 4: `K^{U,λ}` is the S-side with the lower factor `K^{T,λ}`

`clLocalKernelModC_split_sigma`, `clLocalKernelModC_split_fubini`, **`clLocalKernelModC_split_KT`** (modulated
`VineEstS4.clLocalKernel_split_KT`) and `sok_KTM` (modulated `sok_KT`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C.FlatMod
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5C.Cont TTree MeasureTheory

variable {w d : ℕ} {G : Garden w} {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}

section Fubini
variable (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c) (hi : S ∩ T = {b})
  (hU : G.molecule.IsBlock (S ∪ T) a c) (RU : CLRegionData G (S ∪ T) a c) (RS : CLRegionData G S a b)
  (RT : CLRegionData G T b c) (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (lam : ℝ)
  (t0 t1 t2 : ℝ) (e f g h : Mom d)

/-- The modulated time-`b` kernel integrand of `T`, integrated over the times of `T`. -/
noncomputable def JTM
    (p : Σ xS : ExtS RS L base e f, CLLocalDecoration RT L base (bdT RT L base xS.1 g h)) (u : ℝ) : ℂ :=
  ∫ ρ : CLInternalTime RT, lowModC RT lam ![u, t1, t2] ρ *
    clLocalSummand D hG RT L γ δ F layer hLayer base (bdT RT L base p.1.1 g h) ![u, t1, t2] p.2 ρ

/-- The separated modulated integrand over the times of `S`. -/
noncomputable def PhiSM
    (p : Σ xS : ExtS RS L base e f, CLLocalDecoration RT L base (bdT RT L base xS.1 g h))
    (σ : CLInternalTime RS) : ℂ :=
  spart D hG L γ δ F layer hLayer base S a b p.1.1 (clLocalClock RS ![t0, t1, t2] σ) *
    JTM RS RT D hG L γ δ F layer hLayer base lam t1 t2 e f g h p (clLocalClock RS ![t0, t1, t2] σ b)

include hS hT hi hU in
/-- Fubini for one modulated glued summand. -/
theorem fubini_oneM
    (p : Σ xS : ExtS RS L base e f, CLLocalDecoration RT L base (bdT RT L base xS.1 g h))
    (hp : Integrable (fUM hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h p)) :
    Integrable (PhiSM RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h p) ∧
      ∫ τ, fUM hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h p τ =
        ∫ σ, PhiSM RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h p σ ∧
      ∫ σ, ‖PhiSM RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h p σ‖ ≤
        ∫ τ, ‖fUM hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h p τ‖ := by
  obtain ⟨E, hE, hf⟩ := exists_prodFormM hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h
  set f' := fUM hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h p with hf'
  have hg : Integrable (f' ∘ E) := (hE.integrable_comp_emb E.measurableEmbedding).mpr hp
  have hrow : ∀ σ, ∫ ρ, (f' ∘ E) (σ, ρ) = PhiSM RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h p σ := by
    intro σ
    simp only [Function.comp, hf', hf p σ]
    unfold PhiSM JTM
    rw [integral_const_mul]
  have h1 : Integrable (PhiSM RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h p) := by
    have := hg.integral_prod_left
    simpa only [hrow] using this
  refine ⟨h1, ?_, ?_⟩
  · rw [← hE.integral_comp' f']
    change ∫ z, (f' ∘ E) z = _
    exact (integral_prod _ hg).trans (integral_congr_ae (Filter.Eventually.of_forall hrow))
  · have hn : Integrable (fun σ => ∫ ρ, ‖(f' ∘ E) (σ, ρ)‖) := hg.norm.integral_prod_left
    calc ∫ σ, ‖PhiSM RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h p σ‖
        ≤ ∫ σ, ∫ ρ, ‖(f' ∘ E) (σ, ρ)‖ := by
          refine integral_mono h1.norm hn (fun σ => ?_)
          rw [← hrow σ]
          exact norm_integral_le_integral_norm _
      _ = ∫ z, ‖(f' ∘ E) z‖ := (integral_prod _ hg.norm).symm
      _ = ∫ τ, ‖f' τ‖ := hE.integral_comp' (fun τ => ‖f' τ‖)

include hS hT hi hU in
/-- The sigma form of the splitting of `K^{U,λ}` at `b`. -/
theorem clLocalKernelModC_split_sigma (hL : L ≠ 0) :
    clLocalKernelModC D hG RU L γ δ F layer hLayer base lam t0 t1 t2 e f g h =
      (coupling d L γ δ : ℂ) ^ clLocalOrder1 RU * clLocalZeta RU *
        ∑' p : Σ xS : ExtS RS L base e f, CLLocalDecoration RT L base (bdT RT L base xS.1 g h),
          ∫ τ : CLInternalTime RU, fUM hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h p τ := by
  unfold clLocalKernelModC
  congr 1
  rw [← (splitLocalEquiv hS hT hi hU RU RS RT hL base ![e, f, g, h]).symm.tsum_eq]
  refine tsum_congr (fun p => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall (fun τ => ?_))
  unfold fUM
  rw [fU_eq hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h hL p τ]

include hS hT hi hU in
/-- **Fubini form** (modulated `clLocalKernel_split_fubini`). -/
theorem clLocalKernelModC_split_fubini (hL : L ≠ 0)
    (hA : AbsConvM hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h) :
    clLocalKernelModC D hG RU L γ δ F layer hLayer base lam t0 t1 t2 e f g h =
      (coupling d L γ δ : ℂ) ^ clLocalOrder1 RU * clLocalZeta RU *
        ∑' xS : ExtS RS L base e f, ∫ σ : CLInternalTime RS,
          spart D hG L γ δ F layer hLayer base S a b xS.1 (clLocalClock RS ![t0, t1, t2] σ) *
            ∑' κ : CLLocalDecoration RT L base (bdT RT L base xS.1 g h),
              JTM RS RT D hG L γ δ F layer hLayer base lam t1 t2 e f g h ⟨xS, κ⟩ (clLocalClock RS ![t0, t1, t2] σ b) := by
  rw [clLocalKernelModC_split_sigma hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h hL]
  congr 1
  obtain ⟨hint, hsum⟩ := hA
  have hone := fun p => fubini_oneM hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h p (hint p)
  have h1 : ∀ p, ∫ τ, fUM hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h p τ =
      ∫ σ, PhiSM RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h p σ := fun p => (hone p).2.1
  have hsP : Summable (fun p => ∫ σ, ‖PhiSM RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h p σ‖) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) (fun p => (hone p).2.2) hsum
  have hsI : Summable (fun p => ∫ σ, PhiSM RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h p σ) :=
    Summable.of_norm_bounded hsP (fun p => norm_integral_le_integral_norm _)
  simp_rw [h1]
  rw [hsI.tsum_sigma' (fun xS => hsI.sigma_factor xS)]
  refine tsum_congr (fun xS => ?_)
  have hsκ : Summable (fun κ => ∫ σ, ‖PhiSM RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h ⟨xS, κ⟩ σ‖) :=
    hsP.sigma_factor xS
  have := hasSum_integral_of_summable_integral_norm (fun κ => (hone ⟨xS, κ⟩).1) hsκ
  rw [this.tsum_eq]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun σ => by simp only [PhiSM]; exact tsum_mul_left))

include hS hT hi hU in
/-- **(tildeJ2) before the twist sum, with the modulated kernel of the lower block.** -/
theorem clLocalKernelModC_split_KT (hL : L ≠ 0) (hF : HF D hG L F layer base) :
    clLocalKernelModC D hG RU L γ δ F layer hLayer base lam t0 t1 t2 e f g h =
      (coupling d L γ δ : ℂ) ^ clLocalOrder1 RS * clLocalZeta RS *
        ∑' xS : ExtS RS L base e f, ∫ σ : CLInternalTime RS,
          spart D hG L γ δ F layer hLayer base S a b xS.1 (clLocalClock RS ![t0, t1, t2] σ) *
            clLocalKernelModC D hG RT L γ δ F layer hLayer base lam (clLocalClock RS ![t0, t1, t2] σ b) t1 t2
              (base + latticePoint L (xS.1 (clBoundaryNodes RT 0))) (base + latticePoint L (xS.1 (clBoundaryNodes RT 1)))
              g h := by
  rw [clLocalKernelModC_split_fubini hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h hL
    (absConvM_of_inputs hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h hL hF),
    order1_split hS hT hi hU RU RS RT, zeta_split hS hT hi hU RU RS RT, pow_add]
  set CS : ℂ := (coupling d L γ δ : ℂ) ^ clLocalOrder1 RS * clLocalZeta RS with hCS
  set CT : ℂ := (coupling d L γ δ : ℂ) ^ clLocalOrder1 RT * clLocalZeta RT with hCT
  have hcomb : (coupling d L γ δ : ℂ) ^ clLocalOrder1 RS * (coupling d L γ δ : ℂ) ^ clLocalOrder1 RT *
      (clLocalZeta RS * clLocalZeta RT) = CS * CT := by rw [hCS, hCT]; ring
  rw [hcomb, mul_assoc]
  congr 1
  rw [← tsum_mul_left]
  refine tsum_congr fun xS => ?_
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
  simp only
  unfold clLocalKernelModC
  simp only [JTM, bdT]
  rw [hCT]
  ring

include hS hT hi hU RU in
theorem sok_KTM (hL : L ≠ 0) (hF : HF D hG L F layer base) :
    SOK RS D hG L γ δ F layer hLayer base t0 t1 t2 e f (clBoundaryNodes RT 0) (clBoundaryNodes RT 1)
      (fun t E F' => clLocalKernelModC D hG RT L γ δ F layer hLayer base lam t t1 t2 E F' g h) := by
  obtain ⟨hint, hsum⟩ := absConvM_of_inputs hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h hL hF
  have hone := fun p => fubini_oneM hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h p (hint p)
  have hsP : Summable (fun p => ∫ σ, ‖PhiSM RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h p σ‖) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) (fun p => (hone p).2.2) hsum
  set CT : ℂ := (coupling d L γ δ : ℂ) ^ clLocalOrder1 RT * clLocalZeta RT with hCT
  have hK : ∀ (xS : ExtS RS L base e f) (σ : CLInternalTime RS),
      sInt RS D hG L γ δ F layer hLayer base t0 t1 t2 e f (clBoundaryNodes RT 0) (clBoundaryNodes RT 1)
        (fun t E F' => clLocalKernelModC D hG RT L γ δ F layer hLayer base lam t t1 t2 E F' g h) xS σ =
      CT * ∑' κ : CLLocalDecoration RT L base (bdT RT L base xS.1 g h),
        PhiSM RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h ⟨xS, κ⟩ σ := by
    intro xS σ
    unfold sInt
    beta_reduce
    unfold clLocalKernelModC
    simp only [PhiSM, JTM, bdT]
    rw [tsum_mul_left, hCT]
    ring
  refine ⟨fun xS => ?_, ?_⟩
  · have : sInt RS D hG L γ δ F layer hLayer base t0 t1 t2 e f (clBoundaryNodes RT 0) (clBoundaryNodes RT 1)
        (fun t E F' => clLocalKernelModC D hG RT L γ δ F layer hLayer base lam t t1 t2 E F' g h) xS =
        fun σ => CT * ∑' κ : CLLocalDecoration RT L base (bdT RT L base xS.1 g h),
          PhiSM RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h ⟨xS, κ⟩ σ := funext (hK xS)
    rw [this]
    exact (integrable_tsum_of_summable_integral_norm (fun κ => (hone ⟨xS, κ⟩).1) (hsP.sigma_factor xS)).const_mul CT
  · have hb : ∀ xS : ExtS RS L base e f,
        ∫ σ, ‖sInt RS D hG L γ δ F layer hLayer base t0 t1 t2 e f (clBoundaryNodes RT 0) (clBoundaryNodes RT 1)
          (fun t E F' => clLocalKernelModC D hG RT L γ δ F layer hLayer base lam t t1 t2 E F' g h) xS σ‖ ≤
          ‖CT‖ * ∑' κ : CLLocalDecoration RT L base (bdT RT L base xS.1 g h),
            ∫ σ, ‖PhiSM RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h ⟨xS, κ⟩ σ‖ := by
      intro xS
      have h1 : ∀ σ, ‖sInt RS D hG L γ δ F layer hLayer base t0 t1 t2 e f (clBoundaryNodes RT 0) (clBoundaryNodes RT 1)
          (fun t E F' => clLocalKernelModC D hG RT L γ δ F layer hLayer base lam t t1 t2 E F' g h) xS σ‖ =
          ‖CT‖ * ‖∑' κ : CLLocalDecoration RT L base (bdT RT L base xS.1 g h),
            PhiSM RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h ⟨xS, κ⟩ σ‖ := by
        intro σ; rw [hK xS σ, norm_mul]
      simp_rw [h1]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (integral_norm_tsum_le (fun κ => (hone ⟨xS, κ⟩).1) (hsP.sigma_factor xS))
        (norm_nonneg _)
    exact Summable.of_nonneg_of_le (fun xS => integral_nonneg (fun _ => norm_nonneg _)) hb (hsP.sigma.mul_left ‖CT‖)

end Fubini

end WaveTurbulence.VineEstS5C.FlatMod
