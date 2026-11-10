/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.V5WB.B.Member

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.Fubini2
public import WaveTurbulence.Foundations.Flower.V5WB.B.SSum

/-! # V5-SPACE-EXT: splitting a weighted member kernel with weights on both blocks

If the weight of the union region factors on glued decorations as an upper weight times a lower weight,
the modulated member kernel `memberMX` of the union is the weighted S-side with the lower factor the WEIGHTED
member kernel of the lower block (`memberMX_split_KT_bond`). Integrability and summability of the S-side integrand
with this weighted lower factor (`sok_memberMX`) come from the original absolute majorant and the weight bound.
Adapted from `VineSpaceK.WeightedSplit` (upper weight only) and `FlatMod.Fubini2`. -/

/-! Copied by source (V5W-B-WORLD) from V5W-A's port `Flower/V5WA/VineSpaceB/Split.lean` (see `COPIED-SHA256SUMS`): namespace `WaveTurbulence.Flower.V5WB`, every row selector (`variable [RowSel]`), the bond weight `bW` replaced by the masked, normalized `bWN` (`ψ : WD d`, bound `bWNB`). -/

@[expose] public section
namespace WaveTurbulence.Flower.V5WB
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS5C.FlatMod TTree MeasureTheory

variable {w d : ℕ} {G : Garden w} {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}

section Fubini
variable (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c) (hi : S ∩ T = {b})
  (hU : G.molecule.IsBlock (S ∪ T) a c) (RU : CLRegionData G (S ∪ T) a c) (RS : CLRegionData G S a b)
  (RT : CLRegionData G T b c) (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (lam : ℝ)
  (t0 t1 t2 : ℝ) (e f g h : Mom d)
  (μ mS mT : (GNode G.tree → Fin d → ℤ) → ℂ)

include hS hT hi hU in
/-- The sigma form of the splitting of the weighted kernel at `b`. -/
theorem memberMX_bond_split_sigma (hL : L ≠ 0)
    (hμ : ∀ p : Σ xS : ExtS RS L base e f, CLLocalDecoration RT L base (bdT RT L base xS.1 g h),
      μ (glue RS p.1.1 (clExtendIndices RT p.2.1)) = mS p.1.1 * mT (clExtendIndices RT p.2.1)) :
    memberMX D hG RU L γ δ F layer hLayer base lam μ t0 t1 t2 e f g h =
      (coupling d L γ δ : ℂ) ^ clLocalOrder1 RU * clLocalZeta RU *
        ∑' p : Σ xS : ExtS RS L base e f, CLLocalDecoration RT L base (bdT RT L base xS.1 g h),
          ∫ τ : CLInternalTime RU, (mS p.1.1 * mT (clExtendIndices RT p.2.1)) *
            fUM hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h p τ := by
  unfold memberMX
  congr 1
  rw [← (splitLocalEquiv hS hT hi hU RU RS RT hL base ![e, f, g, h]).symm.tsum_eq]
  refine tsum_congr (fun p => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall (fun τ => ?_))
  rw [splitLocalEquiv_symm_val hS hT hi hU RU RS RT hL base ![e, f, g, h] p, hμ p]
  unfold fUM
  exact congrArg (fun z => (mS p.1.1 * mT (clExtendIndices RT p.2.1)) *
    (lowModC RU lam ![t0, t1, t2] τ * z))
    (fU_eq hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h hL p τ).symm

/-- The weighted lower kernel at the boundary read from an upper decoration, as a sum of weighted `JTM`. -/
theorem memberMX_T_eq (xS : ExtS RS L base e f) (u : ℝ) :
    memberMX D hG RT L γ δ F layer hLayer base lam mT u t1 t2
        (base + latticePoint L (xS.1 (clBoundaryNodes RT 0))) (base + latticePoint L (xS.1 (clBoundaryNodes RT 1))) g h =
      (coupling d L γ δ : ℂ) ^ clLocalOrder1 RT * clLocalZeta RT *
        ∑' κ : CLLocalDecoration RT L base (bdT RT L base xS.1 g h),
          mT (clExtendIndices RT κ.1) * JTM RS RT D hG L γ δ F layer hLayer base lam t1 t2 e f g h ⟨xS, κ⟩ u := by
  unfold memberMX JTM
  congr 1
  exact tsum_congr fun κ => integral_const_mul _ _

include hS hT hi hU in
/-- **Fubini form** of the weighted kernel with weights on both blocks. -/
theorem memberMX_bond_split_fubini (hL : L ≠ 0)
    (hμ : ∀ p : Σ xS : ExtS RS L base e f, CLLocalDecoration RT L base (bdT RT L base xS.1 g h),
      μ (glue RS p.1.1 (clExtendIndices RT p.2.1)) = mS p.1.1 * mT (clExtendIndices RT p.2.1))
    (MS MT : ℝ) (hMS : 0 ≤ MS) (hMT : 0 ≤ MT) (hmS : ∀ x, ‖mS x‖ ≤ MS) (hmT : ∀ x, ‖mT x‖ ≤ MT)
    (hA : AbsConvM hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h) :
    memberMX D hG RU L γ δ F layer hLayer base lam μ t0 t1 t2 e f g h =
      (coupling d L γ δ : ℂ) ^ clLocalOrder1 RU * clLocalZeta RU *
        ∑' xS : ExtS RS L base e f, ∫ σ : CLInternalTime RS,
          mS xS.1 * (spart D hG L γ δ F layer hLayer base S a b xS.1 (clLocalClock RS ![t0, t1, t2] σ) *
            ∑' κ : CLLocalDecoration RT L base (bdT RT L base xS.1 g h),
              mT (clExtendIndices RT κ.1) *
                JTM RS RT D hG L γ δ F layer hLayer base lam t1 t2 e f g h ⟨xS, κ⟩ (clLocalClock RS ![t0, t1, t2] σ b)) := by
  rw [memberMX_bond_split_sigma hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h μ mS mT hL hμ]
  congr 1
  obtain ⟨hint, hsum⟩ := hA
  have hone := fun p => fubini_oneM hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h p (hint p)
  set Φ := PhiSM RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h with hΦ
  have h1 : ∀ p : Σ xS : ExtS RS L base e f, CLLocalDecoration RT L base (bdT RT L base xS.1 g h),
      ∫ τ, (mS p.1.1 * mT (clExtendIndices RT p.2.1)) *
        fUM hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h p τ =
      ∫ σ, (mS p.1.1 * mT (clExtendIndices RT p.2.1)) * Φ p σ := by
    intro p
    simp only [integral_const_mul, (hone p).2.1]
  have hsP : Summable (fun p => ∫ σ, ‖Φ p σ‖) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) (fun p => (hone p).2.2) hsum
  have hbd : ∀ p : Σ xS : ExtS RS L base e f, CLLocalDecoration RT L base (bdT RT L base xS.1 g h),
      ‖mS p.1.1 * mT (clExtendIndices RT p.2.1)‖ ≤ MS * MT := fun p => by
    rw [norm_mul]
    exact mul_le_mul (hmS _) (hmT _) (norm_nonneg _) hMS
  have hsI : Summable (fun p : Σ xS : ExtS RS L base e f, CLLocalDecoration RT L base (bdT RT L base xS.1 g h) =>
      ∫ σ, (mS p.1.1 * mT (clExtendIndices RT p.2.1)) * Φ p σ) :=
    summable_weighted_integrals volume _ hsP (fun p => mS p.1.1 * mT (clExtendIndices RT p.2.1)) (MS * MT)
      (mul_nonneg hMS hMT) hbd
  simp_rw [h1]
  rw [hsI.tsum_sigma' (fun xS => hsI.sigma_factor xS)]
  refine tsum_congr (fun xS => ?_)
  have hsκ : Summable (fun κ => ∫ σ, ‖mT (clExtendIndices RT κ.1) * Φ ⟨xS, κ⟩ σ‖) := by
    refine Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) (fun κ => ?_)
      ((hsP.sigma_factor xS).mul_left MT)
    simp only [norm_mul, integral_const_mul]
    exact mul_le_mul_of_nonneg_right (hmT _) (integral_nonneg fun _ => norm_nonneg _)
  have hh := hasSum_integral_of_summable_integral_norm (fun κ => ((hone ⟨xS, κ⟩).1.const_mul
    (mT (clExtendIndices RT κ.1)))) hsκ
  have e1 : ∀ κ : CLLocalDecoration RT L base (bdT RT L base xS.1 g h),
      ∫ σ, (mS xS.1 * mT (clExtendIndices RT κ.1)) * Φ ⟨xS, κ⟩ σ =
        mS xS.1 * ∫ σ, mT (clExtendIndices RT κ.1) * Φ ⟨xS, κ⟩ σ := by
    intro κ
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun σ => by ring)
  simp_rw [e1]
  rw [tsum_mul_left, hh.tsum_eq, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun σ => ?_))
  beta_reduce
  congr 1
  have e2 : ∀ κ : CLLocalDecoration RT L base (bdT RT L base xS.1 g h),
      mT (clExtendIndices RT κ.1) * Φ ⟨xS, κ⟩ σ =
        spart D hG L γ δ F layer hLayer base S a b xS.1 (clLocalClock RS ![t0, t1, t2] σ) *
          (mT (clExtendIndices RT κ.1) *
            JTM RS RT D hG L γ δ F layer hLayer base lam t1 t2 e f g h ⟨xS, κ⟩ (clLocalClock RS ![t0, t1, t2] σ b)) := by
    intro κ
    simp only [hΦ, PhiSM]
    ring
  simp_rw [e2]
  exact tsum_mul_left

include hS hT hi hU in
/-- **The weighted kernel is the weighted S-side with the WEIGHTED lower kernel.** -/
theorem memberMX_split_KT_bond (hL : L ≠ 0) (hF : HF D hG L F layer base)
    (hμ : ∀ p : Σ xS : ExtS RS L base e f, CLLocalDecoration RT L base (bdT RT L base xS.1 g h),
      μ (glue RS p.1.1 (clExtendIndices RT p.2.1)) = mS p.1.1 * mT (clExtendIndices RT p.2.1))
    (MS MT : ℝ) (hMS : 0 ≤ MS) (hMT : 0 ≤ MT) (hmS : ∀ x, ‖mS x‖ ≤ MS) (hmT : ∀ x, ‖mT x‖ ≤ MT) :
    memberMX D hG RU L γ δ F layer hLayer base lam μ t0 t1 t2 e f g h =
      (coupling d L γ δ : ℂ) ^ clLocalOrder1 RS * clLocalZeta RS *
        ∑' xS : ExtS RS L base e f, ∫ σ : CLInternalTime RS,
          mS xS.1 * (spart D hG L γ δ F layer hLayer base S a b xS.1 (clLocalClock RS ![t0, t1, t2] σ) *
            memberMX D hG RT L γ δ F layer hLayer base lam mT (clLocalClock RS ![t0, t1, t2] σ b) t1 t2
              (base + latticePoint L (xS.1 (clBoundaryNodes RT 0))) (base + latticePoint L (xS.1 (clBoundaryNodes RT 1)))
              g h) := by
  rw [memberMX_bond_split_fubini hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h μ mS mT hL hμ
    MS MT hMS hMT hmS hmT (absConvM_of_inputs hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h hL hF),
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
  rw [memberMX_T_eq RS RT D hG L γ δ F layer hLayer base lam t1 t2 e f g h mT xS (clLocalClock RS ![t0, t1, t2] σ b)]
  rw [hCT]
  ring

include hS hT hi hU RU in
/-- Integrability and summability of the S-side integrand with the weighted lower kernel. -/
theorem sok_memberMX (hL : L ≠ 0) (hF : HF D hG L F layer base) (MT : ℝ) (hMT : 0 ≤ MT) (hmT : ∀ x, ‖mT x‖ ≤ MT) :
    SOK RS D hG L γ δ F layer hLayer base t0 t1 t2 e f (clBoundaryNodes RT 0) (clBoundaryNodes RT 1)
      (fun t E F' => memberMX D hG RT L γ δ F layer hLayer base lam mT t t1 t2 E F' g h) := by
  obtain ⟨hint, hsum⟩ := absConvM_of_inputs hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h hL hF
  have hone := fun p => fubini_oneM hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h p (hint p)
  set Φ := PhiSM RS RT D hG L γ δ F layer hLayer base lam t0 t1 t2 e f g h with hΦ
  have hsP : Summable (fun p => ∫ σ, ‖Φ p σ‖) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) (fun p => (hone p).2.2) hsum
  set CT : ℂ := (coupling d L γ δ : ℂ) ^ clLocalOrder1 RT * clLocalZeta RT with hCT
  have hK : ∀ (xS : ExtS RS L base e f) (σ : CLInternalTime RS),
      sInt RS D hG L γ δ F layer hLayer base t0 t1 t2 e f (clBoundaryNodes RT 0) (clBoundaryNodes RT 1)
        (fun t E F' => memberMX D hG RT L γ δ F layer hLayer base lam mT t t1 t2 E F' g h) xS σ =
      CT * ∑' κ : CLLocalDecoration RT L base (bdT RT L base xS.1 g h),
        mT (clExtendIndices RT κ.1) * Φ ⟨xS, κ⟩ σ := by
    intro xS σ
    unfold sInt
    beta_reduce
    rw [memberMX_T_eq RS RT D hG L γ δ F layer hLayer base lam t1 t2 e f g h mT xS (clLocalClock RS ![t0, t1, t2] σ b)]
    have e2 : ∀ κ : CLLocalDecoration RT L base (bdT RT L base xS.1 g h),
        mT (clExtendIndices RT κ.1) * Φ ⟨xS, κ⟩ σ =
          spart D hG L γ δ F layer hLayer base S a b xS.1 (clLocalClock RS ![t0, t1, t2] σ) *
            (mT (clExtendIndices RT κ.1) *
              JTM RS RT D hG L γ δ F layer hLayer base lam t1 t2 e f g h ⟨xS, κ⟩ (clLocalClock RS ![t0, t1, t2] σ b)) := by
      intro κ
      simp only [hΦ, PhiSM]
      ring
    simp_rw [e2]
    rw [tsum_mul_left, hCT]
    ring
  have hsκ : ∀ xS : ExtS RS L base e f,
      Summable (fun κ : CLLocalDecoration RT L base (bdT RT L base xS.1 g h) =>
        ∫ σ, ‖mT (clExtendIndices RT κ.1) * Φ ⟨xS, κ⟩ σ‖) := fun xS => by
    refine Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) (fun κ => ?_)
      ((hsP.sigma_factor xS).mul_left MT)
    simp only [norm_mul, integral_const_mul]
    exact mul_le_mul_of_nonneg_right (hmT _) (integral_nonneg fun _ => norm_nonneg _)
  refine ⟨fun xS => ?_, ?_⟩
  · have : sInt RS D hG L γ δ F layer hLayer base t0 t1 t2 e f (clBoundaryNodes RT 0) (clBoundaryNodes RT 1)
        (fun t E F' => memberMX D hG RT L γ δ F layer hLayer base lam mT t t1 t2 E F' g h) xS =
        fun σ => CT * ∑' κ : CLLocalDecoration RT L base (bdT RT L base xS.1 g h),
          mT (clExtendIndices RT κ.1) * Φ ⟨xS, κ⟩ σ := funext (hK xS)
    rw [this]
    exact (integrable_tsum_of_summable_integral_norm
      (fun κ => (hone ⟨xS, κ⟩).1.const_mul (mT (clExtendIndices RT κ.1))) (hsκ xS)).const_mul CT
  · have hb : ∀ xS : ExtS RS L base e f,
        ∫ σ, ‖sInt RS D hG L γ δ F layer hLayer base t0 t1 t2 e f (clBoundaryNodes RT 0) (clBoundaryNodes RT 1)
          (fun t E F' => memberMX D hG RT L γ δ F layer hLayer base lam mT t t1 t2 E F' g h) xS σ‖ ≤
          ‖CT‖ * (MT * ∑' κ : CLLocalDecoration RT L base (bdT RT L base xS.1 g h), ∫ σ, ‖Φ ⟨xS, κ⟩ σ‖) := by
      intro xS
      have h1 : ∀ σ, ‖sInt RS D hG L γ δ F layer hLayer base t0 t1 t2 e f (clBoundaryNodes RT 0) (clBoundaryNodes RT 1)
          (fun t E F' => memberMX D hG RT L γ δ F layer hLayer base lam mT t t1 t2 E F' g h) xS σ‖ =
          ‖CT‖ * ‖∑' κ : CLLocalDecoration RT L base (bdT RT L base xS.1 g h),
            mT (clExtendIndices RT κ.1) * Φ ⟨xS, κ⟩ σ‖ := by
        intro σ; rw [hK xS σ, norm_mul]
      simp_rw [h1]
      rw [integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine (integral_norm_tsum_le (fun κ => (hone ⟨xS, κ⟩).1.const_mul (mT (clExtendIndices RT κ.1)))
        (hsκ xS)).trans ?_
      rw [← tsum_mul_left]
      refine ((hsκ xS).tsum_le_tsum (fun κ => ?_) ((hsP.sigma_factor xS).mul_left MT))
      simp only [norm_mul, integral_const_mul]
      exact mul_le_mul_of_nonneg_right (hmT _) (integral_nonneg fun _ => norm_nonneg _)
    exact Summable.of_nonneg_of_le (fun xS => integral_nonneg (fun _ => norm_nonneg _)) hb
      ((hsP.sigma.mul_left MT).mul_left ‖CT‖)

end Fubini

end WaveTurbulence.Flower.V5WB
