/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafwiseFrechetMajorant
public import WaveTurbulence.Foundations.Spine.LocalSmoothSeries
/-! Spatial regularity of actual leaf kernels from local summable derivative majorants. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset Set

noncomputable def leafSpatialSummand {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (H : LeafProfiles w d) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) (k : Mom d) : ℂ :=
  (epsDec LG.garden κ.1 : ℂ) *
    phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L 0 κ.1) *
    ∏ l ∈ inputLeaves LG.garden, (H l.1 (k + latticePoint L (κ.1 l.toNode)) : ℂ)

theorem kernelLeaves_eq_spatial_tsum {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (H : LeafProfiles w d) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) (k : Mom d) :
    kernelLeaves L γ δ LG H up s k nroot nfl =
      (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
        ∑' κ : GenDecoration LG.garden d nroot nfl, leafSpatialSummand L γ δ LG H up s κ k := by
  unfold kernelLeaves leafSpatialSummand
  congr 1
  apply tsum_congr
  intro κ
  rw [phaseIntegral_coset_eq_zero L γ δ LG.garden _ s k κ.1 κ.2.1]
  rfl

theorem contDiff_leafSpatialSummand {w d A : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (H : LeafProfiles w d) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (hc : ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ A (fun x => (H l.1 x : ℂ)))
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) : ContDiff ℝ A (leafSpatialSummand L γ δ LG H up s κ) := by
  unfold leafSpatialSummand
  apply contDiff_const.mul
  apply contDiff_prod
  intro l hl
  exact (hc l hl).comp (contDiff_id.add contDiff_const)

theorem norm_leafSpatialSummand_frechet_le {w d A B r : ℕ} (hd : 1 ≤ d) (hB : d + 1 ≤ B)
    (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (C : (Fin w × TTree.Path) → NNReal) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (hc : ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ A (fun x => (H l.1 x : ℂ)))
    (hb : ∀ l ∈ inputLeaves LG.garden, SNormR A B (H l.1) ≤ ENNReal.ofReal (C l.1 : ℝ))
    (hr : r ≤ A) (k k₀ : Mom d) (hk : k ∈ Metric.closedBall k₀ 1)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) :
    ‖iteratedFDeriv ℝ r (leafSpatialSummand L γ δ LG H up s κ) k‖ ≤
      leafLeibnizCount LG r * leafJetMajorant L LG C A k₀ κ := by
  let c : ℂ := (epsDec LG.garden κ.1 : ℂ) *
    phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L 0 κ.1)
  let f : Mom d → ℂ := fun x => ∏ l ∈ inputLeaves LG.garden,
    (H l.1 (x + latticePoint L (κ.1 l.toNode)) : ℂ)
  have hf : ContDiff ℝ A f := by
    apply contDiff_prod
    intro l hl
    exact (hc l hl).comp (contDiff_id.add contDiff_const)
  have hc1 : ‖c‖ ≤ 1 := by
    rw [norm_mul]
    have he : ‖(epsDec LG.garden κ.1 : ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using abs_epsDec_le_one LG.garden κ.1
    exact (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans
      (by simpa only [one_mul] using (norm_phaseIntegral_le_one L γ δ LG up s
        (cosetDecoration LG.garden L 0 κ.1)))
  change ‖iteratedFDeriv ℝ r (fun x => c • f x) k‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' ((hf.of_le (by exact_mod_cast hr)).contDiffAt), norm_smul]
  apply (mul_le_mul_of_nonneg_right hc1 (norm_nonneg _)).trans
  rw [one_mul]
  exact norm_leafProduct_frechet_le hd hB L LG H C hc hb hr k k₀ hk κ

theorem contDiff_kernelLeaves_spatial {w d A B : ℕ} (hd : 1 ≤ d) {L : ℝ} (hL : 1 ≤ L)
    (γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (C : (Fin w × TTree.Path) → NNReal)
    (hc : ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ A (fun x => (H l.1 x : ℂ)))
    (hb : ∀ l ∈ inputLeaves LG.garden, SNormR A B (H l.1) ≤ ENNReal.ofReal (C l.1 : ℝ))
    (hB : d + 1 ≤ B) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hlone : ∀ j, (univ.filter fun l : GLeaf LG.garden.tree =>
      l.1.1 = j ∧ LG.garden.IsLone l).card ≤ 1) :
    ContDiff ℝ A (fun k => kernelLeaves L γ δ LG H up s k nroot nfl) := by
  classical
  have he : (fun k => kernelLeaves L γ δ LG H up s k nroot nfl) =
      fun k => (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
        ∑' κ : GenDecoration LG.garden d nroot nfl, leafSpatialSummand L γ δ LG H up s κ k :=
    funext (kernelLeaves_eq_spatial_tsum L γ δ LG H up s nroot nfl)
  rw [he]
  apply contDiff_iff_contDiffAt.mpr
  intro k₀
  have hseries := local_contDiffOn_tsum (N := (A : ℕ∞))
    (f := fun κ : GenDecoration LG.garden d nroot nfl => leafSpatialSummand L γ δ LG H up s κ)
    (v := fun r κ => leafLeibnizCount LG r * leafJetMajorant L LG C A k₀ κ)
    Metric.isOpen_ball (convex_ball k₀ (1 : ℝ)).isPreconnected
    (fun κ => contDiff_leafSpatialSummand L γ δ LG H up s hc κ)
    (fun r _ => (summable_leafJetMajorant hL LG C A k₀ nroot nfl hlone).mul_left _)
    (fun r κ k hk hr => norm_leafSpatialSummand_frechet_le hd hB L γ δ LG H C up s hc hb
      (by exact_mod_cast hr) k k₀ (Metric.ball_subset_closedBall hk) κ)
  exact (contDiffOn_const.mul hseries).contDiffAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))

end WaveTurbulence.LGSpine
