/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafwiseKernelSpatial
public import WaveTurbulence.Foundations.Spine.LocalCoordinateSeries
/-! Exact first-coordinate differentiation of the actual leaf kernel through its decoration sum. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Finset

theorem partialMom_kernelLeaves_spatial {w d B : ℕ} (hd : 1 ≤ d) {L : ℝ} (hL : 1 ≤ L)
    (hB : d + 1 ≤ B) (γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (C : (Fin w × TTree.Path) → NNReal)
    (hc : ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ (1 : ℕ) (fun x => (H l.1 x : ℂ)))
    (hb : ∀ l ∈ inputLeaves LG.garden, SNormR 1 B (H l.1) ≤ ENNReal.ofReal (C l.1 : ℝ))
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hlone : ∀ j, (univ.filter fun l : GLeaf LG.garden.tree =>
      l.1.1 = j ∧ LG.garden.IsLone l).card ≤ 1)
    (j : Fin d) (k₀ : Mom d) :
    partialMom j (fun k => kernelLeaves L γ δ LG H up s k nroot nfl) k₀ =
      ((coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta) *
        ∑' κ : GenDecoration LG.garden d nroot nfl,
          partialMom j (leafSpatialSummand L γ δ LG H up s κ) k₀ := by
  classical
  let U : Set (Mom d) := Metric.ball k₀ 1
  let v : ℕ → GenDecoration LG.garden d nroot nfl → ℝ :=
    fun r κ => leafLeibnizCount LG r * leafJetMajorant L LG C 1 k₀ κ
  have hv (r : ℕ) (_ : r ≤ 1) : Summable (v r) :=
    (summable_leafJetMajorant hL LG C 1 k₀ nroot nfl hlone).mul_left _
  have hbd (r : ℕ) (κ : GenDecoration LG.garden d nroot nfl) (k : Mom d)
      (hk : k ∈ U) (hr : r ≤ 1) :
      ‖iteratedFDeriv ℝ r (leafSpatialSummand L γ δ LG H up s κ) k‖ ≤ v r κ :=
    norm_leafSpatialSummand_frechet_le hd hB L γ δ LG H C up s hc hb hr k k₀
      (Metric.ball_subset_closedBall hk) κ
  have hf := fun κ : GenDecoration LG.garden d nroot nfl =>
    contDiff_leafSpatialSummand L γ δ LG H up s hc κ
  have hseries := local_contDiffOn_tsum (N := (1 : ℕ∞)) Metric.isOpen_ball
    (convex_ball k₀ (1 : ℝ)).isPreconnected hf
    (fun r hr => hv r (by exact_mod_cast hr))
    (fun r κ k hk hr => hbd r κ k hk (by exact_mod_cast hr))
  have hk₀ : k₀ ∈ U := Metric.mem_ball_self (by norm_num)
  have hdiff := (hseries.contDiffAt (Metric.isOpen_ball.mem_nhds hk₀)).differentiableAt (by norm_num)
  have he : (fun k => kernelLeaves L γ δ LG H up s k nroot nfl) =
      fun k => ((coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta) *
        ∑' κ : GenDecoration LG.garden d nroot nfl, leafSpatialSummand L γ δ LG H up s κ k :=
    funext (kernelLeaves_eq_spatial_tsum L γ δ LG H up s nroot nfl)
  rw [he]
  have hder := hdiff.hasFDerivAt.const_mul
    ((coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta)
  have hpartial := local_partialMom_tsum Metric.isOpen_ball
    (convex_ball k₀ (1 : ℝ)).isPreconnected hf hv hbd j k₀ hk₀
  have hconst : partialMom j
      (fun k => ((coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta) *
        ∑' κ : GenDecoration LG.garden d nroot nfl, leafSpatialSummand L γ δ LG H up s κ k) k₀ =
      ((coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta) *
        partialMom j (fun k => ∑' κ : GenDecoration LG.garden d nroot nfl,
          leafSpatialSummand L γ δ LG H up s κ k) k₀ := by
    unfold partialMom
    rw [hder.fderiv]
    rfl
  rw [hconst, hpartial]

end WaveTurbulence.LGSpine
