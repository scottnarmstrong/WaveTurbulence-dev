/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtWhole.Cont

/-! # D6b: the protected kernel is jointly continuous in its upper clock and its port time

`continuous_kernelProt_joint`: with a bounded multiplier and lattice-summable input profiles (at most one lone leaf
per tree), `ts ↦ kernelProt … (fun _ => ts 0) (ts 1) fix k₀ 0 0` is continuous on `ℝ²` when the pins `fix` do not
depend on `ts`. As `continuous_kernelProt_up`: the free-time integrand is locally constant in `(T, s)` off the null
set `{τ | ∃ b, τ b ∈ {T₀, s₀}}`, dominated by the unit cube, and the decoration series is dominated by ProtCut's
summable leaf majorant. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory Filter Topology

namespace WaveTurbulence.Flower.ProtWhole

open WaveTurbulence.PL234 WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut

variable {w d : ℕ}

theorem mem_protDom_joint_iff (LG : LayeredGarden w) (fix : GBranch LG.garden.tree → Option ℝ)
    (x : GBranch LG.garden.tree → ℝ) (T T₀ s s₀ : ℝ) (h : ∀ b, fix b = none → (x b < T ↔ x b < T₀))
    (h' : ∀ b, fix b = none → (s < x b ↔ s₀ < x b)) :
    x ∈ protDom LG (fun _ => T) s fix ↔ x ∈ protDom LG (fun _ => T₀) s₀ fix := by
  unfold protDom kDomainFix
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun b => ⟨fun hf => ?_, (h1 b).2⟩, fun b hb hf => (h' b hf).1 (h2 b hb hf)⟩
    obtain ⟨a1, a2, a3, a4⟩ := (h1 b).1 hf
    exact ⟨a1, a2, a3, (h b hf).1 a4⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun b => ⟨fun hf => ?_, (h1 b).2⟩, fun b hb hf => (h' b hf).2 (h2 b hb hf)⟩
    obtain ⟨a1, a2, a3, a4⟩ := (h1 b).1 hf
    exact ⟨a1, a2, a3, (h b hf).2 a4⟩

theorem continuousAt_protIntegrand_joint (L γ δ : ℝ) (LG : LayeredGarden w)
    (fix : GBranch LG.garden.tree → Option ℝ) (K : GNode LG.garden.tree → Mom d) (ts₀ : Fin 2 → ℝ)
    (τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ) (hτ : ∀ b, τ b ≠ ts₀ 0 ∧ τ b ≠ ts₀ 1) :
    ContinuousAt (fun ts : Fin 2 → ℝ => protIntegrand L γ δ LG (fun _ => ts 0) (ts 1) fix K τ) ts₀ := by
  have hev : ∀ᶠ ts in 𝓝 ts₀, ∀ b : {b : GBranch LG.garden.tree // fix b = none},
      (τ b < ts 0 ↔ τ b < ts₀ 0) ∧ (ts 1 < τ b ↔ ts₀ 1 < τ b) := by
    rw [Filter.eventually_all]
    intro b
    have e0 : ∀ᶠ ts in 𝓝 ts₀, (τ b < ts 0 ↔ τ b < ts₀ 0) := by
      rcases lt_or_gt_of_ne (hτ b).1 with hb | hb
      · filter_upwards [(continuous_apply (0 : Fin 2)).continuousAt.preimage_mem_nhds (Ioi_mem_nhds hb)]
          with ts hts
        exact iff_of_true hts hb
      · filter_upwards [(continuous_apply (0 : Fin 2)).continuousAt.preimage_mem_nhds (Iio_mem_nhds hb)]
          with ts hts
        exact iff_of_false (not_lt.2 (le_of_lt hts)) (not_lt.2 hb.le)
    have e1 : ∀ᶠ ts in 𝓝 ts₀, (ts 1 < τ b ↔ ts₀ 1 < τ b) := by
      rcases lt_or_gt_of_ne (hτ b).2 with hb | hb
      · filter_upwards [(continuous_apply (1 : Fin 2)).continuousAt.preimage_mem_nhds (Ioi_mem_nhds hb)]
          with ts hts
        exact iff_of_false (not_lt.2 (le_of_lt hts)) (not_lt.2 hb.le)
      · filter_upwards [(continuous_apply (1 : Fin 2)).continuousAt.preimage_mem_nhds (Iio_mem_nhds hb)]
          with ts hts
        exact iff_of_true hts hb
    exact e0.and e1
  refine (continuousAt_const (y := protIntegrand L γ δ LG (fun _ => ts₀ 0) (ts₀ 1) fix K τ)).congr ?_
  filter_upwards [hev] with ts hts
  unfold protIntegrand
  have hmem := mem_protDom_joint_iff LG fix (LG.garden.extendFix fix τ) (ts 0) (ts₀ 0) (ts 1) (ts₀ 1)
    (fun b hf => by rw [extendFix_free LG.garden fix τ ⟨b, hf⟩]; exact (hts ⟨b, hf⟩).1)
    (fun b hf => by rw [extendFix_free LG.garden fix τ ⟨b, hf⟩]; exact (hts ⟨b, hf⟩).2)
  by_cases hm : LG.garden.extendFix fix τ ∈ protDom LG (fun _ => ts₀ 0) (ts₀ 1) fix
  · rw [indicator_of_mem hm, indicator_of_mem (hmem.2 hm)]
  · rw [indicator_of_notMem hm, indicator_of_notMem (fun h => hm (hmem.1 h))]

theorem continuous_protTime_joint (L γ δ : ℝ) (LG : LayeredGarden w)
    (fix : GBranch LG.garden.tree → Option ℝ) (K : GNode LG.garden.tree → Mom d) :
    Continuous (fun ts : Fin 2 → ℝ => protTime L γ δ LG (fun _ => ts 0) (ts 1) fix K) := by
  have hBm : MeasurableSet (freeBox LG fix) := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hint : Integrable ((freeBox LG fix).indicator (1 : ({b : GBranch LG.garden.tree //
      fix b = none} → ℝ) → ℝ)) := by
    rw [integrable_indicator_iff hBm]
    exact integrableOn_const (by rw [volume_freeBox]; exact ENNReal.one_ne_top)
  rw [continuous_iff_continuousAt]
  intro ts₀
  show ContinuousAt (fun ts : Fin 2 → ℝ => ∫ τ, protIntegrand L γ δ LG (fun _ => ts 0) (ts 1) fix K τ) ts₀
  have hae : ∀ᵐ τ ∂(volume : Measure ({b : GBranch LG.garden.tree // fix b = none} → ℝ)),
      ∀ b, τ b ≠ ts₀ 0 ∧ τ b ≠ ts₀ 1 :=
    ((ae_ne_eval _ (ts₀ 0)).and (ae_ne_eval _ (ts₀ 1))).mono fun τ h b => ⟨h.1 b, h.2 b⟩
  exact continuousAt_of_dominated
    (Eventually.of_forall fun ts =>
      (measurable_protIntegrand L γ δ LG (fun _ => ts 0) (ts 1) fix K).aestronglyMeasurable)
    (Eventually.of_forall fun ts => Eventually.of_forall
      (norm_protIntegrand_le L γ δ LG (fun _ => ts 0) (ts 1) fix K))
    hint (hae.mono fun τ hτ => continuousAt_protIntegrand_joint L γ δ LG fix K ts₀ τ hτ)

/-- **Joint continuity in the upper clock and the port time.** -/
theorem continuous_kernelProt_joint (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (C : ℝ) (hm : ∀ K, ‖m K‖ ≤ C)
    (fix : GBranch LG.garden.tree → Option ℝ) (k₀ : Mom d)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree => ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, Summable fun n : Fin d → ℤ => |H ℓ.1 (k₀ + latticePoint L n)|) :
    Continuous (fun ts : Fin 2 → ℝ => kernelProt L γ δ LG H m (fun _ => ts 0) (ts 1) fix k₀ (fun _ => 0) 0) := by
  have he : (fun ts : Fin 2 → ℝ => kernelProt L γ δ LG H m (fun _ => ts 0) (ts 1) fix k₀ (fun _ => 0) 0) =
      fun ts => (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
        ∑' κ : GenDecoration LG.garden d (fun _ => 0) 0,
          protSummand L γ δ LG H m (fun _ => ts 0) (ts 1) fix k₀ κ := by
    funext ts
    exact kernelProt_eq_tsum L γ δ LG H m _ _ fix k₀ _ _
  rw [he]
  refine continuous_const.mul (continuous_tsum (fun κ => ?_)
    ((summable_leafMajorant L LG H k₀ (fun _ => 0) 0 hlone hH).mul_left C)
    (fun κ ts => norm_protSummand_le L γ δ LG H m C hm (fun _ => ts 0) (ts 1) fix k₀ κ))
  unfold protSummand
  exact continuous_const.mul ((continuous_const.mul
    (continuous_protTime_joint L γ δ LG fix _)).mul continuous_const)

end WaveTurbulence.Flower.ProtWhole
