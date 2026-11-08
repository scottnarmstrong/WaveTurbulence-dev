/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.CutTerm

/-! # D6b: the protected kernel is continuous in its upper clock

`continuous_kernelProt_up`: with a bounded multiplier and lattice-summable input profiles (at most one lone leaf per
tree), `T ↦ kernelProt … (fun _ => T) s fix k₀ 0 0` is continuous when the pins `fix` do not depend on `T`.
* the free-time integrand is locally constant in `T` off the null set `{τ | ∃ b, τ b = T₀}`
  (`continuousAt_protIntegrand_up`), and dominated by the unit cube (ProtCut `norm_protIntegrand_le`), so
  `protTime` is continuous (`continuous_protTime_up`, Mathlib `continuousAt_of_dominated`);
* the decoration series is dominated by ProtCut's summable leaf majorant (Weierstrass `continuous_tsum`).

Also `kernelProt_port`: the lone-port time is void when every lone parent is pinned. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory Filter Topology

namespace WaveTurbulence.Flower.ProtWhole

open WaveTurbulence.PL234 WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut

variable {w d : ℕ}

theorem mem_protDom_up_iff (LG : LayeredGarden w) (s : ℝ) (fix : GBranch LG.garden.tree → Option ℝ)
    (x : GBranch LG.garden.tree → ℝ) (T T₀ : ℝ) (h : ∀ b, fix b = none → (x b < T ↔ x b < T₀)) :
    x ∈ protDom LG (fun _ => T) s fix ↔ x ∈ protDom LG (fun _ => T₀) s fix := by
  unfold protDom kDomainFix
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun b => ⟨fun hf => ?_, (h1 b).2⟩, h2⟩
    obtain ⟨a1, a2, a3, a4⟩ := (h1 b).1 hf
    exact ⟨a1, a2, a3, (h b hf).1 a4⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun b => ⟨fun hf => ?_, (h1 b).2⟩, h2⟩
    obtain ⟨a1, a2, a3, a4⟩ := (h1 b).1 hf
    exact ⟨a1, a2, a3, (h b hf).2 a4⟩

theorem continuousAt_protIntegrand_up (L γ δ : ℝ) (LG : LayeredGarden w) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (K : GNode LG.garden.tree → Mom d) (T₀ : ℝ)
    (τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ) (hτ : ∀ b, τ b ≠ T₀) :
    ContinuousAt (fun T => protIntegrand L γ δ LG (fun _ => T) s fix K τ) T₀ := by
  have hev : ∀ᶠ T in 𝓝 T₀, ∀ b : {b : GBranch LG.garden.tree // fix b = none}, (τ b < T ↔ τ b < T₀) := by
    rw [Filter.eventually_all]
    intro b
    rcases lt_or_gt_of_ne (hτ b) with hb | hb
    · filter_upwards [Ioi_mem_nhds hb] with T hT
      exact iff_of_true hT hb
    · filter_upwards [Iio_mem_nhds hb] with T hT
      exact iff_of_false (not_lt.2 (le_of_lt hT)) (not_lt.2 hb.le)
  refine (continuousAt_const (y := protIntegrand L γ δ LG (fun _ => T₀) s fix K τ)).congr ?_
  filter_upwards [hev] with T hT
  unfold protIntegrand
  have hmem := mem_protDom_up_iff LG s fix (LG.garden.extendFix fix τ) T T₀ (fun b hf => by
    rw [extendFix_free LG.garden fix τ ⟨b, hf⟩]
    exact hT ⟨b, hf⟩)
  by_cases hm : LG.garden.extendFix fix τ ∈ protDom LG (fun _ => T₀) s fix
  · rw [indicator_of_mem hm, indicator_of_mem (hmem.2 hm)]
  · rw [indicator_of_notMem hm, indicator_of_notMem (fun h => hm (hmem.1 h))]

theorem ae_ne_eval (ι : Type*) [Fintype ι] (T₀ : ℝ) :
    ∀ᵐ τ ∂(volume : Measure (ι → ℝ)), ∀ b, τ b ≠ T₀ := by
  rw [ae_all_iff]
  intro b
  rw [ae_iff]
  simp only [ne_eq, not_not]
  exact Measure.pi_eval_preimage_null (μ := fun _ : ι => (volume : Measure ℝ)) (i := b) (s := ({T₀} : Set ℝ))
    Real.volume_singleton

theorem continuous_protTime_up (L γ δ : ℝ) (LG : LayeredGarden w) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (K : GNode LG.garden.tree → Mom d) :
    Continuous (fun T => protTime L γ δ LG (fun _ => T) s fix K) := by
  have hBm : MeasurableSet (freeBox LG fix) := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hint : Integrable ((freeBox LG fix).indicator (1 : ({b : GBranch LG.garden.tree //
      fix b = none} → ℝ) → ℝ)) := by
    rw [integrable_indicator_iff hBm]
    exact integrableOn_const (by rw [volume_freeBox]; exact ENNReal.one_ne_top)
  rw [continuous_iff_continuousAt]
  intro T₀
  show ContinuousAt (fun T => ∫ τ, protIntegrand L γ δ LG (fun _ => T) s fix K τ) T₀
  exact continuousAt_of_dominated
    (Eventually.of_forall fun T => (measurable_protIntegrand L γ δ LG (fun _ => T) s fix K).aestronglyMeasurable)
    (Eventually.of_forall fun T => Eventually.of_forall (norm_protIntegrand_le L γ δ LG (fun _ => T) s fix K))
    hint ((ae_ne_eval _ T₀).mono fun τ hτ => continuousAt_protIntegrand_up L γ δ LG s fix K T₀ τ hτ)

/-- **Continuity in the upper clock.** -/
theorem continuous_kernelProt_up (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (C : ℝ) (hm : ∀ K, ‖m K‖ ≤ C) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (k₀ : Mom d)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree => ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, Summable fun n : Fin d → ℤ => |H ℓ.1 (k₀ + latticePoint L n)|) :
    Continuous (fun T => kernelProt L γ δ LG H m (fun _ => T) s fix k₀ (fun _ => 0) 0) := by
  have he : (fun T => kernelProt L γ δ LG H m (fun _ => T) s fix k₀ (fun _ => 0) 0) =
      fun T => (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
        ∑' κ : GenDecoration LG.garden d (fun _ => 0) 0, protSummand L γ δ LG H m (fun _ => T) s fix k₀ κ := by
    funext T
    exact kernelProt_eq_tsum L γ δ LG H m _ s fix k₀ _ _
  rw [he]
  refine continuous_const.mul (continuous_tsum (fun κ => ?_)
    ((summable_leafMajorant L LG H k₀ (fun _ => 0) 0 hlone hH).mul_left C)
    (fun κ T => norm_protSummand_le L γ δ LG H m C hm (fun _ => T) s fix k₀ κ))
  unfold protSummand
  exact continuous_const.mul ((continuous_const.mul
    (continuous_protTime_up L γ δ LG s fix _)).mul continuous_const)

/-- **The lone-port time is void when every lone parent is pinned.** -/
theorem kernelProt_port (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (up : GBranch LG.garden.tree → ℝ) (s s' : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hpin : ∀ b, LG.garden.IsLoneParent b → fix b ≠ none) :
    kernelProt L γ δ LG H m up s fix k₀ nroot nfl = kernelProt L γ δ LG H m up s' fix k₀ nroot nfl := by
  have hs : ∀ s1 : ℝ, kDomainFix LG up fix ∩ {τ | ∀ b, LG.garden.IsLoneParent b → fix b = none → s1 < τ b} =
      kDomainFix LG up fix := by
    intro s1
    ext τ
    exact ⟨fun h => h.1, fun h => ⟨h, fun b hb hf => absurd hf (hpin b hb)⟩⟩
  unfold kernelProt
  rw [hs s, hs s']

end WaveTurbulence.Flower.ProtWhole
