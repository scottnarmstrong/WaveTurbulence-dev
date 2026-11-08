/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TermCore
public import WaveTurbulence.Foundations.Flower.ProtCut.CutTerm

/-! # D3 PROT-PIN (P7): generic tools for the root trace of a side couple

* `tc_kink0`: `kink_restr` with the kink point allowed at the bottom of the window (`p ≤ s`): the partner integral
  `u ↦ ∫_{p<u'<u} e^{πiA(u'-p)} h(u, u') du'` of a root trace whose partner root is in layer `p`.
* `tc_cont_clock`: `kernelProt` is continuous in one clock (the branches with `P b` at clock `u`, the others at fixed
  clocks), with pins independent of `u` (the pattern of ProtWhole/Cont.lean, for several clocks). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier Filter Topology
open scoped ENNReal NNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut

/-- **The zero-extended terminal operator with the kink point allowed at the bottom of the window.** -/
theorem tc_kink0 {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type) [Countable ι] (p s : ℝ), p ≤ s → s < p + 1 →
      ∀ (A : ι → ℝ) (c : ι → ℂ) (h : ι → (Fin 2 → ℝ) → ℂ), (∀ i, Continuous (h i)) →
      (∀ i, rn θ (triS p s) (h i) < ⊤) →
      rn θ (win p) (fun T => ∑' i, c i * ∫ u in Ioo s (T 0), cutMod (A i) s u * h i ![T 0, u]) ≤
        ENNReal.ofReal C * ∑' i, ‖c i‖ₑ * rn θ (triS p s) (h i) := by
  obtain ⟨C₀, hC₀, hK⟩ := termKink_sum hθ0 hθ1
  refine ⟨C₀ + 1, by linarith, fun ι _ p s hps hsp A c h hc hfin => ?_⟩
  set S := ∑' i, ‖c i‖ₑ * rn θ (triS p s) (h i) with hS
  have hC1 : ENNReal.ofReal (C₀ + 1) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; linarith
  by_cases hStop : S = ⊤
  · rw [hStop, ENNReal.mul_top hC1]
    exact le_top
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  set ε' : ℝ≥0∞ := (ε : ℝ≥0∞) / ENNReal.ofReal (C₀ + 1) with hε'
  have hε'0 : ε' ≠ 0 := by
    rw [hε']
    exact ENNReal.div_pos_iff.2 ⟨by exact_mod_cast hε.ne', ENNReal.ofReal_ne_top⟩ |>.ne'
  obtain ⟨w, hwpos, hwsum⟩ := ENNReal.exists_pos_sum_of_countable hε'0 ι
  set δ : ι → ℝ≥0∞ := fun i => (w i : ℝ≥0∞) / (‖c i‖ₑ + 1) with hδ
  have hδpos : ∀ i, 0 < δ i := fun i =>
    ENNReal.div_pos_iff.2 ⟨by exact_mod_cast (hwpos i).ne', by simp⟩
  have hδtop : ∀ i, δ i ≠ ⊤ := fun i =>
    ENNReal.div_ne_top (by simp) (by simp)
  have hext := fun i => exists_cont_ext hθ0 (triS_closure p s) (hc i) (hfin i) (hδpos i) (hδtop i)
  choose g hgc hgag hgfin hgle using hext
  have hcδ : ∀ i, ‖c i‖ₑ * δ i ≤ (w i : ℝ≥0∞) := fun i => by
    rw [hδ]
    calc ‖c i‖ₑ * ((w i : ℝ≥0∞) / (‖c i‖ₑ + 1)) ≤ (‖c i‖ₑ + 1) * ((w i : ℝ≥0∞) / (‖c i‖ₑ + 1)) :=
          mul_le_mul' le_self_add le_rfl
      _ = (w i : ℝ≥0∞) := ENNReal.mul_div_cancel (by simp) (by simp)
  have hsumg : ∑' i, ‖c i‖ₑ * timeFourierNorm θ (g i) ≤ S + ε' := by
    calc ∑' i, ‖c i‖ₑ * timeFourierNorm θ (g i) ≤ ∑' i, (‖c i‖ₑ * rn θ (triS p s) (h i) + (w i : ℝ≥0∞)) :=
          ENNReal.tsum_le_tsum fun i => by
            calc ‖c i‖ₑ * timeFourierNorm θ (g i) ≤ ‖c i‖ₑ * (rn θ (triS p s) (h i) + δ i) :=
                  mul_le_mul' le_rfl (hgle i)
              _ = ‖c i‖ₑ * rn θ (triS p s) (h i) + ‖c i‖ₑ * δ i := by rw [mul_add]
              _ ≤ _ := add_le_add le_rfl (hcδ i)
      _ = S + ∑' i, (w i : ℝ≥0∞) := ENNReal.tsum_add
      _ ≤ S + ε' := add_le_add le_rfl hwsum.le
  have hfin' : ∑' i, ‖c i‖ₑ * timeFourierNorm θ (g i) < ⊤ :=
    hsumg.trans_lt (ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hStop,
      lt_top_iff_ne_top.2 (ENNReal.div_ne_top ENNReal.coe_ne_top hC1)⟩)
  obtain ⟨G, hGeq, hGnorm⟩ := hK ι s A c g hgc hgfin hfin'
  refine (rn_le θ (g := G) fun T hT => ?_).trans ?_
  · have hT1 : |T 0 - s| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [hT.1, hT.2]
    rw [hGeq T hT1]
    refine tsum_congr fun i => ?_
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    have hmem : (![T 0, u] : Fin 2 → ℝ) ∈ triS p s := by
      refine ⟨⟨hT, ?_, ?_⟩, hu.1, hu.2⟩
      · show p ≤ u; linarith [hu.1]
      · show u ≤ p + 1; linarith [hu.2, hT.2]
    rw [hgag i _ hmem]
    rfl
  · calc timeFourierNorm θ G ≤ ENNReal.ofReal C₀ * ∑' i, ‖c i‖ₑ * timeFourierNorm θ (g i) := hGnorm
      _ ≤ ENNReal.ofReal (C₀ + 1) * (S + ε') :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) hsumg
      _ = ENNReal.ofReal (C₀ + 1) * S + ε := by
          rw [mul_add, hε', ENNReal.mul_div_cancel hC1 ENNReal.ofReal_ne_top]

/-! ### Continuity in one clock -/

section Cont

variable {w d : ℕ}

theorem tc_mem_protDom_iff (LG : LayeredGarden w) (P : GBranch LG.garden.tree → Prop) [DecidablePred P]
    (cl : GBranch LG.garden.tree → ℝ) (s : ℝ) (fix : GBranch LG.garden.tree → Option ℝ)
    (x : GBranch LG.garden.tree → ℝ) (u u₀ : ℝ) (h : ∀ b, fix b = none → P b → (x b < u ↔ x b < u₀)) :
    x ∈ protDom LG (fun b => if P b then u else cl b) s fix ↔
      x ∈ protDom LG (fun b => if P b then u₀ else cl b) s fix := by
  have key : ∀ b, fix b = none → (x b < (if P b then u else cl b) ↔ x b < (if P b then u₀ else cl b)) := by
    intro b hb
    by_cases hP : P b
    · rw [if_pos hP, if_pos hP]; exact h b hb hP
    · rw [if_neg hP, if_neg hP]
  unfold protDom kDomainFix
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun b => ⟨fun hf => ?_, (h1 b).2⟩, h2⟩
    obtain ⟨a1, a2, a3, a4⟩ := (h1 b).1 hf
    exact ⟨a1, a2, a3, (key b hf).1 a4⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun b => ⟨fun hf => ?_, (h1 b).2⟩, h2⟩
    obtain ⟨a1, a2, a3, a4⟩ := (h1 b).1 hf
    exact ⟨a1, a2, a3, (key b hf).2 a4⟩

theorem tc_continuousAt_protIntegrand (L γ δ : ℝ) (LG : LayeredGarden w) (P : GBranch LG.garden.tree → Prop)
    [DecidablePred P] (cl : GBranch LG.garden.tree → ℝ) (s : ℝ) (fix : GBranch LG.garden.tree → Option ℝ)
    (K : GNode LG.garden.tree → Mom d) (u₀ : ℝ) (τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ)
    (hτ : ∀ b, τ b ≠ u₀) :
    ContinuousAt (fun u => protIntegrand L γ δ LG (fun b => if P b then u else cl b) s fix K τ) u₀ := by
  have hev : ∀ᶠ u in 𝓝 u₀, ∀ b : {b : GBranch LG.garden.tree // fix b = none}, (τ b < u ↔ τ b < u₀) := by
    rw [Filter.eventually_all]
    intro b
    rcases lt_or_gt_of_ne (hτ b) with hb | hb
    · filter_upwards [Ioi_mem_nhds hb] with T hT
      exact iff_of_true hT hb
    · filter_upwards [Iio_mem_nhds hb] with T hT
      exact iff_of_false (not_lt.2 (le_of_lt hT)) (not_lt.2 hb.le)
  refine (continuousAt_const (y := protIntegrand L γ δ LG (fun b => if P b then u₀ else cl b) s fix K τ)).congr ?_
  filter_upwards [hev] with u hu
  unfold protIntegrand
  have hmem := tc_mem_protDom_iff LG P cl s fix (LG.garden.extendFix fix τ) u u₀ (fun b hf _ => by
    rw [extendFix_free LG.garden fix τ ⟨b, hf⟩]
    exact hu ⟨b, hf⟩)
  by_cases hm : LG.garden.extendFix fix τ ∈ protDom LG (fun b => if P b then u₀ else cl b) s fix
  · rw [indicator_of_mem hm, indicator_of_mem (hmem.2 hm)]
  · rw [indicator_of_notMem hm, indicator_of_notMem (fun h => hm (hmem.1 h))]

theorem tc_ae_ne_eval (ι : Type*) [Fintype ι] (T₀ : ℝ) :
    ∀ᵐ τ ∂(volume : Measure (ι → ℝ)), ∀ b, τ b ≠ T₀ := by
  rw [ae_all_iff]
  intro b
  rw [ae_iff]
  simp only [ne_eq, not_not]
  exact Measure.pi_eval_preimage_null (μ := fun _ : ι => (volume : Measure ℝ)) (i := b) (s := ({T₀} : Set ℝ))
    Real.volume_singleton

theorem tc_continuous_protTime (L γ δ : ℝ) (LG : LayeredGarden w) (P : GBranch LG.garden.tree → Prop)
    [DecidablePred P] (cl : GBranch LG.garden.tree → ℝ) (s : ℝ) (fix : GBranch LG.garden.tree → Option ℝ)
    (K : GNode LG.garden.tree → Mom d) :
    Continuous (fun u => protTime L γ δ LG (fun b => if P b then u else cl b) s fix K) := by
  have hBm : MeasurableSet (freeBox LG fix) := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hint : Integrable ((freeBox LG fix).indicator (1 : ({b : GBranch LG.garden.tree //
      fix b = none} → ℝ) → ℝ)) := by
    rw [integrable_indicator_iff hBm]
    exact integrableOn_const (by rw [volume_freeBox]; exact ENNReal.one_ne_top)
  rw [continuous_iff_continuousAt]
  intro u₀
  show ContinuousAt (fun u => ∫ τ, protIntegrand L γ δ LG (fun b => if P b then u else cl b) s fix K τ) u₀
  exact continuousAt_of_dominated
    (Eventually.of_forall fun u => (measurable_protIntegrand L γ δ LG _ s fix K).aestronglyMeasurable)
    (Eventually.of_forall fun u => Eventually.of_forall (norm_protIntegrand_le L γ δ LG _ s fix K))
    hint ((tc_ae_ne_eval _ u₀).mono fun τ hτ => tc_continuousAt_protIntegrand L γ δ LG P cl s fix K u₀ τ hτ)

/-- **Continuity of `kernelProt` in one clock.** -/
theorem tc_cont_clock (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (C : ℝ) (hm : ∀ K, ‖m K‖ ≤ C)
    (P : GBranch LG.garden.tree → Prop) [DecidablePred P] (cl : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (k₀ : Mom d)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree => ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, Summable fun n : Fin d → ℤ => |H ℓ.1 (k₀ + latticePoint L n)|) :
    Continuous (fun u => kernelProt L γ δ LG H m (fun b => if P b then u else cl b) s fix k₀ (fun _ => 0) 0) := by
  have he : (fun u => kernelProt L γ δ LG H m (fun b => if P b then u else cl b) s fix k₀ (fun _ => 0) 0) =
      fun u => (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
        ∑' κ : GenDecoration LG.garden d (fun _ => 0) 0,
          protSummand L γ δ LG H m (fun b => if P b then u else cl b) s fix k₀ κ := by
    funext u
    exact kernelProt_eq_tsum L γ δ LG H m _ s fix k₀ _ _
  rw [he]
  refine continuous_const.mul (continuous_tsum (fun κ => ?_)
    ((PL234.summable_leafMajorant L LG H k₀ (fun _ => 0) 0 hlone hH).mul_left C)
    (fun κ u => norm_protSummand_le L γ δ LG H m C hm _ s fix k₀ κ))
  unfold protSummand
  exact continuous_const.mul ((continuous_const.mul
    (tc_continuous_protTime L γ δ LG P cl s fix _)).mul continuous_const)

end Cont

end WaveTurbulence.Flower.ProtPin
