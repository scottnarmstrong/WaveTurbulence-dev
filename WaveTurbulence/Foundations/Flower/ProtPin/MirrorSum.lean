/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.MirrorTensor
public import WaveTurbulence.Foundations.Flower.ProtPin.KinkOp

/-! # D3-MIRROR: countable sums under a common cutoff, the triangles of the root trace, a slack limit

* `tsum_cut_le`: for continuous `g_i` with `Σ |c_i| ‖g_i‖_{A^θ} < ∞` and a continuous compactly supported cutoff `χ`,
  `x ↦ Σ_i c_i χ(x) g_i(x)` is continuous with `A^θ` norm `≤ 2^θ ‖χ‖ Σ_i |c_i| ‖g_i‖` (the cutoff gives the summable
  `L¹` masses that the counting-integral Minkowski bound `timeFourierNorm_count_le` needs; `|g_i| ≤ ‖g_i‖_{A^θ}`).
* `triO p = {p < s < t < p+1}`, `triC p = {p ≤ s ≤ t ≤ p+1}` (`ts = (t, s)`), `triC p ⊆ closure (triO p)`.
* `cut2 p`: the unit cutoff of `[p, p+1]²`.
* `le_of_slack`: `X ≤ K₁ (K₀ (a+δ)(S+δ) + δ)` for all `δ > 0` gives `X ≤ K₁ K₀ a S` (finite constants). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence Set Finset MeasureTheory WaveTurbulence.Fourier Filter Topology
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtPin

/-- **A countable family under a common compactly supported cutoff.** -/
theorem tsum_cut_le {r : ℕ} {θ : ℝ} (hθ : 0 ≤ θ) {χ : (Fin r → ℝ) → ℂ} (hχc : Continuous χ)
    (hχs : HasCompactSupport χ) (hχn : timeFourierNorm θ χ < ⊤) {ι : Type} [Countable ι] (c : ι → ℂ)
    (g : ι → (Fin r → ℝ) → ℂ) (hgc : ∀ i, Continuous (g i)) (hgn : ∀ i, timeFourierNorm θ (g i) < ⊤)
    (hsum : (∑' i, ‖c i‖ₑ * timeFourierNorm θ (g i)) < ⊤) :
    Continuous (fun x => ∑' i, c i * (χ x * g i x)) ∧
      timeFourierNorm θ (fun x => ∑' i, c i * (χ x * g i x)) ≤
        ENNReal.ofReal (2 ^ θ) * timeFourierNorm θ χ * ∑' i, ‖c i‖ₑ * timeFourierNorm θ (g i) := by
  let _ : MeasurableSpace ι := ⊤
  have : MeasurableSingletonClass ι := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  set F : ι → (Fin r → ℝ) → ℂ := fun i x => c i * (χ x * g i x) with hF
  have hFc : ∀ i, Continuous (F i) := fun i => continuous_const.mul (hχc.mul (hgc i))
  have hpt : ∀ i x, ‖F i x‖ₑ ≤ timeFourierNorm θ χ * (‖c i‖ₑ * timeFourierNorm θ (g i)) := fun i x => by
    simp only [hF, enorm_mul]
    calc ‖c i‖ₑ * (‖χ x‖ₑ * ‖g i x‖ₑ) ≤ ‖c i‖ₑ * (timeFourierNorm θ χ * timeFourierNorm θ (g i)) := by
          gcongr
          · exact Regref.enorm_le_timeFourierNorm_at hθ χ x hχc.continuousAt
          · exact Regref.enorm_le_timeFourierNorm_at hθ (g i) x (hgc i).continuousAt
      _ = _ := by ring
  set u : ι → ℝ≥0∞ := fun i => timeFourierNorm θ χ * (‖c i‖ₑ * timeFourierNorm θ (g i)) with hu
  have husum : (∑' i, u i) ≠ ⊤ := by
    rw [hu, ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top hχn.ne hsum.ne
  have hus : Summable (fun i => (u i).toReal) := ENNReal.summable_toReal husum
  have hut : ∀ i, u i ≠ ⊤ := fun i => ENNReal.ne_top_of_tsum_ne_top husum i
  have hnorm : ∀ i x, ‖F i x‖ ≤ (u i).toReal := fun i x => by
    rw [← toReal_enorm]
    exact ENNReal.toReal_mono (hut i) (hpt i x)
  have hsx : ∀ x, Summable (fun i => ‖F i x‖) := fun x =>
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hnorm i x) hus
  refine ⟨continuous_tsum hFc hus hnorm, ?_⟩
  have hg' : (fun x => ∑' i, c i * (χ x * g i x)) = fun x => ∫ i, F i x ∂Measure.count := by
    funext x
    exact (Sumint.count_integral_eq_tsum (fun i => F i x) (hsx x)).symm
  rw [hg']
  have hχi : Integrable χ := hχc.integrable_of_hasCompactSupport hχs
  have hFi : ∀ i, Integrable (F i) := fun i =>
    (hFc i).integrable_of_hasCompactSupport (hχs.mul_right.mul_left)
  have hmass : (∑' i, ∫⁻ x, ‖F i x‖ₑ) < ⊤ := by
    calc (∑' i, ∫⁻ x, ‖F i x‖ₑ) ≤ ∑' i, (∫⁻ x, ‖χ x‖ₑ) * (‖c i‖ₑ * timeFourierNorm θ (g i)) := by
          refine ENNReal.tsum_le_tsum fun i => ?_
          rw [← lintegral_mul_const' _ _ (ENNReal.mul_ne_top enorm_ne_top (hgn i).ne)]
          refine lintegral_mono fun x => ?_
          simp only [hF, enorm_mul]
          calc ‖c i‖ₑ * (‖χ x‖ₑ * ‖g i x‖ₑ) ≤ ‖c i‖ₑ * (‖χ x‖ₑ * timeFourierNorm θ (g i)) := by
                gcongr
                exact Regref.enorm_le_timeFourierNorm_at hθ (g i) x (hgc i).continuousAt
            _ = _ := by ring
      _ = (∫⁻ x, ‖χ x‖ₑ) * ∑' i, ‖c i‖ₑ * timeFourierNorm θ (g i) := ENNReal.tsum_mul_left
      _ < ⊤ := ENNReal.mul_lt_top hχi.2 hsum
  refine (timeFourierNorm_count_le θ F (fun i => (hFc i).measurable) hFi hmass).trans ?_
  calc ∑' i, timeFourierNorm θ (F i)
      ≤ ∑' i, ENNReal.ofReal (2 ^ θ) * timeFourierNorm θ χ * (‖c i‖ₑ * timeFourierNorm θ (g i)) := by
        refine ENNReal.tsum_le_tsum fun i => ?_
        have e : F i = fun x => c i • (χ x * g i x) := rfl
        rw [e, timeFourierNorm_smul]
        calc ‖c i‖ₑ * timeFourierNorm θ (fun x => χ x * g i x)
            ≤ ‖c i‖ₑ * (ENNReal.ofReal (2 ^ θ) * timeFourierNorm θ χ * timeFourierNorm θ (g i)) := by
              gcongr
              exact timeFourierNorm_mul_le hθ (hgc i) hχn (hgn i)
          _ = _ := by ring
    _ = _ := ENNReal.tsum_mul_left

/-! ### The triangles -/

/-- The open triangle `p < s < t < p + 1` (`ts = (t, s)`). -/
def triO (p : ℝ) : Set (Fin 2 → ℝ) := {ts | p < ts 1 ∧ ts 1 < ts 0 ∧ ts 0 < p + 1}

/-- The closed triangle `p ≤ s ≤ t ≤ p + 1`. -/
def triC (p : ℝ) : Set (Fin 2 → ℝ) := {ts | p ≤ ts 1 ∧ ts 1 ≤ ts 0 ∧ ts 0 ≤ p + 1}

theorem isOpen_triO (p : ℝ) : IsOpen (triO p) :=
  (isOpen_lt continuous_const (continuous_apply 1)).inter
    ((isOpen_lt (continuous_apply 1) (continuous_apply 0)).inter (isOpen_lt (continuous_apply 0) continuous_const))

theorem triO_cl (p : ℝ) : ∀ x ∈ triO p, x ∈ closure (interior (triO p)) := fun x hx => by
  rw [(isOpen_triO p).interior_eq]
  exact subset_closure hx

theorem triC_subset_closure (p : ℝ) : triC p ⊆ closure (triO p) := by
  intro x hx
  set y : Fin 2 → ℝ := ![p + 2 / 3, p + 1 / 3] with hy
  have hlim : Tendsto (fun n : ℕ => x + (1 / ((n : ℝ) + 1)) • (y - x)) atTop (𝓝 x) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const (y - x)
    simpa using tendsto_const_nhds.add this
  refine mem_closure_of_tendsto hlim (Eventually.of_forall fun n => ?_)
  obtain ⟨h1, h2, h3⟩ := hx
  have hl0 : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have hl1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  set l := 1 / ((n : ℝ) + 1)
  simp only [triO, mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hy,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [mul_nonneg (sub_nonneg.2 hl1) (sub_nonneg.2 h1)]
  · nlinarith [mul_nonneg (sub_nonneg.2 hl1) (sub_nonneg.2 h2)]
  · nlinarith [mul_nonneg (sub_nonneg.2 hl1) (sub_nonneg.2 h3)]

theorem timeBoxGt_subset_triC (p : ℝ) : timeBoxGt p p ⊆ triC p := fun _ hx =>
  ⟨hx.1.2.1, hx.2.le, hx.1.1.2⟩

/-! ### The cutoff of the square -/

/-- The unit cutoff of `[p, p+1]²`. -/
def cut2 (p : ℝ) (x : Fin 2 → ℝ) : ℂ := coordinateCutoff (r := 2) Layered.chiUnit (fun i => x i - p)

theorem cut2_eq_translate (p : ℝ) :
    cut2 p = fun x => coordinateCutoff (r := 2) Layered.chiUnit (x + fun _ => -p) := by
  funext x
  unfold cut2
  congr 1

theorem continuous_cut2 (p : ℝ) : Continuous (cut2 p) := by
  unfold cut2
  exact (coordinateCutoff_contDiff Layered.chiUnit_contDiff).continuous.comp (by fun_prop)

theorem hasCompactSupport_cut2 (p : ℝ) : HasCompactSupport (cut2 p) := by
  rw [cut2_eq_translate]
  exact (coordinateCutoff_hasCompactSupport Layered.chiUnit_hasCompactSupport).comp_homeomorph
    (Homeomorph.addRight fun _ => -p)

/-- Its norm (independent of `p`). -/
def cut2Norm (θ : ℝ) : ℝ≥0∞ := timeFourierNorm θ (coordinateCutoff (r := 2) Layered.chiUnit)

theorem cut2_norm (θ p : ℝ) : timeFourierNorm θ (cut2 p) = cut2Norm θ := by
  rw [cut2_eq_translate, timeFourierNorm_translate]
  rfl

theorem cut2Norm_lt_top (θ : ℝ) : cut2Norm θ < ⊤ :=
  timeFourierNorm_lt_top_of_smooth_compact θ
    (coordinateCutoff_hasCompactSupport Layered.chiUnit_hasCompactSupport)
    (coordinateCutoff_contDiff Layered.chiUnit_contDiff)

theorem cut2_norm_lt_top (θ p : ℝ) : timeFourierNorm θ (cut2 p) < ⊤ := by
  rw [cut2_eq_translate, timeFourierNorm_translate]
  exact timeFourierNorm_lt_top_of_smooth_compact θ
    (coordinateCutoff_hasCompactSupport Layered.chiUnit_hasCompactSupport)
    (coordinateCutoff_contDiff Layered.chiUnit_contDiff)

theorem cut2_eq_one {p : ℝ} {x : Fin 2 → ℝ} (hx : x ∈ triC p) : cut2 p x = 1 := by
  unfold cut2
  refine Layered.coordinateCutoff_chiUnit_eq_one fun i => ?_
  obtain ⟨h1, h2, h3⟩ := hx
  fin_cases i
  · exact ⟨by simp; linarith, by simp; linarith⟩
  · exact ⟨by simp; linarith, by simp; linarith⟩

/-! ### The slack limit -/

theorem le_of_slack {X K₀ K₁ a S : ℝ≥0∞} (hK₀ : K₀ ≠ ⊤) (hK₁ : K₁ ≠ ⊤) (ha : a ≠ ⊤) (hS : S ≠ ⊤)
    (h : ∀ δ : ℝ≥0∞, 0 < δ → δ ≠ ⊤ → X ≤ K₁ * (K₀ * (a + δ) * (S + δ) + δ)) : X ≤ K₁ * K₀ * a * S := by
  have ha' : Tendsto (fun δ : ℝ≥0∞ => a + δ) (𝓝 0) (𝓝 (a + 0)) := tendsto_const_nhds.add tendsto_id
  have hS' : Tendsto (fun δ : ℝ≥0∞ => S + δ) (𝓝 0) (𝓝 (S + 0)) := tendsto_const_nhds.add tendsto_id
  have h1 : Tendsto (fun δ : ℝ≥0∞ => K₀ * (a + δ)) (𝓝 0) (𝓝 (K₀ * (a + 0))) :=
    ENNReal.Tendsto.const_mul ha' (Or.inr hK₀)
  have h2 : Tendsto (fun δ : ℝ≥0∞ => K₀ * (a + δ) * (S + δ)) (𝓝 0) (𝓝 (K₀ * (a + 0) * (S + 0))) :=
    ENNReal.Tendsto.mul h1 (Or.inr (by simpa using hS)) hS'
      (Or.inr (by simpa using ENNReal.mul_ne_top hK₀ ha))
  have h3 : Tendsto (fun δ : ℝ≥0∞ => K₀ * (a + δ) * (S + δ) + δ) (𝓝 0)
      (𝓝 (K₀ * (a + 0) * (S + 0) + 0)) := h2.add tendsto_id
  have h4 : Tendsto (fun δ : ℝ≥0∞ => K₁ * (K₀ * (a + δ) * (S + δ) + δ)) (𝓝 0)
      (𝓝 (K₁ * (K₀ * (a + 0) * (S + 0) + 0))) := ENNReal.Tendsto.const_mul h3 (Or.inr hK₁)
  have ht := h4.comp ENNReal.tendsto_inv_nat_nhds_zero
  have hX := ge_of_tendsto ht (eventually_atTop.2 ⟨1, fun n hn => h _
    (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top n))
    (ENNReal.inv_ne_top.2 (by exact_mod_cast (show n ≠ 0 by omega)))⟩)
  simpa [mul_assoc] using hX

end WaveTurbulence.Flower.ProtPin
